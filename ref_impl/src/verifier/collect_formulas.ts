//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import chalk from "chalk";
import { MIREmitter } from "../compiler/mir_emitter";
import { PackageConfig, MIRAssembly, MIRFunctionDecl } from "../compiler/mir_assembly";
import { MIRBody, MIRBasicBlock, MIROpTag, MIRBinCmp, MIRArgument, MIROp, MIRConstantArgument, MIRRegisterArgument, MIRVarLifetimeStart } from "../compiler/mir_ops";
import { } from "../compiler/mir_ssa"; // We might need somethings from there, eventually!
import { topologicalOrder, computeBlockLinks } from "../compiler/ir_info";
import { TypeExpr, IntType, BoolType, StringType, UninterpretedType } from "../verifier/type_expr";
import { VarExpr } from "../verifier/term_expr";
import { PredicateExpr, FormulaExpr, AndExpr, EqualityExpr } from "../verifier/formula_expr";

// TODO: Probably we dont need to instantiate
// new elements from TypeExpr() ..

// Global variable to gather the types seen 
// in the program
// Keep in mind that blocks will be 
// process in a topological order
// Hence, it cannot be the case that
// we introduce inconsistency in the types
// of a well-typed program
let typesSeen: Map<string, string> = new Map<string, string>();

// I agree, this looks extremely dirty
function resolveType(typeName: string): TypeExpr {
    switch (typeName) {
        case "NSCore::Int": {
            return new IntType();
        }
        case "NSCore::Bool": {
            return new BoolType();
        }
        case "NSCore::String": {
            return new StringType();
        }
        case "true" : {
            return new BoolType();
        }
        case "false" : {
            return new BoolType();
        }
        default: {
            if(typeName.length > 3){
                switch(typeName.substr(0, 4)) {
                    case "=int" : {
                        return new IntType();
                    }
                    case "=str" : {
                        return new StringType();
                    }
                    default : {
                        return new UninterpretedType(typeName);
                    }
                }
            }   
            else{
                return new UninterpretedType(typeName);
            }
        }
    }
}

function getControlFlow(app: string, section: string, fd: number): void {

    let bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));

    let files: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(bosque_dir, "src/core/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();

        const collectionsdir = Path.join(bosque_dir, "src/core/collections.bsq");
        const collectionsdata = FS.readFileSync(collectionsdir).toString();

        const appdir = app;
        const appdata = FS.readFileSync(appdir).toString();

        files = [{ relativePath: coredir, contents: coredata }, { relativePath: collectionsdir, contents: collectionsdata }, { relativePath: appdir, contents: appdata }];
    }
    catch (ex) {
        process.stdout.write(chalk.red(`Read failed with exception -- ${ex}\n`));
        process.exit(1);
    }

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), files);

    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk.red(`Parse error -- ${errors[i]}\n`));
        }
        process.exit(1);
    }

    try {
        const sectionName = section.split(":").join("_");
        const invokeDecl = ((masm as MIRAssembly).functionDecls.get(section) as MIRFunctionDecl).invoke;
        const ibody = (invokeDecl.body as MIRBody).body;
        // If this is a FunctionDecl then the array of parameters,
        // if it is not empty, will add more elements to the
        // variable typesSeen
        invokeDecl.params.map(x => typesSeen.set(sectionName + "__" + x.name, x.type.trkey));
        if (typeof (ibody) === "string") {
            process.stdout.write("Success as string!\n");
            process.exit(0);
        }
        else {
            // Here we generate the file.z3, essentially
            // Since for Z3 is invalid a name with ":",
            // we replace it with a "_"
            collectFormulas(ibody, sectionName).toZ3(fd, false);
            process.stdout.write("Success as blocks!\n");
            process.exit(0);
        }
    }
    catch (ex) {
        process.stdout.write(chalk.red(`fail with exception -- ${ex}\n`));
        process.exit(1);
    }
}

function argumentToVarExpr(arg : MIRArgument, section : string) : VarExpr {
    // Observation elements of type MIRConstantArgument
    // start with "="
    if(arg.nameID[0] === "="){
        let argConstant = arg as MIRConstantArgument;
        let argName = argConstant.stringify();
        let result = new VarExpr(argName, resolveType(argConstant.nameID));
        // With this we prevent printing constant argument
        // as declarations in Z3
        VarExpr.symbolTable.set(argName, true);
        return result;
    }
    else{
        let argRegister = arg as MIRRegisterArgument;
        let argName = section + "__" + argRegister.nameID;
        return new VarExpr(argName, resolveType(typesSeen.get(argName) as string));
    }
}

function opToFormula(op: MIROp, section : string): FormulaExpr {
    switch (op.tag) {
        case MIROpTag.LoadConst:
        case MIROpTag.LoadConstTypedString:
        case MIROpTag.AccessNamespaceConstant:
        case MIROpTag.AccessConstField:
        case MIROpTag.LoadFieldDefaultValue: {
            return new PredicateExpr("notdone1", []);
        }
        case MIROpTag.AccessCapturedVariable: {
            return new PredicateExpr("notdone2", []);
        }
        case MIROpTag.AccessArgVariable: {
            return new PredicateExpr("notdone3", []);
        }
        case MIROpTag.AccessLocalVariable: {
            return new PredicateExpr("notdone4", []);
        }
        case MIROpTag.ConstructorPrimary: {
            return new PredicateExpr("notdone5", []);
        }
        case MIROpTag.ConstructorPrimaryCollectionEmpty: {
            return new PredicateExpr("notdone6", []);
        }
        case MIROpTag.ConstructorPrimaryCollectionSingletons: {
            return new PredicateExpr("notdone7", []);
        }
        case MIROpTag.ConstructorPrimaryCollectionCopies: {
            return new PredicateExpr("notdone8", []);
        }
        case MIROpTag.ConstructorPrimaryCollectionMixed: {
            return new PredicateExpr("notdone9", []);
        }
        case MIROpTag.ConstructorTuple: {
            return new PredicateExpr("notdone10", []);
        }
        case MIROpTag.ConstructorRecord: {
            return new PredicateExpr("notdone11", []);
        }
        case MIROpTag.ConstructorLambda: {
            return new PredicateExpr("notdone12", []);
        }
        case MIROpTag.CallNamespaceFunction: {
            return new PredicateExpr("notdone13", []);
        }
        case MIROpTag.CallStaticFunction: {
            return new PredicateExpr("notdone14", []);
        }
        case MIROpTag.MIRAccessFromIndex: {
            return new PredicateExpr("notdone15", []);
        }
        case MIROpTag.MIRProjectFromIndecies: {
            return new PredicateExpr("notdone16", []);
        }
        case MIROpTag.MIRAccessFromProperty: {
            return new PredicateExpr("notdone17", []);
        }
        case MIROpTag.MIRProjectFromProperties: {
            return new PredicateExpr("notdone18", []);
        }
        case MIROpTag.MIRAccessFromField: {
            return new PredicateExpr("notdone19", []);
        }
        case MIROpTag.MIRProjectFromFields: {
            return new PredicateExpr("notdone20", []);
        }
        case MIROpTag.MIRProjectFromTypeTuple: {
            return new PredicateExpr("notdone21", []);
        }
        case MIROpTag.MIRProjectFromTypeRecord: {
            return new PredicateExpr("notdone22", []);
        }
        case MIROpTag.MIRProjectFromTypeConcept: {
            return new PredicateExpr("notdone23", []);
        }
        case MIROpTag.MIRModifyWithIndecies: {
            return new PredicateExpr("notdone24", []);
        }
        case MIROpTag.MIRModifyWithProperties: {
            return new PredicateExpr("notdone25", []);
        }
        case MIROpTag.MIRModifyWithFields: {
            return new PredicateExpr("notdone26", []);
        }
        case MIROpTag.MIRStructuredExtendTuple: {
            return new PredicateExpr("notdone27", []);
        }
        case MIROpTag.MIRStructuredExtendRecord: {
            return new PredicateExpr("notdone28", []);
        }
        case MIROpTag.MIRStructuredExtendObject: {
            return new PredicateExpr("notdone29", []);
        }
        case MIROpTag.MIRInvokeKnownTarget: {
            return new PredicateExpr("notdone30", []);
        }
        case MIROpTag.MIRInvokeVirtualTarget: {
            return new PredicateExpr("notdone31", []);
        }
        case MIROpTag.MIRCallLambda: {
            return new PredicateExpr("notdone32", []);
        }
        case MIROpTag.MIRPrefixOp: {
            return new PredicateExpr("notdone33", []);
        }
        case MIROpTag.MIRBinOp: {
            return new PredicateExpr("notdone34", []);
        }
        case MIROpTag.MIRBinEq: {
            return new PredicateExpr("notdone35", []);
        }
        case MIROpTag.MIRBinCmp: {

            let opBinCmp = op as MIRBinCmp;
            let opFormula = new PredicateExpr(opBinCmp.op, [
                argumentToVarExpr(opBinCmp.lhs, section), 
                argumentToVarExpr(opBinCmp.rhs, section)
            ]);

            let regName = opBinCmp.trgt.nameID[0] == "#" ? "__" + opBinCmp.trgt.nameID.slice(1) : opBinCmp.trgt.nameID;
            let regFormula = new EqualityExpr(new VarExpr(regName, new BoolType()), opFormula);
            return new AndExpr(opFormula, regFormula);
        }
        case MIROpTag.MIRRegAssign: {
            return new PredicateExpr("notdone37", []);
        }
        case MIROpTag.MIRTruthyConvert: {
            return new PredicateExpr("notdone38", []);
        }
        case MIROpTag.MIRVarStore: {
            return new PredicateExpr("notdone39", []);
        }
        case MIROpTag.MIRReturnAssign: {
            return new PredicateExpr("notdone40", []);
        }
        case MIROpTag.MIRAssert: {
            return new PredicateExpr("notdone41", []);
        }
        case MIROpTag.MIRCheck: {
            return new PredicateExpr("notdone42", []);
        }
        case MIROpTag.MIRDebug: {
            return new PredicateExpr("notdone43", []);
        }
        case MIROpTag.MIRJump: {
            return new PredicateExpr("notdone44", []);
        }
        case MIROpTag.MIRJumpCond: {
            return new PredicateExpr("notdone45", []);
        }
        case MIROpTag.MIRJumpNone: {
            return new PredicateExpr("notdone46", []);
        }
        case MIROpTag.MIRVarLifetimeStart: {
            let opVarLifetimeStart = op as MIRVarLifetimeStart;
            typesSeen.set(section + "__" + opVarLifetimeStart.name, opVarLifetimeStart.rtype);
            // TODO: Here is where we include the type relation 
            // of variables
            return new PredicateExpr("almostdone47", []);
        }
        case MIROpTag.MIRVarLifetimeEnd: {
            return new PredicateExpr("notdone48", []);
        }
        default:
            return new PredicateExpr("thismightbeaproblem", []);
    }
}

// params is a sorted array of MIRFunctionParameter
// i.e. the first element corresponds to the first argument, ... and so on.
// Resolve names by prefixing section to every name encountered
function collectFormulas(ibody: Map<string, MIRBasicBlock>, section: string): FormulaExpr {
    const blocks = topologicalOrder(ibody);
    const flow = computeBlockLinks(ibody);

    console.log("Blocks:-----------------------------------------------------------------------");
    console.log(blocks);
    console.log("More detailed Blocks:---------------------------------------------------------");
    blocks.map(x => console.log(x));
    console.log("More detailed++ Blocks:-------------------------------------------------------");
    blocks.map(x => console.log(x.jsonify()));
    console.log("Flow:-------------------------------------------------------------------------");
    console.log(flow);

    let formulass = blocks.map(block => block.ops.map(x => opToFormula(x, section)));
    // TODO: This is wrong and the logical formula should 
    // be built by traversing the flow graph in a breadth
    // first search manner
    return (formulass as FormulaExpr[][])
        .map(formulas => formulas
            .reduce((a, b) => new AndExpr(a, b)))
        .reduce((a, b) => new AndExpr(a, b));
}

////
//Entrypoint

// Mac Machine
// let bosqueFile = "/Users/joseabelcastellanosjoo/BosqueLanguage/ref_impl/src/test/apps/max/main.bsq"
// Windows Machine
let bosqueFile = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/max/main4.bsq";

let section = "NSMain::main";
let fd = FS.openSync('file.z3', 'w');
setImmediate(() => {
    getControlFlow(bosqueFile, section, fd);
    FS.closeSync(fd);
});
