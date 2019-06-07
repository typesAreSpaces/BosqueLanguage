//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRBasicBlock, MIROpTag, MIRBinCmp, MIRArgument, MIROp, MIRRegisterArgument, MIRVarLifetimeStart, MIRVarStore, MIRReturnAssign, MIRJump, MIRJumpCond, MIRBinOp, MIRPhi } from "../compiler/mir_ops";
import { topologicalOrder, computeBlockLinks, FlowLink } from "../compiler/mir_info";
import { TypeExpr, IntType, BoolType, StringType, UninterpretedType } from "../verifier/type_expr";
import { VarExpr, FuncExpr } from "../verifier/term_expr";
import { PredicateExpr, FormulaExpr, AndExpr, EqualityExpr, ImplExpr, NegExpr } from "../verifier/formula_expr";

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
let mapFormulas: Map<string, FormulaExpr> = new Map<string, FormulaExpr>();

let DEBUGGING = false;

function debugging(x : any, flag : boolean){
    if(flag){
        console.log(x);
    }
}
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

        default: {
            return new UninterpretedType(typeName);
        }
    }
}
// I agree, this looks extremely dirty
function resolveTypeUsingValue(value: string): string {
    switch (value) {
        case "true": {
            return "NSCore::Bool";
        }
        case "false": {
            return "NSCore::Bool";
        }
        default : {
            if (value.length > 3) {
                switch (value.substr(1, 3)) {
                    case "int": {
                        return "NSCore::Int";
                    }
                    case "str": {
                        return "NSCore::String";
                    }
                    default: {
                        return "unknown";
                    }
                }
            }
            else {
                return "unknown";
            }
        }
    }
}

function argumentToVarExpr(arg: MIRArgument, section: string): VarExpr {
    if (arg instanceof MIRRegisterArgument) {
        let argName = section + "__" + arg.nameID;
        return new VarExpr(argName, resolveType(typesSeen.get(argName) as string));
    }
    else {
        let argName = arg.stringify();
        let result = new VarExpr(argName, resolveType(arg.nameID));
        // With this we prevent printing constant argument
        // as declarations in Z3
        // TODO: Or should we remove it?
        VarExpr.symbolTable.set(argName, true);
        return result;
    }
}

function opToFormula(op: MIROp, section: string): FormulaExpr {
    let formula = new PredicateExpr("ahhh", []);
    switch (op.tag) {
        case MIROpTag.LoadConst:
        case MIROpTag.LoadConstTypedString:
        case MIROpTag.AccessNamespaceConstant:
        case MIROpTag.AccessConstField:
        case MIROpTag.LoadFieldDefaultValue: {
            debugging("LoadFieldDefaultValue Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.AccessCapturedVariable: {
            debugging("AcessCapturedVariable Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.AccessArgVariable: {
            debugging("AccessArgVariable Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.AccessLocalVariable: {
            debugging("AcessLocalVariable Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorPrimary: {
            debugging("ConstructorPrimary Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorPrimaryCollectionEmpty: {
            debugging("ConstructorPrimaryCollectionEmpty Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorPrimaryCollectionSingletons: {
            debugging("ConstructorPrimaryCollectionSingletons Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorPrimaryCollectionCopies: {
            debugging("ConstructorPrimaryCollectionCopies Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorPrimaryCollectionMixed: {
            debugging("ConstructorPrimaryCollectionMixed Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorTuple: {
            debugging("ConstructorTuple Not implemented yet", DEBUGGING);
            return formula
        }
        case MIROpTag.ConstructorRecord: {
            debugging("ConstructorRecord Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.ConstructorLambda: {
            debugging("ConstructorLambda Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.CallNamespaceFunction: {
            debugging("CallNamespaceFunction Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.CallStaticFunction: {
            debugging("CallStaticFunction Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRAccessFromIndex: {
            debugging("MIRAccessFromIndex Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRProjectFromIndecies: {
            debugging("MIRProjectFromIndecies Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRAccessFromProperty: {
            debugging("MIRAcessFromProperty Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRProjectFromProperties: {
            debugging("MIRProjectFromProperties Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRAccessFromField: {
            debugging("MIRAccessFromField Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRProjectFromFields: {
            debugging("MIRProjectFromFields Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRProjectFromTypeTuple: {
            debugging("MIRProjectFromTypeTuple Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRProjectFromTypeRecord: {
            debugging("MIRProjectFromTypeRecord Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRProjectFromTypeConcept: {
            debugging("MIRProjectFromTypeConcept Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRModifyWithIndecies: {
            debugging("MIRModifyWithIndecies Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRModifyWithProperties: {
            debugging("MIRModifyWithProperties Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRModifyWithFields: {
            debugging("MIRModifyWithFields Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRStructuredExtendTuple: {
            debugging("MIRStructuredExtendedTuple Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRStructuredExtendRecord: {
            debugging("MIRStructuredExtendRecord Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRStructuredExtendObject: {
            debugging("MIRStructuredExtendObject Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRInvokeKnownTarget: {
            debugging("MIRInvokeKnownTarget Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRInvokeVirtualTarget: {
            debugging("MIRInvokeVirtualTarget Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRCallLambda: {
            debugging("MIRCallLambda Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRPrefixOp: {
            debugging("MIRPrefixOp Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRBinOp: {
            let opBinOp = op as MIRBinOp;
            let regName = opBinOp.trgt.nameID[0] == "#" ? "__" + opBinOp.trgt.nameID.slice(1) : opBinOp.trgt.nameID;
            // We assume the expressions are well-typed.
            // So we assign the type of the register
            // the type of the lhs element in the operation
            let typeOfrhsTerm = resolveType(typesSeen.get(section + "__" + opBinOp.lhs.nameID) as string);
            let rhsOfAssignmentTerm = new FuncExpr(opBinOp.op, typeOfrhsTerm, [
                argumentToVarExpr(opBinOp.lhs, section),
                argumentToVarExpr(opBinOp.rhs, section)
            ]);
            let opFormula = new EqualityExpr(new VarExpr(regName, typeOfrhsTerm), rhsOfAssignmentTerm);
            return opFormula;
        }
        case MIROpTag.MIRBinEq: {
            debugging("MIRBinEq Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRBinCmp: {
            // The predicate returned is of type Bool
            // because the operations to arrive at this
            // point are <, <=, >, >= only
            let opBinCmp = op as MIRBinCmp;
            let opFormula = new PredicateExpr(opBinCmp.op, [
                argumentToVarExpr(opBinCmp.lhs, section),
                argumentToVarExpr(opBinCmp.rhs, section)
            ]);

            let regName = opBinCmp.trgt.nameID[0] == "#" ? "__" + opBinCmp.trgt.nameID.slice(1) : opBinCmp.trgt.nameID;
            return new EqualityExpr(new PredicateExpr(regName, []), opFormula);
        }
        case MIROpTag.MIRRegAssign: {
            debugging("MIRRegAssign Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRTruthyConvert: {
            debugging("MIRTruthyConvert Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRVarStore: {
            let opVarStore = op as MIRVarStore;
            let regName = section + "__" + opVarStore.name.nameID;
            let srcName = opVarStore.src.nameID;
            if(opVarStore.src instanceof MIRRegisterArgument){
                srcName = section + "__" + srcName;
                typesSeen.set(regName, typesSeen.get(srcName) as string);
            }
            else{
                typesSeen.set(regName, resolveTypeUsingValue(srcName));
            }
            let opFormula = new EqualityExpr(
                argumentToVarExpr(opVarStore.src, section),
                argumentToVarExpr(opVarStore.name, section));
            return opFormula;
        }
        case MIROpTag.MIRReturnAssign: {
            let opReturnAssign = op as MIRReturnAssign;
            let regName = section + "__" + opReturnAssign.name.nameID;
            let srcName = opReturnAssign.src.nameID;
            // The register Variable will have the same
            // type of the src Variable
            if(opReturnAssign.src instanceof MIRRegisterArgument){
                srcName = section + "__" + srcName;
                typesSeen.set(regName, typesSeen.get(srcName) as string);
            }
            else{
                typesSeen.set(regName, resolveTypeUsingValue(srcName));
            }
            let opFormula = new EqualityExpr(
                argumentToVarExpr(opReturnAssign.name, section),
                argumentToVarExpr(opReturnAssign.src, section));
            return opFormula;
        }
        case MIROpTag.MIRAbort: {
            debugging("MIRAbort Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRDebug: {
            debugging("MIRDDebug Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRJump: {
            let opJump = op as MIRJump;
            opJump;
            // console.log("Implementing MIRJump--------------------------------------------------");
            // console.log(opJump);
            return formula;
        }
        case MIROpTag.MIRJumpCond: {
            let opJumpCond = op as MIRJumpCond;
            opJumpCond;
            // console.log("Implementing MIRJumpCond----------------------------------------------");
            // console.log(opJumpCond);
            return formula;
        }
        case MIROpTag.MIRJumpNone: {
            debugging("MIRJumpNone Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRVarLifetimeStart: {
            let opVarLifetimeStart = op as MIRVarLifetimeStart;
            // We don't check if opVarLifetimeStart
            // is an instance of MIRRegisterArgument
            // because it always is a variable
            typesSeen.set(section + "__" + opVarLifetimeStart.name, opVarLifetimeStart.rtype);
            // TODO: Here is where we include the type relation 
            // of variables
            return formula;
        }
        case MIROpTag.MIRVarLifetimeEnd: {
            debugging("MIRVarLifetimeEnd Not implemented yet", DEBUGGING);
            return formula;
        }
        case MIROpTag.MIRPhi: {
            let opPhi = op as MIRPhi;
            console.log("Implementing MIRPhi-----------------------------");
            console.log(opPhi);
            let targetName = section + "__" + opPhi.trgt.nameID;
            // TODO: Fix this using UnionType or a
            // clever approach. Currently is just set to 
            // be the IntType for the purpose of the 
            // max function demo
            typesSeen.set(targetName, "NSCore::Int");
            opPhi.src.forEach((value, key) => {
                value;
            });
            // let targetExpr = argumentToVarExpr(opPhi.trgt, section);
            return formula;
        }
        default:
            debugging("This might be a problem", DEBUGGING);
            return formula;
    }
}

function makeConjunction(formulas: FormulaExpr[]): FormulaExpr {
    let changeFormula = false;
    let result = new PredicateExpr("true", []) as FormulaExpr;
    for (let formula of formulas) {
        if (!changeFormula) {
            changeFormula = true;
            result = formula;
        }
        else {
            result = new AndExpr(result, formula);
        }
    }
    return result;
}

// params is a sorted array of MIRFunctionParameter
// i.e. the first element corresponds to the first argument, ... and so on.
// Resolve names by prefixing section to every name encountered
function collectFormulas(ibody: Map<string, MIRBasicBlock>, section: string): FormulaExpr {
    const blocks = topologicalOrder(ibody);
    const flow = computeBlockLinks(ibody);

    const mapBlocks = new Map<string, MIRBasicBlock>();
    blocks.map(x => mapBlocks.set(x.label, x));

    // console.log("Blocks:-----------------------------------------------------------------------");
    // console.log(blocks);
    // console.log("More detailed Blocks:---------------------------------------------------------");
    // blocks.map(x => console.log(x));
    // console.log("More detailed++ Blocks:-------------------------------------------------------");
    // blocks.map(x => console.log(x.jsonify()));
    // console.log("Flow:-------------------------------------------------------------------------");
    // console.log(flow);

    for (let currentBlock of blocks) {
        let currentBlockName = currentBlock.label;
        //---------------------------------------------------------------------------------------------        
        // Important: according to the weakest precondition 
        // semantics currentBlocks.ops should be in reverse
        // let blockFormula = currentBlock.ops.reduce((a, b) => opToFormula(b, section, a), initialFormula);
        //---------------------------------------------------------------------------------------------
        //---------------------------------------------------------------------------------------------
        // Process the formula for the individual block
        let blockFormula = makeConjunction(currentBlock.ops.map(x => opToFormula(x, section)));

        //--------------------------------------------------------------------------------------------
        //---------------------------------------------------------------------------------------------
        // Extend to above formula with previous conditions
        let extendedBlockFormula = new PredicateExpr("true", []) as FormulaExpr;
        let flowBlock = flow.get(currentBlockName) as FlowLink;
        let changeFormula = false;
        if (flowBlock.preds.size !== 0) {
            let flowBlockPred = Array.from(flowBlock.preds);
            for (let predLabel of flowBlockPred) {
                let predBlock = (mapBlocks.get(predLabel) as MIRBasicBlock);
                let lastIndex = predBlock.ops.length - 1;
                let lastOp = predBlock.ops[lastIndex];
                changeFormula = false;
                if (!changeFormula) {
                    if (lastOp instanceof MIRJumpCond) {
                        changeFormula = true;
                        let regName = lastOp.arg.nameID[0] == "#" ? "__" + lastOp.arg.nameID.slice(1) : lastOp.arg.nameID;
                        if (currentBlockName === lastOp.trueblock) {
                            extendedBlockFormula = new ImplExpr(new PredicateExpr(regName, []), blockFormula);
                        }
                        else {
                            extendedBlockFormula = new ImplExpr(new NegExpr(new PredicateExpr(regName, [])), blockFormula);
                        }
                    }
                    if (lastOp instanceof MIRJump) {
                    }
                }
                else {
                    if (lastOp instanceof MIRJumpCond) {
                        let regName = lastOp.arg.nameID[0] == "#" ? "__" + lastOp.arg.nameID.slice(1) : lastOp.arg.nameID;
                        let regPredicate = new PredicateExpr(regName, []);
                        if (currentBlockName === lastOp.trueblock) {
                            extendedBlockFormula = new AndExpr(extendedBlockFormula, new ImplExpr(regPredicate, blockFormula));
                        }
                        else {
                            extendedBlockFormula = new AndExpr(extendedBlockFormula, new ImplExpr(new NegExpr(regPredicate), blockFormula));
                        }
                    }
                    if (lastOp instanceof MIRJump) {
                    }
                }
            }
            if (changeFormula) {
                mapFormulas.set(currentBlockName, extendedBlockFormula);
            }
        }
        else {
            mapFormulas.set(currentBlockName, blockFormula);
        }
        //---------------------------------------------------------------------------------------------
    }
    //---------------------------------------------------------------------------------------------
    // Collects all the formulas
    return makeConjunction(Array.from(mapFormulas.values()));
    //---------------------------------------------------------------------------------------------
}

export { collectFormulas, typesSeen }