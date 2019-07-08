//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRBasicBlock, MIRJumpCond, MIROp, MIROpTag, MIRVarStore, MIRRegisterArgument, MIRReturnAssign, MIRPhi, MIRBinCmp, MIRArgument, MIRBinOp, MIRPrefixOp } from "../compiler/mir_ops";
// import { MIRBasicBlock, MIROpTag, MIRBinCmp, MIRArgument, MIROp, MIRRegisterArgument, MIRVarLifetimeStart, MIRVarStore, MIRReturnAssign, MIRJumpCond, MIRBinOp, MIRPhi, MIRJump, MIRIsTypeOfSome, MIRIsTypeOfNone, MIRConstructorTuple, MIRConstructorLambda, MIRConstructorRecord, MIRAccessFromIndex, MIRAccessFromProperty, MIRCallNamespaceFunction } from "../compiler/mir_ops";
import { computeBlockLinks, FlowLink } from "../compiler/mir_info";
import { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr } from "./expression_expr";
import { IntType, BoolType } from "./type_expr";
import { ConstTerm, VarTerm, FuncTerm, TermExpr } from "./term_expr";
import { sanitizeName } from "./util";

let intType = new IntType();
let boolType = new BoolType();

let DEBUGGING = false;

function debugging(message: string, flag: boolean): void {
    if (flag) {
        console.log(message);
    }
}

function argumentToExpr(arg: MIRArgument): TermExpr {
    // This branch handles variables
    if (arg instanceof MIRRegisterArgument) {
        // FIX: Use the right type!
        // return new VarExpr(arg, resolveType(stringVariableToStringType.get(argName) as string));
        return new VarTerm(sanitizeName(arg.nameID), intType);
    }
    // This branch handles constants
    else {
        // FIX: Use the right type!
        // return new ConstExpr(arg.stringify(), resolveType(stringConstantToStringType(arg.nameID)));
        return new ConstTerm(arg.stringify(), intType);
    }
}

function opToAssignment(op: MIROp, comingFrom : string): [VarTerm, TermExpr] {
    switch (op.tag) {
        case MIROpTag.LoadConst:
        case MIROpTag.LoadConstTypedString:
        case MIROpTag.AccessNamespaceConstant:
        case MIROpTag.AccessConstField:
        case MIROpTag.LoadFieldDefaultValue: {
            debugging("LoadFieldDefaultValue Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_LoadFieldDefaultValue", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.AccessCapturedVariable: {
            debugging("AcessCapturedVariable Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_AccessCapturedVariable", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.AccessArgVariable: {
            debugging("AccessArgVariable Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_AccessArgVariable", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.AccessLocalVariable: {
            debugging("AcessLocalVariable Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_AcessLocalVariable", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.ConstructorPrimary: {
            debugging("ConstructorPrimary Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_ConstructorPrimary", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.ConstructorPrimaryCollectionEmpty: {
            debugging("ConstructorPrimaryCollectionEmpty Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_ConstructorPrimaryCollectionEmpty", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.ConstructorPrimaryCollectionSingletons: {
            debugging("ConstructorPrimaryCollectionSingletons Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_ConstructorPrimaryCollectionSingletons", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.ConstructorPrimaryCollectionCopies: {
            debugging("ConstructorPrimaryCollectionCopies Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_ConstructorPrimaryCollectionCopies", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.ConstructorPrimaryCollectionMixed: {
            debugging("ConstructorPrimaryCollectionMixed Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_ConstructorPrimaryCollectionMixed", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.ConstructorTuple: {
            // let opConstructorTuple = op as MIRConstructorTuple;

            // let regName = section + "_" + opConstructorTuple.trgt.nameID;
            // stringVariableToStringType.set(regName,
            //     "[" + opConstructorTuple.args.map(arg => {
            //         if (arg instanceof MIRRegisterArgument) {
            //             return stringVariableToStringType.get(section + "_" + arg.nameID);
            //         }
            //         else {
            //             return stringConstantToStringType(arg.nameID);
            //         }
            //     }).join(", ") + "]");

            // let regVar = argumentToTermExpr(opConstructorTuple.trgt, section);

            // formula = new EqualityTerm(new FuncExpr("TupleLength", new IntType(), [regVar]),
            //     new ConstExpr(opConstructorTuple.args.length.toString(), new IntType())
            // );

            // opConstructorTuple.args.map((arg, index) => {
            //     let argExpr = argumentToTermExpr(arg, section);
            //     formula = new AndExpr(formula,
            //         new EqualityTerm(
            //             new FuncExpr("TupleElement", argExpr.ty, [regVar, new ConstExpr(index.toString(), new IntType())]),
            //             BoxTermExpr(UnboxTermExpr(argExpr))))
            // });
            let temporal = [new VarTerm("_ConstructorTuple", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.ConstructorRecord: {
            // let opConstructorRecord = op as MIRConstructorRecord;

            // let regName = section + "_" + opConstructorRecord.trgt.nameID;
            // stringVariableToStringType.set(regName,
            //     "{" + opConstructorRecord.args.map(arg => {
            //         if (arg[1] instanceof MIRRegisterArgument) {
            //             return arg[0] + ":" + stringVariableToStringType.get(section + "_" + arg[1].nameID);
            //         }
            //         else {
            //             return arg[0] + ":" + stringConstantToStringType(arg[1].nameID);
            //         }
            //     }).join(", ") + "}");

            // let regVar = argumentToTermExpr(opConstructorRecord.trgt, section);

            // formula = new EqualityTerm(new FuncExpr("RecordLength", new IntType(), [regVar]),
            //     new ConstExpr(opConstructorRecord.args.length.toString(), new IntType())
            // );

            // opConstructorRecord.args.map((arg) => {
            //     let argExpr = argumentToTermExpr(arg[1], section);
            //     formula = new AndExpr(formula,
            //         new EqualityTerm(
            //             new FuncExpr("RecordElement", argExpr.ty, [regVar, new VarExpr(arg[0], new RecordPropertyType())]),
            //             BoxTermExpr(UnboxTermExpr(argExpr))))
            // });
            let temporal = [new VarTerm("_ConstructorRecord", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.ConstructorLambda: {
            // debugging("ConstructorLambda Not implemented yet", DEBUGGING);
            // let opConstructorLambda = op as MIRConstructorLambda;
            // console.log(opConstructorLambda);
            let temporal = [new VarTerm("_ConstructorLambda", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.CallNamespaceFunction: {
            // debugging("CallNamespaceFunction is being implemented", DEBUGGING);
            // let opCallNamespaceFunction = op as MIRCallNamespaceFunction;
            // console.log(opCallNamespaceFunction);

            // let [ir_body, sectionName] = bosqueToIRBody({ directory: info.directory, fileName: info.fileName, section: opCallNamespaceFunction.fkey });
            // // Not sure about this
            // let formula = collectFormula(ir_body, { directory: info.directory, fileName: info.fileName, section: sectionName });
            let temporal = [new VarTerm("_CallNamespaceFunction", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.CallStaticFunction: {
            debugging("CallStaticFunction Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_CallStaticFunction", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRAccessFromIndex: {
            // let opMIRAccessFromIndex = op as MIRAccessFromIndex;

            // let regName = section + "_" + opMIRAccessFromIndex.trgt.nameID;
            // let srcName = section + "_" + opMIRAccessFromIndex.arg.nameID;
            // let tupleTyString = stringVariableToStringType.get(srcName) as string;
            // let srcTypeString = tupleTyString.substr(1, tupleTyString.length - 2).split(", ")[opMIRAccessFromIndex.idx];

            // stringVariableToStringType.set(regName, srcTypeString);
            // let regVar = argumentToTermExpr(opMIRAccessFromIndex.trgt, section);
            // formula = new EqualityTerm(
            //     regVar,
            //     BoxTermExpr(UnboxTermExpr(
            //         new FuncExpr("TupleElement", resolveType(srcTypeString),
            //             [argumentToTermExpr(opMIRAccessFromIndex.arg, section),
            //             new ConstExpr(opMIRAccessFromIndex.idx.toString(), new IntType())]
            //         ))));
            let temporal = [new VarTerm("_MIRAccessFromIndex", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRProjectFromIndecies: {
            debugging("MIRProjectFromIndecies Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRProjectFromIndecies", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRAccessFromProperty: {
            // let opMIRAccessFromProperty = op as MIRAccessFromProperty;

            // let regName = section + "_" + opMIRAccessFromProperty.trgt.nameID;
            // let srcName = section + "_" + opMIRAccessFromProperty.arg.nameID;
            // let tupleTyString = stringVariableToStringType.get(srcName) as string;
            // let srcTypeAll = tupleTyString.substr(1, tupleTyString.length - 2).split(", ");

            // let srcTypeString: string = "";
            // for (let argString of srcTypeAll) {
            //     if (argString.startsWith(opMIRAccessFromProperty.property)) {
            //         srcTypeString = argString;
            //         break;
            //     }
            // }
            // srcTypeString = srcTypeString.slice(srcTypeString.indexOf(":") + 1);

            // stringVariableToStringType.set(regName, srcTypeString);
            // let regVar = argumentToTermExpr(opMIRAccessFromProperty.trgt, section);
            // formula = new EqualityTerm(
            //     regVar,
            //     BoxTermExpr(UnboxTermExpr(
            //         new FuncExpr("RecordElement", resolveType(srcTypeString),
            //             [argumentToTermExpr(opMIRAccessFromProperty.arg, section),
            //             new VarExpr(opMIRAccessFromProperty.property, new RecordPropertyType())]
            //         ))));
            let temporal = [new VarTerm("_MIRAccessFromProperty", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRProjectFromProperties: {
            debugging("MIRProjectFromProperties Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRProjectFromProperties", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRAccessFromField: {
            debugging("MIRAccessFromField Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRAccessFromField", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRProjectFromFields: {
            debugging("MIRProjectFromFields Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRProjectFromFields", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRProjectFromTypeTuple: {
            debugging("MIRProjectFromTypeTuple Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRProjectFromTypeTuple", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRProjectFromTypeRecord: {
            debugging("MIRProjectFromTypeRecord Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRProjectFromTypeRecord", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRProjectFromTypeConcept: {
            debugging("MIRProjectFromTypeConcept Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRProjectFromTypeConcept", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRModifyWithIndecies: {
            debugging("MIRModifyWithIndecies Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRModifyWithIndecies", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRModifyWithProperties: {
            debugging("MIRModifyWithProperties Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRModifyWithProperties", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRModifyWithFields: {
            debugging("MIRModifyWithFields Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRModifyWithFields", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRStructuredExtendTuple: {
            debugging("MIRStructuredExtendedTuple Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRStructuredExtendTuple", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRStructuredExtendRecord: {
            debugging("MIRStructuredExtendRecord Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRStructuredExtendRecord", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRStructuredExtendObject: {
            debugging("MIRStructuredExtendObject Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRStructuredExtendObject", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRInvokeKnownTarget: {
            debugging("MIRInvokeKnownTarget Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRInvokeKnownTarget", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRInvokeVirtualTarget: {
            debugging("MIRInvokeVirtualTarget Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRInvokeVirtualTarget", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRCallLambda: {
            debugging("MIRCallLambda Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRCallLambda", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRPrefixOp: {
            let opPrefixOp = op as MIRPrefixOp;
            console.log(opPrefixOp);
            // FIX: Use the proper types
            return [argumentToExpr(opPrefixOp.trgt), 
                new FuncTerm(TermExpr.unaryOpToFStar.get(opPrefixOp.op) as string, 
                [argumentToExpr(opPrefixOp.arg)], 
                intType)]; // This type
        }
        case MIROpTag.MIRBinOp: {
            let opBinOp = op as MIRBinOp;
            let lhs = argumentToExpr(opBinOp.lhs);
            let rhs = argumentToExpr(opBinOp.rhs);
            return [argumentToExpr(opBinOp.trgt), 
                new FuncTerm(TermExpr.binOpToFStar.get(opBinOp.op) as string, 
                [lhs, rhs], 
                intType)];
        }
        case MIROpTag.MIRBinEq: {
            debugging("MIRBinEq Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRBinEq", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRBinCmp: {
            // The predicate returned is of type Bool
            // because the operations to arrive at this
            // point are <, <=, >, >= only
            let opBinCmp = op as MIRBinCmp;
            let lhs = argumentToExpr(opBinCmp.lhs);
            let rhs = argumentToExpr(opBinCmp.rhs);
            // TODO: Is still necessary check if the type is either
            // an int or a string?
            return [argumentToExpr(opBinCmp.trgt), 
                new FuncTerm((TermExpr.binOpToFStar.get(opBinCmp.op) as string), [lhs, rhs], boolType)];
        }
        case MIROpTag.MIRRegAssign: {
            debugging("MIRRegAssign Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRRegAssign", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRTruthyConvert: {
            debugging("MIRTruthyConvert Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRTruthyConvert", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRVarStore: {
            let opVarStore = op as MIRVarStore;
            return [argumentToExpr(opVarStore.name), argumentToExpr(opVarStore.src)];
        }
        case MIROpTag.MIRReturnAssign: {
            let opReturnAssign = op as MIRReturnAssign;
            return [argumentToExpr(opReturnAssign.name), argumentToExpr(opReturnAssign.src)];    
        }
        case MIROpTag.MIRAbort: {
            debugging("MIRAbort Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRAbort", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRDebug: {
            debugging("MIRDDebug Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRDebug", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRJump: {            
            // This return value here won't be used because collecExpr doesnt include it!
            // by slicing the array of ops from 1
            return [new VarTerm("_MIRJump", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
        }
        case MIROpTag.MIRJumpCond: {            
            // This return value here won't be used because collecExpr doesnt include it!
            // by slicing the array of ops from 1
            return [new VarTerm("_MIRJumpCond", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
        }
        case MIROpTag.MIRJumpNone: {
            // TODO: Needs testing
            // This return value here won't be used because collecExpr doesnt include it!
            // by slicing the array of ops from 1
            return [new VarTerm("_MIRJumpNone", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
        }
        case MIROpTag.MIRVarLifetimeStart: {
            // let opVarLifetimeStart = op as MIRVarLifetimeStart;
            // // We don't check if opVarLifetimeStart
            // // is an instance of MIRRegisterArgument
            // // because we know it is always a variable
            // let sectionName = section + "_" + opVarLifetimeStart.name;
            // stringVariableToStringType.set(sectionName, opVarLifetimeStart.rtype);
            let temporal = [new VarTerm("_MIRVarLifetimeStart", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRVarLifetimeEnd: {
            debugging("MIRVarLifetimeEnd Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRVarLifetimeEnd", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRPhi: {
            let opPhi = op as MIRPhi;
            return [argumentToExpr(opPhi.trgt), argumentToExpr(opPhi.src.get(comingFrom) as MIRRegisterArgument)];
        }
        case MIROpTag.MIRIsTypeOfNone: {
            // let opIsTypeOfNone = op as MIRIsTypeOfNone;

            // let regName = section + "_" + opIsTypeOfNone.trgt.nameID;
            // stringVariableToStringType.set(regName, "NSCore::Bool");

            // return new EqualityTerm(new VarExpr(regName, new BoolType()),
            //     BoxFormulaExpr(new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"),
            //         [argumentToTermExpr(opIsTypeOfNone.arg, section)]), BNone)));
            let temporal = [new VarTerm("_MIRIsTypeOfNone", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRIsTypeOfSome: {
            debugging("MIRIsTypeOfSome Not implemented yet", DEBUGGING);
            // let opIsTypeOfSome = op as MIRIsTypeOfSome;
            // console.log(opIsTypeOfSome);
            let temporal = [new VarTerm("_MIRIsTypeOfSome", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        case MIROpTag.MIRIsTypeOf: {
            debugging("MIRIsTypeOf Not implemented yet", DEBUGGING);
            let temporal = [new VarTerm("_MIRIsTypeOf", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
        }
        default:
            debugging("This might be a problem", DEBUGGING);
            let temporal = [new VarTerm("_default_problem", intType), new ConstTerm("0", intType)] as [VarTerm, TermExpr];
            return temporal;
    }
}

function opsToExpr(ops: MIROp[], comingFrom : string, program: ExprExpr): ExprExpr {
    if (ops.length == 0) {
        return program;
    }
    else {
        let [lval, rval] = opToAssignment(ops[0], comingFrom);
        return opsToExpr(ops.slice(1), comingFrom, new AssignmentExpr(lval, rval, program));
    }
}

// params is a sorted array of MIRFunctionParameter
// i.e. the first element corresponds to the first argument, ... and so on.
// We resolve nameing by prefixing the section variable to every name encountered
// function collectExpr(mapBlocks: Map<string, MIRBasicBlock>, info: InfoFunctionCall): ExprExpr {
function collectExpr(mapBlocks: Map<string, MIRBasicBlock>): ExprExpr {
    const flow = computeBlockLinks(mapBlocks);

    console.log("Blocks:-----------------------------------------------------------------------");
    console.log(mapBlocks);
    console.log("More detailed Blocks:---------------------------------------------------------");
    mapBlocks.forEach(x => console.log(x));
    console.log("More detailed++ Blocks:-------------------------------------------------------");
    mapBlocks.forEach(x => console.log(x.jsonify()));
    console.log();

    // We need to reverse the currentBlockFormula.ops
    // because opsToExpr requires it
    mapBlocks.forEach(x => x.ops.reverse());

    function traverse(block: MIRBasicBlock, comingFrom : string): ExprExpr {
        let currentFlow = flow.get(block.label) as FlowLink;

        let currentBlockFormula = mapBlocks.get(block.label) as MIRBasicBlock;
        console.assert(currentBlockFormula.ops.length > 0);

        switch (currentFlow.succs.size) {
            case 0: {
                let lastOp = currentBlockFormula.ops[0] as MIRVarStore;
                console.assert(lastOp != undefined);

                let regName = sanitizeName(lastOp.name.nameID);
                // FIX: Use the correct type!
                return opsToExpr(currentBlockFormula.ops, comingFrom,
                    new ReturnExpr(new VarTerm(regName, intType)));
            }
            case 1: {
                let successorLabel = currentFlow.succs.values().next().value;
                return opsToExpr(currentBlockFormula.ops.slice(1), comingFrom,
                    traverse(mapBlocks.get(successorLabel) as MIRBasicBlock, block.label));
            }
            case 2: {
                let jumpCondOp = block.ops[0] as MIRJumpCond;
                let regName = sanitizeName(jumpCondOp.arg.nameID);
                let condition = new FuncTerm("op_Equality",
                    [new VarTerm(regName, boolType), new ConstTerm("true", boolType)], boolType);
                let branchTrue = traverse(mapBlocks.get(jumpCondOp.trueblock) as MIRBasicBlock, block.label);
                let branchFalse = traverse(mapBlocks.get(jumpCondOp.falseblock) as MIRBasicBlock, block.label);
                return opsToExpr(currentBlockFormula.ops.slice(1), comingFrom, 
                    new ConditionalExpr(condition, branchTrue, branchFalse));
            }
            default: {
                throw new Error("Wrong Control-Flow graph. The out-degree of any node cannot be more than 2.");
            }
        }
    }
    return traverse(mapBlocks.get("entry") as MIRBasicBlock, "entry");
}

export { collectExpr }