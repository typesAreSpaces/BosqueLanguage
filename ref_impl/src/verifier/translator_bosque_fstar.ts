//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { MIRBasicBlock, MIRJumpCond, MIROp, MIROpTag, MIRVarStore, MIRRegisterArgument, MIRReturnAssign, MIRPhi, MIRBinCmp, MIRArgument, MIRBinOp, MIRPrefixOp, MIRCallNamespaceFunction, MIRBody } from "../compiler/mir_ops";
import { computeBlockLinks, FlowLink } from "../compiler/mir_info";
import { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr } from "./expression_expr";
import { IntType, BoolType } from "./type_expr";
import { ConstTerm, VarTerm, FuncTerm, TermExpr } from "./term_expr";
import { sanitizeName } from "./util";
import { MIRFunctionDecl } from "../compiler/mir_assembly";

class TranslatorBosqueFStar {
    static readonly intType = new IntType();
    static readonly boolType = new BoolType();
    static readonly DEBUGGING = false;
    
    readonly stack_programs = [] as [string, string[], ExprExpr][];
    readonly mapDeclarations: Map<string, MIRFunctionDecl>;

    constructor(mapDeclarations: Map<string, MIRFunctionDecl>) {
        this.mapDeclarations = mapDeclarations;
    }

    static debugging(message: string, flag: boolean): void {
        if (flag) {
            console.log(message);
        }
    }

    static argumentToExpr(arg: MIRArgument): TermExpr {
        // This branch handles variables
        if (arg instanceof MIRRegisterArgument) {
            // FIX: Use the right type!
            // return new VarExpr(arg, resolveType(stringVariableToStringType.get(argName) as string));
            return new VarTerm(sanitizeName(arg.nameID), TranslatorBosqueFStar.intType);
        }
        // This branch handles constants
        else {
            // FIX: Use the right type!
            // return new ConstExpr(arg.stringify(), resolveType(stringConstantToStringType(arg.nameID)));
            return new ConstTerm(arg.stringify(), TranslatorBosqueFStar.intType);
        }
    }

    opToAssignment(op: MIROp, comingFrom: string): [VarTerm, TermExpr] {
        switch (op.tag) {
            case MIROpTag.LoadConst:
            case MIROpTag.LoadConstTypedString:
            case MIROpTag.AccessNamespaceConstant:
            case MIROpTag.AccessConstField:
            case MIROpTag.LoadFieldDefaultValue: {
                TranslatorBosqueFStar.debugging("LoadFieldDefaultValue Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_LoadFieldDefaultValue", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.AccessCapturedVariable: {
                TranslatorBosqueFStar.debugging("AcessCapturedVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_AccessCapturedVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.AccessArgVariable: {
                TranslatorBosqueFStar.debugging("AccessArgVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_AccessArgVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.AccessLocalVariable: {
                TranslatorBosqueFStar.debugging("AcessLocalVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_AcessLocalVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.ConstructorPrimary: {
                TranslatorBosqueFStar.debugging("ConstructorPrimary Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_ConstructorPrimary", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.ConstructorPrimaryCollectionEmpty: {
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionEmpty Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_ConstructorPrimaryCollectionEmpty", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.ConstructorPrimaryCollectionSingletons: {
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionSingletons Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_ConstructorPrimaryCollectionSingletons", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.ConstructorPrimaryCollectionCopies: {
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionCopies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_ConstructorPrimaryCollectionCopies", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.ConstructorPrimaryCollectionMixed: {
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionMixed Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_ConstructorPrimaryCollectionMixed", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
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

                // formula = new EqualityTerm(new FuncExpr("TupleLength", new TranslatorBosqueFStar.intType(), [regVar]),
                //     new ConstExpr(opConstructorTuple.args.length.toString(), new TranslatorBosqueFStar.intType())
                // );

                // opConstructorTuple.args.map((arg, index) => {
                //     let argExpr = argumentToTermExpr(arg, section);
                //     formula = new AndExpr(formula,
                //         new EqualityTerm(
                //             new FuncExpr("TupleElement", argExpr.ty, [regVar, new ConstExpr(index.toString(), new TranslatorBosqueFStar.intType())]),
                //             BoxTermExpr(UnboxTermExpr(argExpr))))
                // });
                let temporal = [new VarTerm("_ConstructorTuple", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
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

                // formula = new EqualityTerm(new FuncExpr("RecordLength", new TranslatorBosqueFStar.intType(), [regVar]),
                //     new ConstExpr(opConstructorRecord.args.length.toString(), new TranslatorBosqueFStar.intType())
                // );

                // opConstructorRecord.args.map((arg) => {
                //     let argExpr = argumentToTermExpr(arg[1], section);
                //     formula = new AndExpr(formula,
                //         new EqualityTerm(
                //             new FuncExpr("RecordElement", argExpr.ty, [regVar, new VarExpr(arg[0], new RecordPropertyType())]),
                //             BoxTermExpr(UnboxTermExpr(argExpr))))
                // });
                let temporal = [new VarTerm("_ConstructorRecord", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.ConstructorLambda: {
                // TranslatorBosqueFStar.debugging("ConstructorLambda Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                // let opConstructorLambda = op as MIRConstructorLambda;
                // console.log(opConstructorLambda);
                let temporal = [new VarTerm("_ConstructorLambda", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.CallNamespaceFunction: {
                let opCallNamespaceFunction = op as MIRCallNamespaceFunction;
                let currentFunctionKey = opCallNamespaceFunction.fkey;
                // The following line will keep pushing to 
                // the stack_expressions stack
                this.collectExpr(currentFunctionKey);
                // FIX: Use the proper type
                return [TranslatorBosqueFStar.argumentToExpr(opCallNamespaceFunction.trgt), 
                    new FuncTerm(sanitizeName(currentFunctionKey), 
                    opCallNamespaceFunction.args.map(TranslatorBosqueFStar.argumentToExpr), 
                    TranslatorBosqueFStar.intType)]; // This one
            }
            case MIROpTag.CallStaticFunction: {
                TranslatorBosqueFStar.debugging("CallStaticFunction Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_CallStaticFunction", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
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
                //             new ConstExpr(opMIRAccessFromIndex.idx.toString(), new TranslatorBosqueFStar.intType())]
                //         ))));
                let temporal = [new VarTerm("_MIRAccessFromIndex", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRProjectFromIndecies: {
                TranslatorBosqueFStar.debugging("MIRProjectFromIndecies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRProjectFromIndecies", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
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
                let temporal = [new VarTerm("_MIRAccessFromProperty", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRProjectFromProperties: {
                TranslatorBosqueFStar.debugging("MIRProjectFromProperties Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRProjectFromProperties", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRAccessFromField: {
                TranslatorBosqueFStar.debugging("MIRAccessFromField Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRAccessFromField", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRProjectFromFields: {
                TranslatorBosqueFStar.debugging("MIRProjectFromFields Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRProjectFromFields", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeTuple Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRProjectFromTypeTuple", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeRecord Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRProjectFromTypeRecord", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRProjectFromTypeConcept: {
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeConcept Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRProjectFromTypeConcept", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRModifyWithIndecies: {
                TranslatorBosqueFStar.debugging("MIRModifyWithIndecies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRModifyWithIndecies", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRModifyWithProperties: {
                TranslatorBosqueFStar.debugging("MIRModifyWithProperties Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRModifyWithProperties", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRModifyWithFields: {
                TranslatorBosqueFStar.debugging("MIRModifyWithFields Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRModifyWithFields", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRStructuredExtendTuple: {
                TranslatorBosqueFStar.debugging("MIRStructuredExtendedTuple Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRStructuredExtendTuple", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRStructuredExtendRecord: {
                TranslatorBosqueFStar.debugging("MIRStructuredExtendRecord Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRStructuredExtendRecord", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRStructuredExtendObject: {
                TranslatorBosqueFStar.debugging("MIRStructuredExtendObject Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRStructuredExtendObject", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRInvokeKnownTarget: {
                TranslatorBosqueFStar.debugging("MIRInvokeKnownTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRInvokeKnownTarget", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                TranslatorBosqueFStar.debugging("MIRInvokeVirtualTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRInvokeVirtualTarget", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRCallLambda: {
                TranslatorBosqueFStar.debugging("MIRCallLambda Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRCallLambda", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRPrefixOp: {
                let opPrefixOp = op as MIRPrefixOp;
                console.log(opPrefixOp);
                // FIX: Use the proper types
                return [TranslatorBosqueFStar.argumentToExpr(opPrefixOp.trgt),
                new FuncTerm(TermExpr.unaryOpToFStar.get(opPrefixOp.op) as string,
                    [TranslatorBosqueFStar.argumentToExpr(opPrefixOp.arg)],
                    TranslatorBosqueFStar.intType)]; // This type
            }
            case MIROpTag.MIRBinOp: {
                let opBinOp = op as MIRBinOp;
                let lhs = TranslatorBosqueFStar.argumentToExpr(opBinOp.lhs);
                let rhs = TranslatorBosqueFStar.argumentToExpr(opBinOp.rhs);
                return [TranslatorBosqueFStar.argumentToExpr(opBinOp.trgt),
                new FuncTerm(TermExpr.binOpToFStar.get(opBinOp.op) as string,
                    [lhs, rhs],
                    TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRBinEq: {
                TranslatorBosqueFStar.debugging("MIRBinEq Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRBinEq", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRBinCmp: {
                // The predicate returned is of type Bool
                // because the operations to arrive at this
                // point are <, <=, >, >= only
                let opBinCmp = op as MIRBinCmp;
                let lhs = TranslatorBosqueFStar.argumentToExpr(opBinCmp.lhs);
                let rhs = TranslatorBosqueFStar.argumentToExpr(opBinCmp.rhs);
                // TODO: Is still necessary check if the type is either
                // an int or a string?
                return [TranslatorBosqueFStar.argumentToExpr(opBinCmp.trgt),
                new FuncTerm((TermExpr.binOpToFStar.get(opBinCmp.op) as string), [lhs, rhs], TranslatorBosqueFStar.boolType)];
            }
            case MIROpTag.MIRRegAssign: {
                TranslatorBosqueFStar.debugging("MIRRegAssign Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRRegAssign", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRTruthyConvert: {
                TranslatorBosqueFStar.debugging("MIRTruthyConvert Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRTruthyConvert", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRVarStore: {
                let opVarStore = op as MIRVarStore;
                return [TranslatorBosqueFStar.argumentToExpr(opVarStore.name), TranslatorBosqueFStar.argumentToExpr(opVarStore.src)];
            }
            case MIROpTag.MIRReturnAssign: {
                let opReturnAssign = op as MIRReturnAssign;
                return [TranslatorBosqueFStar.argumentToExpr(opReturnAssign.name), TranslatorBosqueFStar.argumentToExpr(opReturnAssign.src)];
            }
            case MIROpTag.MIRAbort: {
                TranslatorBosqueFStar.debugging("MIRAbort Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRAbort", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRDebug: {
                TranslatorBosqueFStar.debugging("MIRDDebug Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRDebug", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRJump: {
                // This return value here won't be used because collecExpr doesnt include it!
                // by slicing the array of ops from 1
                return [new VarTerm("_MIRJump", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
            }
            case MIROpTag.MIRJumpCond: {
                // This return value here won't be used because collecExpr doesnt include it!
                // by slicing the array of ops from 1
                return [new VarTerm("_MIRJumpCond", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
            }
            case MIROpTag.MIRJumpNone: {
                // TODO: Needs testing
                // This return value here won't be used because collecExpr doesnt include it!
                // by slicing the array of ops from 1
                return [new VarTerm("_MIRJumpNone", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
            }
            case MIROpTag.MIRVarLifetimeStart: {
                // let opVarLifetimeStart = op as MIRVarLifetimeStart;
                // // We don't check if opVarLifetimeStart
                // // is an instance of MIRRegisterArgument
                // // because we know it is always a variable
                // let sectionName = section + "_" + opVarLifetimeStart.name;
                // stringVariableToStringType.set(sectionName, opVarLifetimeStart.rtype);
                let temporal = [new VarTerm("_MIRVarLifetimeStart", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRVarLifetimeEnd: {
                TranslatorBosqueFStar.debugging("MIRVarLifetimeEnd Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRVarLifetimeEnd", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRPhi: {
                let opPhi = op as MIRPhi;
                return [TranslatorBosqueFStar.argumentToExpr(opPhi.trgt), TranslatorBosqueFStar.argumentToExpr(opPhi.src.get(comingFrom) as MIRRegisterArgument)];
            }
            case MIROpTag.MIRIsTypeOfNone: {
                // let opIsTypeOfNone = op as MIRIsTypeOfNone;

                // let regName = section + "_" + opIsTypeOfNone.trgt.nameID;
                // stringVariableToStringType.set(regName, "NSCore::Bool");

                // return new EqualityTerm(new VarExpr(regName, new TranslatorBosqueFStar.boolType()),
                //     BoxFormulaExpr(new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"),
                //         [argumentToTermExpr(opIsTypeOfNone.arg, section)]), BNone)));
                let temporal = [new VarTerm("_MIRIsTypeOfNone", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRIsTypeOfSome: {
                TranslatorBosqueFStar.debugging("MIRIsTypeOfSome Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                // let opIsTypeOfSome = op as MIRIsTypeOfSome;
                // console.log(opIsTypeOfSome);
                let temporal = [new VarTerm("_MIRIsTypeOfSome", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            case MIROpTag.MIRIsTypeOf: {
                TranslatorBosqueFStar.debugging("MIRIsTypeOf Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_MIRIsTypeOf", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
            }
            default:
                TranslatorBosqueFStar.debugging("This might be a problem", TranslatorBosqueFStar.DEBUGGING);
                let temporal = [new VarTerm("_default_problem", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)] as [VarTerm, TermExpr];
                return temporal;
        }
    }

    opsToExpr(ops: MIROp[], comingFrom: string, program: ExprExpr): ExprExpr {
        return ops.reduce((partialProgram, currentOp) => {
            let [lval, rval] = this.opToAssignment(currentOp, comingFrom);
            return new AssignmentExpr(lval, rval, partialProgram);
        }, program);
    }

    // params is a sorted array of MIRFunctionParameter
    // i.e. the first element corresponds to the first argument, ... and so on.
    // We resolve nameing by prefixing the section variable to every name encountered
    // function collectExpr(mapBlocks: Map<string, MIRBasicBlock>, info: InfoFunctionCall): ExprExpr {
    collectExpr(fkey : string): [string, string[], ExprExpr][] {
        let declarations = (this.mapDeclarations.get(fkey) as MIRFunctionDecl).invoke;
        let mapBlocks = (declarations.body as MIRBody).body;
        if (typeof (mapBlocks) === "string") {
            throw new Error("The program is a string\n");
        }
        else {
            const flow = computeBlockLinks(mapBlocks);
            // console.log("Blocks:-----------------------------------------------------------------------");
            // console.log(mapBlocks);
            // console.log("More detailed Blocks:---------------------------------------------------------");
            // mapBlocks.forEach(x => console.log(x));
            // console.log("More detailed++ Blocks:-------------------------------------------------------");
            // mapBlocks.forEach(x => console.log(x.jsonify()));
            
            // We need to reverse the currentBlockFormula.ops
            // because opsToExpr requires it
            mapBlocks.forEach(x => x.ops.reverse());

            let traverse = (block: MIRBasicBlock, comingFrom: string): ExprExpr => {
                mapBlocks = mapBlocks as Map<string, MIRBasicBlock>;
                let currentFlow = flow.get(block.label) as FlowLink;
                let currentBlockFormula = mapBlocks.get(block.label) as MIRBasicBlock;
                console.assert(currentBlockFormula.ops.length > 0);

                switch (currentFlow.succs.size) {
                    case 0: {
                        let lastOp = currentBlockFormula.ops[0] as MIRVarStore;
                        console.assert(lastOp != undefined);

                        let regName = sanitizeName(lastOp.name.nameID);
                        // FIX: Use the correct type!
                        return this.opsToExpr(currentBlockFormula.ops, comingFrom,
                            new ReturnExpr(new VarTerm(regName, TranslatorBosqueFStar.intType)));
                    }
                    case 1: {
                        let successorLabel = currentFlow.succs.values().next().value;
                        return this.opsToExpr(currentBlockFormula.ops.slice(1), comingFrom,
                            traverse(mapBlocks.get(successorLabel) as MIRBasicBlock, block.label));
                    }
                    case 2: {
                        let jumpCondOp = block.ops[0] as MIRJumpCond;
                        let regName = sanitizeName(jumpCondOp.arg.nameID);
                        let condition = new FuncTerm("op_Equality",
                            [new VarTerm(regName, TranslatorBosqueFStar.boolType), new ConstTerm("true", TranslatorBosqueFStar.boolType)], TranslatorBosqueFStar.boolType);
                        let branchTrue = traverse(mapBlocks.get(jumpCondOp.trueblock) as MIRBasicBlock, block.label);
                        let branchFalse = traverse(mapBlocks.get(jumpCondOp.falseblock) as MIRBasicBlock, block.label);
                        return this.opsToExpr(currentBlockFormula.ops.slice(1), comingFrom,
                            new ConditionalExpr(condition, branchTrue, branchFalse));
                    }
                    default: {
                        throw new Error("Wrong Control-Flow graph. The out-degree of any node cannot be more than 2.");
                    }
                }
            }
            this.stack_programs.push([fkey, 
                declarations.params.map(x => x.name), 
                traverse(mapBlocks.get("entry") as MIRBasicBlock, "entry")]);
            return this.stack_programs;
        }
    }
}

export { TranslatorBosqueFStar }