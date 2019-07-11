//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import { MIRBasicBlock, MIRJumpCond, MIROp, MIROpTag, MIRVarStore, MIRRegisterArgument, MIRReturnAssign, MIRPhi, MIRBinCmp, MIRArgument, MIRBinOp, MIRPrefixOp, MIRCallNamespaceFunction, MIRBody, MIRConstructorTuple, MIRAccessFromIndex } from "../compiler/mir_ops";
import { computeBlockLinks, FlowLink } from "../compiler/mir_info";
import { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr } from "./expression_expr";
import { IntType, BoolType, FuncType, TypeExpr, TupleType, PolymorphicTupleType } from "./type_expr";
import { ConstTerm, VarTerm, FuncTerm, TermExpr } from "./term_expr";
import { sanitizeName } from "./util";
import { MIRFunctionDecl } from "../compiler/mir_assembly";

class FStarDeclaration {
    readonly fkey: string;
    readonly args: string[];
    readonly program: ExprExpr;
    readonly type: FuncType;
    constructor(fkey: string, args: string[], program: ExprExpr, type: FuncType) {
        this.fkey = fkey;
        this.args = args;
        this.program = program;
        this.type = type;
    }
    print(fd: number): void {
        FS.writeSync(fd, `val ${sanitizeName(this.fkey)} : ${this.type.getFStarType()}\n`);
        FS.writeSync(fd, `let ${sanitizeName(this.fkey)} ${this.args.join(" ")} = \n${this.program.toML(1)}\n\n`);
    }
}

class TranslatorBosqueFStar {
    static readonly intType = new IntType();
    static readonly boolType = new BoolType();
    static readonly skipCommand = new VarTerm("_skip", TranslatorBosqueFStar.boolType);
    static readonly DEBUGGING = false;
    // typesSeen : String[MangledNamewithFkey] -> String[Type]
    static readonly typesSeen = new Map<string, string>();

    readonly mapDeclarations: Map<string, MIRFunctionDecl>;
    readonly fileName: string;
    readonly stack_declarations = [] as FStarDeclaration[];
    readonly isFkeyDeclared: Set<string>;

    constructor(mapDeclarations: Map<string, MIRFunctionDecl>, fileName: string) {
        this.mapDeclarations = mapDeclarations;
        this.fileName = fileName;
        this.isFkeyDeclared = new Set<string>();
    }

    printPrelude(fd: number): void {
        FS.writeSync(fd, `module ${this.fileName.slice(0, -4)}\n\n`);
    }

    static closeFS(fd: number): void {
        FS.closeSync(fd);
    }

    static debugging(message: string, flag: boolean): void {
        if (flag) {
            console.log(message);
        }
    }

    // TODO: Add more types as needed
    static stringTypeToType(s: string): TypeExpr {
        switch (s) {
            case "NSCore::Int": {
                return TranslatorBosqueFStar.intType;
            }
            case "NSCore::Bool": {
                return TranslatorBosqueFStar.boolType;
            }
            default: {
                if (s.charAt(0) == '[') {
                    return new TupleType(s
                        .slice(1)
                        .slice(0, -1)
                        .split(", ")
                        .map(TranslatorBosqueFStar.stringTypeToType));
                }
                throw new Error("Not a valid type, yet");
            }
        }
    }

    // TODO: Add more types as needed
    static stringConstToType(s: string): TypeExpr {
        throw new Error("Not implemented yet");
    }

    static argumentToExpr(arg: MIRArgument): TermExpr {
        // This branch handles variables
        if (arg instanceof MIRRegisterArgument) {
            if(TranslatorBosqueFStar.typesSeen.get(sanitizeName(arg.nameID)) == undefined){
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(arg.nameID), "NSCore::Int");
            }
            return new VarTerm(sanitizeName(arg.nameID),
                TranslatorBosqueFStar.stringTypeToType(TranslatorBosqueFStar.typesSeen.get(sanitizeName(arg.nameID)) as string));
        }
        // This branch handles constants
        else {
            // FIX: Use the proper type
            return new ConstTerm(arg.stringify(),
                TranslatorBosqueFStar.intType); // This one
            // The following implementation goes in the right
            // direction, but it should use information from
            // the MIRConstantArgument
            // return new ConstTerm(arg.stringify(),
            //     TranslatorBosqueFStar.stringConstToType(TranslatorBosqueFStar.typesSeen.get(sanitizeName(arg.nameID)) as string));
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
                return [new VarTerm("_LoadFieldDefaultValue", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.AccessCapturedVariable: {
                TranslatorBosqueFStar.debugging("AcessCapturedVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_AccessCapturedVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.AccessArgVariable: {
                TranslatorBosqueFStar.debugging("AccessArgVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_AccessArgVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.AccessLocalVariable: {
                TranslatorBosqueFStar.debugging("AcessLocalVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_AcessLocalVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorPrimary: {
                // let opConstructorPrimary = op as MIRConstructorPrimary;
                TranslatorBosqueFStar.debugging("ConstructorPrimary Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimary", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorPrimaryCollectionEmpty: {
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionEmpty Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionEmpty", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorPrimaryCollectionSingletons: {
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionSingletons Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionSingletons", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorPrimaryCollectionCopies: {
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionCopies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionCopies", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorPrimaryCollectionMixed: {
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionMixed Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionMixed", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorTuple: {
                let opConstructorTuple = op as MIRConstructorTuple;
                // FIX: Use the right type
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opConstructorTuple.trgt.nameID),
                    "NSCore::Int"); // This one
                return [TranslatorBosqueFStar.argumentToExpr(opConstructorTuple.trgt),
                new FuncTerm("Mktuple__" + opConstructorTuple.args.length,
                    opConstructorTuple.args.map(x => TranslatorBosqueFStar.argumentToExpr(x)),
                    new PolymorphicTupleType(opConstructorTuple.args.length))];
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
                return [new VarTerm("_ConstructorRecord", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorLambda: {
                // TranslatorBosqueFStar.debugging("ConstructorLambda Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                // let opConstructorLambda = op as MIRConstructorLambda;
                // console.log(opConstructorLambda);
                return [new VarTerm("_ConstructorLambda", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.CallNamespaceFunction: {
                const opCallNamespaceFunction = op as MIRCallNamespaceFunction;
                const currentFunctionKey = opCallNamespaceFunction.fkey;
                // The following line will keep pushing to 
                // the stack_expressions stack
                this.collectExpr(currentFunctionKey);
                // FIX: Use the right type
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opCallNamespaceFunction.trgt.nameID), "NSCore::Int");
                return [TranslatorBosqueFStar.argumentToExpr(opCallNamespaceFunction.trgt),
                new FuncTerm(sanitizeName(currentFunctionKey),
                    opCallNamespaceFunction.args.map(TranslatorBosqueFStar.argumentToExpr),
                    TranslatorBosqueFStar.stringTypeToType((this.mapDeclarations.get(currentFunctionKey) as MIRFunctionDecl).invoke.resultType.trkey))];
            }
            case MIROpTag.CallStaticFunction: {
                TranslatorBosqueFStar.debugging("CallStaticFunction Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_CallStaticFunction", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRAccessFromIndex: {
                let opMIRAccessFromIndex = op as MIRAccessFromIndex;
                // console.log(opMIRAccessFromIndex);
                // FIX: Use the proper type
                let somethingAboutLength = "2";
                // FIX: Use the right type
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opMIRAccessFromIndex.trgt.nameID), "NSCore::Int");
                return [TranslatorBosqueFStar.argumentToExpr(opMIRAccessFromIndex.trgt),
                new FuncTerm("Mktuple__" + somethingAboutLength + "?._" + (opMIRAccessFromIndex.idx + 1),
                    [TranslatorBosqueFStar.argumentToExpr(opMIRAccessFromIndex.arg)],
                    TranslatorBosqueFStar.intType)]; // This one
            }
            case MIROpTag.MIRProjectFromIndecies: {
                TranslatorBosqueFStar.debugging("MIRProjectFromIndecies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromIndecies", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
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
                return [new VarTerm("_MIRAccessFromProperty", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRProjectFromProperties: {
                TranslatorBosqueFStar.debugging("MIRProjectFromProperties Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromProperties", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRAccessFromField: {
                TranslatorBosqueFStar.debugging("MIRAccessFromField Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRAccessFromField", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRProjectFromFields: {
                TranslatorBosqueFStar.debugging("MIRProjectFromFields Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromFields", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeTuple Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromTypeTuple", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeRecord Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromTypeRecord", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRProjectFromTypeConcept: {
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeConcept Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromTypeConcept", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRModifyWithIndecies: {
                TranslatorBosqueFStar.debugging("MIRModifyWithIndecies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRModifyWithIndecies", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRModifyWithProperties: {
                TranslatorBosqueFStar.debugging("MIRModifyWithProperties Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRModifyWithProperties", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRModifyWithFields: {
                TranslatorBosqueFStar.debugging("MIRModifyWithFields Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRModifyWithFields", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRStructuredExtendTuple: {
                TranslatorBosqueFStar.debugging("MIRStructuredExtendedTuple Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRStructuredExtendTuple", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRStructuredExtendRecord: {
                TranslatorBosqueFStar.debugging("MIRStructuredExtendRecord Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRStructuredExtendRecord", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRStructuredExtendObject: {
                TranslatorBosqueFStar.debugging("MIRStructuredExtendObject Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRStructuredExtendObject", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRInvokeKnownTarget: {
                TranslatorBosqueFStar.debugging("MIRInvokeKnownTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRInvokeKnownTarget", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                TranslatorBosqueFStar.debugging("MIRInvokeVirtualTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRInvokeVirtualTarget", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRCallLambda: {
                TranslatorBosqueFStar.debugging("MIRCallLambda Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRCallLambda", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRPrefixOp: {
                const opPrefixOp = op as MIRPrefixOp;
                // FIX: Use the right type
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opPrefixOp.trgt.nameID), "NSCore::Int");
                // FIX: Use the proper types
                return [TranslatorBosqueFStar.argumentToExpr(opPrefixOp.trgt),
                new FuncTerm(TermExpr.unaryOpToFStar.get(opPrefixOp.op) as string,
                    [TranslatorBosqueFStar.argumentToExpr(opPrefixOp.arg)],
                    TranslatorBosqueFStar.intType)]; // This one
            }
            case MIROpTag.MIRBinOp: {
                const opBinOp = op as MIRBinOp;
                const lhs = TranslatorBosqueFStar.argumentToExpr(opBinOp.lhs);
                const rhs = TranslatorBosqueFStar.argumentToExpr(opBinOp.rhs);
                // FIX: Use the right type
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opBinOp.trgt.nameID), "NSCore::Int");
                return [TranslatorBosqueFStar.argumentToExpr(opBinOp.trgt),
                new FuncTerm(TermExpr.binOpToFStar.get(opBinOp.op) as string,
                    [lhs, rhs],
                    TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRBinEq: {
                TranslatorBosqueFStar.debugging("MIRBinEq Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRBinEq", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRBinCmp: {
                // The predicate returned is of type Bool
                // because the operations to arrive at this
                // point are <, <=, >, >= only
                const opBinCmp = op as MIRBinCmp;
                const lhs = TranslatorBosqueFStar.argumentToExpr(opBinCmp.lhs);
                const rhs = TranslatorBosqueFStar.argumentToExpr(opBinCmp.rhs);
                // TODO: Is still necessary check if the type is either
                // an int or a string?
                // FIX: Use the right type
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opBinCmp.trgt.nameID), "NSCore::Int");
                return [TranslatorBosqueFStar.argumentToExpr(opBinCmp.trgt),
                new FuncTerm((TermExpr.binOpToFStar.get(opBinCmp.op) as string), [lhs, rhs], TranslatorBosqueFStar.boolType)];
            }
            case MIROpTag.MIRRegAssign: {
                TranslatorBosqueFStar.debugging("MIRRegAssign Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRRegAssign", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRTruthyConvert: {
                TranslatorBosqueFStar.debugging("MIRTruthyConvert Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRTruthyConvert", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRVarStore: {
                const opVarStore = op as MIRVarStore;
                // FIX: Use the right type
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opVarStore.name.nameID), "NSCore::Int");
                return [TranslatorBosqueFStar.argumentToExpr(opVarStore.name), TranslatorBosqueFStar.argumentToExpr(opVarStore.src)];
            }
            case MIROpTag.MIRReturnAssign: {
                const opReturnAssign = op as MIRReturnAssign;
                // FIX: Use the right type
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opReturnAssign.name.nameID), "NSCore::Int");
                return [TranslatorBosqueFStar.argumentToExpr(opReturnAssign.name), TranslatorBosqueFStar.argumentToExpr(opReturnAssign.src)];
            }
            case MIROpTag.MIRAbort: {
                TranslatorBosqueFStar.debugging("MIRAbort Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRAbort", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRDebug: {
                TranslatorBosqueFStar.debugging("MIRDDebug Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRDebug", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRJump: {
                return [TranslatorBosqueFStar.skipCommand, TranslatorBosqueFStar.skipCommand];
            }
            case MIROpTag.MIRJumpCond: {
                return [TranslatorBosqueFStar.skipCommand, TranslatorBosqueFStar.skipCommand];
            }
            case MIROpTag.MIRJumpNone: {
                return [TranslatorBosqueFStar.skipCommand, TranslatorBosqueFStar.skipCommand];
            }
            case MIROpTag.MIRVarLifetimeStart: {
                return [TranslatorBosqueFStar.skipCommand, TranslatorBosqueFStar.skipCommand];
            }
            case MIROpTag.MIRVarLifetimeEnd: {
                return [TranslatorBosqueFStar.skipCommand, TranslatorBosqueFStar.skipCommand];
            }
            case MIROpTag.MIRPhi: {
                const opPhi = op as MIRPhi;
                // FIX: Use the right type 
                // ?? I'm not so sure about this one
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opPhi.trgt.nameID), "NSCore::Int");
                return [TranslatorBosqueFStar.argumentToExpr(opPhi.trgt), TranslatorBosqueFStar.argumentToExpr(opPhi.src.get(comingFrom) as MIRRegisterArgument)];
            }
            case MIROpTag.MIRIsTypeOfNone: {
                // let opIsTypeOfNone = op as MIRIsTypeOfNone;

                // let regName = section + "_" + opIsTypeOfNone.trgt.nameID;
                // stringVariableToStringType.set(regName, "NSCore::Bool");

                // return new EqualityTerm(new VarExpr(regName, new TranslatorBosqueFStar.boolType()),
                //     BoxFormulaExpr(new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"),
                //         [argumentToTermExpr(opIsTypeOfNone.arg, section)]), BNone)));
                return [new VarTerm("_MIRIsTypeOfNone", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRIsTypeOfSome: {
                TranslatorBosqueFStar.debugging("MIRIsTypeOfSome Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                // let opIsTypeOfSome = op as MIRIsTypeOfSome;
                // console.log(opIsTypeOfSome);
                return [new VarTerm("_MIRIsTypeOfSome", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRIsTypeOf: {
                TranslatorBosqueFStar.debugging("MIRIsTypeOf Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRIsTypeOf", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            default:
                TranslatorBosqueFStar.debugging("This might be a problem", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_default_problem", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
        }
    }

    opsToExpr(ops: MIROp[], comingFrom: string, program: ExprExpr): ExprExpr {
        // return ops.reduce((partialProgram, currentOp) => {
        //     const [lval, rval] = this.opToAssignment(currentOp, comingFrom);
        //     if (lval.symbolName == "_skip") {
        //         return partialProgram;
        //     }
        //     else {
        //         return new AssignmentExpr(lval, rval, partialProgram);
        //     }
        // }, program);
        if(ops.length == 0){
            return program;
        }
        else{
            const [lval, rval] = this.opToAssignment(ops[0], comingFrom);
            if(lval.symbolName == "_skip"){
                return this.opsToExpr(ops.slice(1), comingFrom, program);
            }   
            else{
                return new AssignmentExpr(lval, rval, this.opsToExpr(ops.slice(1), comingFrom, program));
            }
        } 
    }

    collectExpr(fkey: string): FStarDeclaration[] {
        const declarations = (this.mapDeclarations.get(fkey) as MIRFunctionDecl).invoke;
        let mapBlocks = (declarations.body as MIRBody).body;
        if (typeof (mapBlocks) === "string") {
            throw new Error(`The program with fkey ${fkey} is a string\n`);
        }
        else {
            const returnType = TranslatorBosqueFStar.stringTypeToType(declarations.resultType.trkey);
            const flow = computeBlockLinks(mapBlocks);

            // console.log("Blocks:-----------------------------------------------------------------------");
            // console.log(mapBlocks);
            // console.log("More detailed Blocks:---------------------------------------------------------");
            // mapBlocks.forEach(x => console.log(x));
            // console.log("More detailed++ Blocks:-------------------------------------------------------");
            // mapBlocks.forEach(x => console.log(x.jsonify()));

            const traverse = (block: MIRBasicBlock, comingFrom: string): ExprExpr => {
                mapBlocks = mapBlocks as Map<string, MIRBasicBlock>;
                const currentFlow = flow.get(block.label) as FlowLink;
                console.assert(block.ops.length > 0);

                switch (currentFlow.succs.size) {
                    case 0: {
                        const lastOp = block.ops[block.ops.length - 1] as MIRVarStore;
                        console.assert(lastOp != undefined);

                        const regName = sanitizeName(lastOp.name.nameID);
                        return this.opsToExpr(block.ops, comingFrom,
                            new ReturnExpr(new VarTerm(regName,
                                returnType)));
                    }
                    case 1: {
                        const successorLabel = currentFlow.succs.values().next().value;
                        return this.opsToExpr(block.ops.slice(1), comingFrom,
                            traverse(mapBlocks.get(successorLabel) as MIRBasicBlock, block.label));
                    }
                    case 2: {
                        const jumpCondOp = block.ops[block.ops.length - 1] as MIRJumpCond;
                        const regName = sanitizeName(jumpCondOp.arg.nameID);
                        const condition = new FuncTerm("op_Equality",
                            [new VarTerm(regName, TranslatorBosqueFStar.boolType), new ConstTerm("true", TranslatorBosqueFStar.boolType)], TranslatorBosqueFStar.boolType);
                        const branchTrue = traverse(mapBlocks.get(jumpCondOp.trueblock) as MIRBasicBlock, block.label);
                        const branchFalse = traverse(mapBlocks.get(jumpCondOp.falseblock) as MIRBasicBlock, block.label);
                        return this.opsToExpr(block.ops.slice(0, -1), comingFrom,
                            new ConditionalExpr(condition, branchTrue, branchFalse));
                    }
                    default: {
                        throw new Error("Wrong Control-Flow graph. The out-degree of any node cannot be more than 2.");
                    }
                }
            }
            declarations.params.map(x => TranslatorBosqueFStar.typesSeen.set(x.name, x.type.trkey));
            const programType = new FuncType(
                declarations.params.map(x => TranslatorBosqueFStar.stringTypeToType(x.type.trkey)),
                returnType);
            // FIX: Needs to be mangled
            TranslatorBosqueFStar.typesSeen.set("_return_", programType.image.getBosqueType());
            if (!this.isFkeyDeclared.has(fkey)) {
                this.stack_declarations.push(
                    new FStarDeclaration(fkey,
                        declarations.params.map(x => x.name),
                        traverse(mapBlocks.get("entry") as MIRBasicBlock, "entry"),
                        programType));
                this.isFkeyDeclared.add(fkey);
            }
            return this.stack_declarations;
        }
    }

    // This method destroys this.stack_declarations
    generateFStarCode(fkey: string) {
        const fd = FS.openSync(this.fileName, 'w');
        this.collectExpr(fkey);
        this.stack_declarations.reverse();
        this.printPrelude(fd);
        TypeExpr.print(fd);
        while (this.stack_declarations.length > 0) {
            (this.stack_declarations.pop() as FStarDeclaration).print(fd);
        }
        TranslatorBosqueFStar.closeFS(fd);
    }
}

export { TranslatorBosqueFStar }