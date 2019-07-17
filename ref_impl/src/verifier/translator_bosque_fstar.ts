//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import { MIRBasicBlock, MIRJumpCond, MIROp, MIROpTag, MIRVarStore, MIRRegisterArgument, MIRReturnAssign, MIRPhi, MIRBinCmp, MIRArgument, MIRBinOp, MIRPrefixOp, MIRCallNamespaceFunction, MIRBody, MIRConstructorTuple, MIRAccessFromIndex, MIRConstructorRecord, MIRAccessFromProperty } from "../compiler/mir_ops";
import { computeBlockLinks, FlowLink } from "../compiler/mir_info";
import { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr } from "./expression_expr";
import { IntType, BoolType, FuncType, TypeExpr, TupleType, StringType, RecordType } from "./type_expr";
import { ConstTerm, VarTerm, FuncTerm, TermExpr } from "./term_expr";
import { sanitizeName } from "./util";
import { MIRFunctionDecl } from "../compiler/mir_assembly";

type StringTypeMangleNameWithFkey = string;

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
    static readonly stringType = new StringType();
    static readonly skipCommand = new VarTerm("_skip", TranslatorBosqueFStar.boolType);
    static readonly DEBUGGING = false;
    // typesSeen : String[MangledNamewithFkey] -> TypeExpr
    static readonly typesSeen = new Map<StringTypeMangleNameWithFkey, TypeExpr>();

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
    // stringTypeToType : String[Type] -> TypeExpr
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
                else {
                    throw new Error(`${s} is not a valid constant value type, yet`);
                }
            }
        }
    }

    // TODO: Add more types as needed
    // stringConstToType : String[ValueType] -> TypeExpr
    static stringConstToType(s: string): TypeExpr {
        let stringConst = s.slice(1);
        stringConst = stringConst.substr(0, stringConst.indexOf("="));
        switch (stringConst) {
            case "int": {
                return TranslatorBosqueFStar.intType;
            }
            case "true": {
                return TranslatorBosqueFStar.boolType;
            }
            case "false": {
                return TranslatorBosqueFStar.boolType;
            }
            case "string": {
                return TranslatorBosqueFStar.stringType;
            }
            default: {
                throw new Error(`The case ${stringConst} is not implemented yet`);
            }
        }
    }

    static argumentToExpr(arg: MIRArgument, fkey: string): TermExpr {
        // This branch handles variables
        if (arg instanceof MIRRegisterArgument) {
            return new VarTerm(sanitizeName(arg.nameID),
                (TranslatorBosqueFStar.typesSeen.get(sanitizeName(arg.nameID + fkey)) as TypeExpr));
        }
        // This branch handles constants
        else {
            return new ConstTerm(arg.stringify(),
                TranslatorBosqueFStar.stringConstToType(arg.nameID));
        }
    }

    // typeArgumentToType : MIRArgument -> TypeExpr
    static typeArgumentToType(arg: MIRArgument, fkey: string): TypeExpr {
        // This branch handles variables
        if (arg instanceof MIRRegisterArgument) {
            return (TranslatorBosqueFStar.typesSeen.get(sanitizeName(arg.nameID + fkey)) as TypeExpr);
        }
        // This branch handles constants
        else {
            return TranslatorBosqueFStar.stringConstToType(arg.nameID);
        }
    }

    // -- Common pattern: 
    // typesSeen -> set -> (sanitize -> trgt.name + fkey, a Type)
    // return [argumentToExpr (trgt, fkey), argumentToExpr (src, fkey)]
    // -- Example:
    // TranslatorBosqueFStar.typesSeen.set(sanitizeName(opPhi.trgt.nameID + fkey), TranslatorBosqueFStar.intType);        
    // return [TranslatorBosqueFStar.argumentToExpr(opPhi.trgt, fkey), TranslatorBosqueFStar.argumentToExpr(opPhi.src.get(comingFrom) as MIRRegisterArgument, fkey)];
    opToAssignment(op: MIROp, comingFrom: string, fkey: string): [VarTerm, TermExpr] {
        switch (op.tag) {
            case MIROpTag.LoadConst:
            case MIROpTag.LoadConstTypedString:
            case MIROpTag.AccessNamespaceConstant:
            case MIROpTag.AccessConstField:
            case MIROpTag.LoadFieldDefaultValue: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("LoadFieldDefaultValue Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_LoadFieldDefaultValue", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.AccessCapturedVariable: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("AcessCapturedVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_AccessCapturedVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.AccessArgVariable: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("AccessArgVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_AccessArgVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.AccessLocalVariable: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("AcessLocalVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_AcessLocalVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorPrimary: { // IMPLEMENT:
                // const opConstructorPrimary = op as MIRConstructorPrimary;
                TranslatorBosqueFStar.debugging("ConstructorPrimary Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimary", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorPrimaryCollectionEmpty: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionEmpty Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionEmpty", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorPrimaryCollectionSingletons: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionSingletons Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionSingletons", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorPrimaryCollectionCopies: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionCopies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionCopies", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorPrimaryCollectionMixed: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionMixed Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionMixed", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.ConstructorTuple: {
                const opConstructorTuple = op as MIRConstructorTuple;
                const types = opConstructorTuple.args.map(x => TranslatorBosqueFStar.typeArgumentToType(x, fkey));
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opConstructorTuple.trgt.nameID + fkey),
                    new TupleType(types));
                return [TranslatorBosqueFStar.argumentToExpr(opConstructorTuple.trgt, fkey),
                new FuncTerm("Mktuple__" + opConstructorTuple.args.length,
                    opConstructorTuple.args.map(x => TranslatorBosqueFStar.argumentToExpr(x, fkey)),
                    new TupleType(types))];
            }
            case MIROpTag.ConstructorRecord: { 
                const opConstructorRecord = op as MIRConstructorRecord;
                const elements = opConstructorRecord.args.map(x => [x[0], TranslatorBosqueFStar.typeArgumentToType(x[1], fkey)]) as [string, TypeExpr][];
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opConstructorRecord.trgt.nameID + fkey),
                    new RecordType(elements));
                return [TranslatorBosqueFStar.argumentToExpr(opConstructorRecord.trgt, fkey),
                new FuncTerm("Mkrecord__" + opConstructorRecord.args.map(x => x[0]).join("_"),
                    opConstructorRecord.args.map(x => TranslatorBosqueFStar.argumentToExpr(x[1], fkey)),
                    new RecordType(elements))];
            }
            case MIROpTag.ConstructorLambda: { // IMPLEMENT:
                // TranslatorBosqueFStar.debugging("ConstructorLambda Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                // const opConstructorLambda = op as MIRConstructorLambda;
                // console.log(opConstructorLambda);
                return [new VarTerm("_ConstructorLambda", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.CallNamespaceFunction: {
                const opCallNamespaceFunction = op as MIRCallNamespaceFunction;
                const currentFunctionKey = opCallNamespaceFunction.fkey;
                // The following line will keep pushing to 
                // the stack_expressions stack
                this.collectExpr(currentFunctionKey);
                const resultType = TranslatorBosqueFStar.stringTypeToType((this.mapDeclarations.get(currentFunctionKey) as MIRFunctionDecl).invoke.resultType.trkey);
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opCallNamespaceFunction.trgt.nameID + fkey),
                    resultType);
                return [TranslatorBosqueFStar.argumentToExpr(opCallNamespaceFunction.trgt, fkey),
                new FuncTerm(sanitizeName(currentFunctionKey),
                    opCallNamespaceFunction.args.map(x => TranslatorBosqueFStar.argumentToExpr(x, fkey)),
                    resultType)];
            }
            case MIROpTag.CallStaticFunction: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("CallStaticFunction Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_CallStaticFunction", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRAccessFromIndex: {
                const opMIRAccessFromIndex = op as MIRAccessFromIndex;
                const typeOfTuple = TranslatorBosqueFStar.typesSeen.get(sanitizeName(opMIRAccessFromIndex.arg.nameID + fkey)) as TypeExpr;
                if (typeOfTuple instanceof TupleType) {
                    TranslatorBosqueFStar.typesSeen.set(sanitizeName(opMIRAccessFromIndex.trgt.nameID + fkey),
                        typeOfTuple.elements[opMIRAccessFromIndex.idx]);
                    return [TranslatorBosqueFStar.argumentToExpr(opMIRAccessFromIndex.trgt, fkey),
                    new FuncTerm("Mktuple__" + typeOfTuple.elements.length + "?._" + (opMIRAccessFromIndex.idx + 1),
                        [TranslatorBosqueFStar.argumentToExpr(opMIRAccessFromIndex.arg, fkey)],
                        typeOfTuple.elements[opMIRAccessFromIndex.idx])];
                }
                else {
                    throw new Error(`Type ${typeOfTuple} is not a TupleType`);
                }
            }
            case MIROpTag.MIRProjectFromIndecies: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRProjectFromIndecies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromIndecies", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRAccessFromProperty: {
                const opMIRAccessFromProperty = op as MIRAccessFromProperty;
                const typeOfTuple = TranslatorBosqueFStar.typesSeen.get(sanitizeName(opMIRAccessFromProperty.arg.nameID + fkey)) as TypeExpr;
                if (typeOfTuple instanceof RecordType) {
                    const keyTypes = new Map(typeOfTuple.elements);
                    TranslatorBosqueFStar.typesSeen.set(sanitizeName(opMIRAccessFromProperty.trgt.nameID + fkey),
                        (keyTypes.get(opMIRAccessFromProperty.property) as TypeExpr));
                    return [TranslatorBosqueFStar.argumentToExpr(opMIRAccessFromProperty.trgt, fkey),
                    new FuncTerm("Mkrecord__" + typeOfTuple.signature + "?." + opMIRAccessFromProperty.property,
                        [TranslatorBosqueFStar.argumentToExpr(opMIRAccessFromProperty.arg, fkey)],
                        (keyTypes.get(opMIRAccessFromProperty.property) as TypeExpr))];
                }
                else {
                    throw new Error(`Type ${typeOfTuple} is not a RecordType`);
                }
            }
            case MIROpTag.MIRProjectFromProperties: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRProjectFromProperties Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromProperties", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRAccessFromField: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRAccessFromField Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRAccessFromField", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRProjectFromFields: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRProjectFromFields Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromFields", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRProjectFromTypeTuple: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeTuple Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromTypeTuple", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRProjectFromTypeRecord: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeRecord Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromTypeRecord", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRProjectFromTypeConcept: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeConcept Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromTypeConcept", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRModifyWithIndecies: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRModifyWithIndecies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRModifyWithIndecies", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRModifyWithProperties: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRModifyWithProperties Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRModifyWithProperties", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRModifyWithFields: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRModifyWithFields Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRModifyWithFields", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRStructuredExtendTuple: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRStructuredExtendedTuple Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRStructuredExtendTuple", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRStructuredExtendRecord: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRStructuredExtendRecord Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRStructuredExtendRecord", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRStructuredExtendObject: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRStructuredExtendObject Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRStructuredExtendObject", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRInvokeKnownTarget: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRInvokeKnownTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRInvokeKnownTarget", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRInvokeVirtualTarget: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRInvokeVirtualTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRInvokeVirtualTarget", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRCallLambda: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRCallLambda Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRCallLambda", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRPrefixOp: {
                const opPrefixOp = op as MIRPrefixOp;
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opPrefixOp.trgt.nameID + fkey),
                    TranslatorBosqueFStar.typeArgumentToType(opPrefixOp.arg, fkey));
                return [TranslatorBosqueFStar.argumentToExpr(opPrefixOp.trgt, fkey),
                new FuncTerm(TermExpr.unaryOpToFStar.get(opPrefixOp.op) as string,
                    [TranslatorBosqueFStar.argumentToExpr(opPrefixOp.arg, fkey)],
                    TranslatorBosqueFStar.typeArgumentToType(opPrefixOp.arg, fkey))];
            }
            case MIROpTag.MIRBinOp: {
                const opBinOp = op as MIRBinOp;
                const lhs = TranslatorBosqueFStar.argumentToExpr(opBinOp.lhs, fkey);
                const rhs = TranslatorBosqueFStar.argumentToExpr(opBinOp.rhs, fkey);
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opBinOp.trgt.nameID + fkey),
                    TranslatorBosqueFStar.intType);
                return [TranslatorBosqueFStar.argumentToExpr(opBinOp.trgt, fkey),
                new FuncTerm(TermExpr.binOpToFStar.get(opBinOp.op) as string,
                    [lhs, rhs],
                    TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRBinEq: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRBinEq Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRBinEq", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRBinCmp: { 
                // The predicate returned is of type Bool
                // because the operations to arrive at this
                // point are <, <=, >, >= only
                const opBinCmp = op as MIRBinCmp;
                const lhs = TranslatorBosqueFStar.argumentToExpr(opBinCmp.lhs, fkey);
                const rhs = TranslatorBosqueFStar.argumentToExpr(opBinCmp.rhs, fkey);
                // TODO: Is still necessary check if the type is either
                // an int or a string?
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opBinCmp.trgt.nameID + fkey),
                    TranslatorBosqueFStar.boolType);
                return [TranslatorBosqueFStar.argumentToExpr(opBinCmp.trgt, fkey),
                new FuncTerm((TermExpr.binOpToFStar.get(opBinCmp.op) as string), [lhs, rhs], TranslatorBosqueFStar.boolType)];
            }
            case MIROpTag.MIRRegAssign: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRRegAssign Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRRegAssign", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRTruthyConvert: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRTruthyConvert Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRTruthyConvert", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRVarStore: {
                const opVarStore = op as MIRVarStore;
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opVarStore.name.nameID + fkey),
                    TranslatorBosqueFStar.typeArgumentToType(opVarStore.src, fkey));
                return [TranslatorBosqueFStar.argumentToExpr(opVarStore.name, fkey), TranslatorBosqueFStar.argumentToExpr(opVarStore.src, fkey)];
            }
            case MIROpTag.MIRReturnAssign: {
                const opReturnAssign = op as MIRReturnAssign;
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opReturnAssign.name.nameID + fkey),
                    TranslatorBosqueFStar.typeArgumentToType(opReturnAssign.src, fkey));
                return [TranslatorBosqueFStar.argumentToExpr(opReturnAssign.name, fkey), TranslatorBosqueFStar.argumentToExpr(opReturnAssign.src, fkey)];
            }
            case MIROpTag.MIRAbort: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRAbort Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRAbort", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRDebug: { // IMPLEMENT:
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
                TranslatorBosqueFStar.typesSeen.set(sanitizeName(opPhi.trgt.nameID + fkey),
                    TranslatorBosqueFStar.intType); // I mean, this one
                return [TranslatorBosqueFStar.argumentToExpr(opPhi.trgt, fkey), TranslatorBosqueFStar.argumentToExpr(opPhi.src.get(comingFrom) as MIRRegisterArgument, fkey)];
            }
            case MIROpTag.MIRIsTypeOfNone: { // IMPLEMENT:
                // const opIsTypeOfNone = op as MIRIsTypeOfNone;

                // const regName = section + "_" + opIsTypeOfNone.trgt.nameID;
                // stringVariableToStringType.set(regName, "NSCore::Bool");

                // return new EqualityTerm(new VarExpr(regName, new TranslatorBosqueFStar.boolType()),
                //     BoxFormulaExpr(new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"),
                //         [argumentToTermExpr(opIsTypeOfNone.arg, section)]), BNone)));
                return [new VarTerm("_MIRIsTypeOfNone", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRIsTypeOfSome: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRIsTypeOfSome Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                // const opIsTypeOfSome = op as MIRIsTypeOfSome;
                // console.log(opIsTypeOfSome);
                return [new VarTerm("_MIRIsTypeOfSome", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRIsTypeOf: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRIsTypeOf Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRIsTypeOf", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            default:
                TranslatorBosqueFStar.debugging("This might be a problem", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_default_problem", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
        }
    }

    opsToExpr(ops: MIROp[], comingFrom: string, fkey: string, program: () => ExprExpr): ExprExpr {
        if (ops.length == 0) {
            return program();
        }
        else {
            const [lval, rval] = this.opToAssignment(ops[0], comingFrom, fkey);
            if (lval.symbolName == "_skip") {
                return this.opsToExpr(ops.slice(1), comingFrom, fkey, program);
            }
            else {
                return new AssignmentExpr(lval, rval, this.opsToExpr(ops.slice(1), comingFrom, fkey, program));
            }
        }
    }

    collectExpr(fkey: string): FStarDeclaration[] {
        const declarations = (this.mapDeclarations.get(fkey) as MIRFunctionDecl).invoke;
        const mapBlocks = (declarations.body as MIRBody).body;
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
                const currentFlow = flow.get(block.label) as FlowLink;
                console.assert(block.ops.length > 0);

                switch (currentFlow.succs.size) {
                    case 0: {
                        const lastOp = block.ops[block.ops.length - 1] as MIRVarStore;
                        console.assert(lastOp != undefined);
                        const regName = sanitizeName(lastOp.name.nameID);
                        const continuation = () => new ReturnExpr(new VarTerm(regName, returnType));
                        return this.opsToExpr(block.ops, comingFrom, fkey, continuation);
                    }
                    case 1: {
                        const successorLabel = currentFlow.succs.values().next().value;
                        const continuation = () => traverse((mapBlocks as Map<string, MIRBasicBlock>).get(successorLabel) as MIRBasicBlock, block.label);
                        return this.opsToExpr(block.ops.slice(0, -1), comingFrom, fkey, continuation);
                    }
                    case 2: {
                        const jumpCondOp = block.ops[block.ops.length - 1] as MIRJumpCond;
                        const regName = sanitizeName(jumpCondOp.arg.nameID);
                        const condition = new FuncTerm("op_Equality",
                            [new VarTerm(regName, TranslatorBosqueFStar.boolType), new ConstTerm("true", TranslatorBosqueFStar.boolType)], TranslatorBosqueFStar.boolType);
                        const branchTrue = traverse(mapBlocks.get(jumpCondOp.trueblock) as MIRBasicBlock, block.label);
                        const branchFalse = traverse(mapBlocks.get(jumpCondOp.falseblock) as MIRBasicBlock, block.label);
                        const continuation = () => new ConditionalExpr(condition, branchTrue, branchFalse);
                        return this.opsToExpr(block.ops.slice(0, -1), comingFrom, fkey, continuation);
                    }
                    default: {
                        throw new Error(`Wrong Control-Flow graph. The out-degree of any node cannot be more than 2 in block: ${block}`);
                    }
                }
            }
            declarations.params.map(x => TranslatorBosqueFStar.typesSeen.set(sanitizeName(x.name + fkey), TranslatorBosqueFStar.stringTypeToType(x.type.trkey)));
            const programType = new FuncType(
                declarations.params.map(x => TranslatorBosqueFStar.stringTypeToType(x.type.trkey)),
                returnType);
            if (!this.isFkeyDeclared.has(fkey)) {
                this.stack_declarations.push(
                    new FStarDeclaration(fkey,
                        declarations.params.map(x => x.name),
                        traverse(mapBlocks.get("entry") as MIRBasicBlock, "entry"),
                        programType));
                this.isFkeyDeclared.add(fkey);
            }
            console.log(TranslatorBosqueFStar.typesSeen);
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