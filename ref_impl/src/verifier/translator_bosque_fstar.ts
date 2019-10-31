//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

// PRIORITIES:
// LoadFieldDefaultValue Not implemented yet
// ConstructorPrimary Not implemented yet
// MIRAccessConstantValue Not implemented yet
// MIRAccessFromField Not implemented yet
// MIRModifyWithFields Not implemented yetcat
// MIRAccessFromIndex Not implemented yet
// MIRIsTypeOfSome Not implemented yet
// LoadConstTypedString Not implemented yet
// ConstructorPrimaryCollectionSingletons Not implemented yet

import * as FS from "fs";
import { MIRBasicBlock, MIRJumpCond, MIROp, MIROpTag, MIRVarStore, MIRRegisterArgument, MIRReturnAssign, MIRPhi, MIRBinCmp, MIRArgument, MIRBinOp, MIRPrefixOp, MIRBody, MIRConstructorTuple, MIRConstructorRecord, MIRInvokeFixedFunction, MIRIsTypeOfNone, MIRLoadFieldDefaultValue, MIRLoadConstTypedString, MIRLoadConst, MIRConstructorPrimary } from "../compiler/mir_ops";
import { computeBlockLinks, FlowLink } from "../compiler/mir_info";
import { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr } from "./expression_expr";
import { IntType, BoolType, FuncType, TypeExpr, TupleType, TypedStringType, RecordType, UnionType, NoneType, AnyType, SomeType, ConstructorType } from "./type_expr";
import { ConstTerm, VarTerm, FuncTerm, TermExpr } from "./term_expr";
import { sanitizeName } from "./util";
import { MIRInvokeBodyDecl, MIRAssembly, MIRConceptTypeDecl, MIREntityTypeDecl, MIRConstantDecl } from "../compiler/mir_assembly";

type StringTypeMangleNameWithFkey = string;

class FunctionDeclaration {
    readonly declarations: MIRInvokeBodyDecl;
    readonly program: ExprExpr;

    constructor(declarations: MIRInvokeBodyDecl, program: ExprExpr) {
        this.declarations = declarations;
        this.program = program;
    }
    print(fd: number): void {
        const fkey = this.declarations.key;
        const args = this.declarations.params.map(x => x.name);
        const returnType = TranslatorBosqueFStar.stringTypeToType(this.declarations.resultType);
        const type = new FuncType(
            this.declarations.params.map(x => TranslatorBosqueFStar.stringTypeToType(x.type)),
            returnType);
        // TODO: Figure out how to include the following fields:
        // 1) recursive, 2) preconditions, 3) postconditions
        FS.writeSync(fd, `val ${sanitizeName(fkey)} : ${type.getFStarTerm()}\n`);
        FS.writeSync(fd, `let ${sanitizeName(fkey)} ${args.join(" ")} = \n${this.program.toML(1, 1)}\n\n`);
    }
}

// TODO: Incomplete implementation
class ConceptDeclaration {
    readonly declarations: MIRConceptTypeDecl;
    constructor(declarations: MIRConceptTypeDecl) {
        this.declarations = declarations;
    }
    print(fd: number): void {
        // FS.writeSync(fd, `val ${sanitizeName(this.ckey)} : ${this.type.getFStarTerm()}\n`);
        // FS.writeSync(fd, `let ${sanitizeName(this.ckey)} ${this.args.join(" ")} = \n${this.program.toML(1)}\n\n`);
    }
}

class EntityDeclaration {
    readonly declarations: MIREntityTypeDecl;
    constructor(declarations: MIREntityTypeDecl) {
        this.declarations = declarations;
        // this.declarations.tkey is the 'name'
    }
    // TODO: Figure out how to include the following fields:
    // 1) invariants, 2) fields, 3) vcallMap, 4) provides
    print(fd: number): void {
        // FS.writeSync(fd, `val ${sanitizeName(this.ekey)} : ${this.type.getFStarTerm()}\n`);
        // FS.writeSync(fd, `let ${sanitizeName(this.ekey)} ${this.args.join(" ")} = \n${this.program.toML(1)}\n\n`);
    }
}

class TranslatorBosqueFStar {
    static readonly anyType = new AnyType();
    static readonly someType = new SomeType();
    static readonly intType = new IntType();
    static readonly boolType = new BoolType();
    static readonly noneType = new NoneType();
    static readonly stringType = new TypedStringType(TranslatorBosqueFStar.anyType);

    static readonly skipCommand = new VarTerm("_skip", TranslatorBosqueFStar.boolType);
    static readonly DEBUGGING = true;

    // String[MangledNamewithFkey] means that the string
    // takes into consideration the scope where it comes from
    // types_seen : String[MangledNamewithFkey] -> TypeExpr
    static readonly types_seen = new Map<StringTypeMangleNameWithFkey, TypeExpr>();

    readonly mapFuncDeclarations: Map<string, MIRInvokeBodyDecl>;
    readonly mapConceptDeclarations: Map<string, MIRConceptTypeDecl>;
    readonly mapEntityDeclarations: Map<string, MIREntityTypeDecl>;
    readonly mapConstantDeclarations: Map<string, MIRConstantDecl>;
    readonly isFkeyDeclared: Set<string> = new Set<string>();
    readonly isCkeyDeclared: Set<string> = new Set<string>();
    readonly isEkeyDeclared: Set<string> = new Set<string>();
    readonly function_declarations = [] as FunctionDeclaration[];
    readonly concept_declarations = [] as ConceptDeclaration[];
    readonly entity_declarations = [] as EntityDeclaration[];

    readonly fileName: string;

    constructor(masm: MIRAssembly, fileName: string) {
        this.mapFuncDeclarations = masm.invokeDecls;
        this.mapConceptDeclarations = masm.conceptDecls;
        this.mapEntityDeclarations = masm.entityDecls;
        this.mapConstantDeclarations = masm.constantDecls;

        // masm.primitiveInvokeDecls contains all the functions

        // used in the Bosque File from the Core and Collection library
        // FIX: This is wrong, but temporarily useful
        masm.primitiveInvokeDecls.forEach((_, index) => {
            this.mapFuncDeclarations.set(index, (this.mapFuncDeclarations.get("NSMain::id") as MIRInvokeBodyDecl))
        });

        this.fileName = fileName;
    }

    printPrelude(fd: number): void {
        FS.writeSync(fd, `module ${this.fileName.slice(0, -4)}\n`);
        // TODO: Change to the appropriate Prelude
        FS.writeSync(fd, `open Sequence\n`);
        FS.writeSync(fd, `open BosqueTypes\n`);
        FS.writeSync(fd, `open BosqueTerms\n`);
    }

    static closeFS(fd: number): void {
        FS.closeSync(fd);
    }

    static debugging(message: string, flag: boolean): void {
        if (flag) {
            console.log(message);
        }
    }

    static optionalTupleSugaring(isOpen: boolean, nonOptionals: string, optionals: string[]): UnionType {
        const setOfTypes = new Set<TypeExpr>();
        setOfTypes.add(new TupleType(false, nonOptionals.split(", ").map(TranslatorBosqueFStar.stringTypeToType)));
        let accum = nonOptionals;
        const secondLastIndex = optionals.length - 2;
        for (let index = 0; index < secondLastIndex; ++index) {
            accum += ", " + optionals[index];
            setOfTypes.add(new TupleType(false, accum.split(", ").map(TranslatorBosqueFStar.stringTypeToType)));
        }
        accum += ", " + optionals[secondLastIndex + 1];
        setOfTypes.add(new TupleType(isOpen, accum.split(", ").map(TranslatorBosqueFStar.stringTypeToType)));
        return new UnionType(setOfTypes);
    }

    // TODO: Add more types as needed
    // String[Type] means that the string is a type which 
    // description comes from a Type expression
    // stringTypeToType : String[Type] -> TypeExpr
    static stringTypeToType(s: string): TypeExpr {
        switch (s) {
            case "NSCore::Any": {
                return TranslatorBosqueFStar.anyType;
            }
            case "NSCore::Some": {
                return TranslatorBosqueFStar.someType;
            }
            case "NSCore::Int": {
                return TranslatorBosqueFStar.intType;
            }
            case "NSCore::Bool": {
                return TranslatorBosqueFStar.boolType;
            }
            case "NSCore::None": {
                return TranslatorBosqueFStar.noneType;
            }
            default: {
                if (s.charAt(0) == '[') {
                    s = s.slice(1, -1);
                    if (s.includes("...")) {
                        s = s.slice(0, -5); // Getting rid of the ellipsis and comma
                        if (s.includes("?:")) {
                            // This is based on the assumption that 
                            // concrete types cannot follow optional types
                            // inside tuples
                            const types = s.split("?:");
                            const nonOptionals = types[0].slice(0, -2); // Getting rid of a comma
                            const optionals = types.slice(1);
                            return TranslatorBosqueFStar.optionalTupleSugaring(true, nonOptionals,
                                optionals.map(x => x.includes(",") ? x.slice(0, -2) : x));
                        }
                        else {
                            return new TupleType(true,
                                s.split(", ").map(TranslatorBosqueFStar.stringTypeToType));
                        }
                    }
                    else {
                        if (s.includes("?:")) {
                            // This is based on the assumption that 
                            // concrete types cannot follow optional types
                            // inside tuples
                            const types = s.split("?:");
                            const nonOptionals = types[0].slice(0, -2); // Getting rid of a comma
                            const optionals = types.slice(1);
                            return TranslatorBosqueFStar.optionalTupleSugaring(false, nonOptionals,
                                optionals.map(x => x.includes(",") ? x.slice(0, -2) : x));
                        }
                        else {
                            return new TupleType(false,
                                s.split(", ").map(TranslatorBosqueFStar.stringTypeToType));
                        }
                    }
                }
                else {
                    if (s.charAt(0) == '{') {
                        // FIX: Implement record type
                        return TranslatorBosqueFStar.noneType;
                    }
                    else {
                        if (s.includes("|")) {
                            return new UnionType(new Set(s
                                .split(" | ")
                                .map(TranslatorBosqueFStar.stringTypeToType)
                            ));
                        }
                        else {
                            if (s.includes("NSCore::String")) {
                                const index = s.indexOf("=");
                                s = s.substr(index + 1, s.length - index - 2);
                                return new TypedStringType(TranslatorBosqueFStar.stringTypeToType(s));
                            }
                            // FIX: This is wrong, but temporarily useful
                            return TranslatorBosqueFStar.noneType;
                            console.log(s + " is constant value type, yet");
                            throw new Error(s + " is constant value type, yet");
                        }
                    }
                }
            }
        }
    }

    // TODO: Add more types as needed
    // String[ValueType] means that the string is a type which
    // description comes from a Value expression
    // stringConstToType : String[ValueType] -> TypeExpr
    static stringConstToType(s: string): TypeExpr {
        let stringConst = s.slice(1);
        stringConst = stringConst.substr(0, stringConst.indexOf("="));
        switch (stringConst) {
            case "none": {
                return TranslatorBosqueFStar.noneType;
            }
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
                // // FIX: This is wrong, but temporarily useful
                // return TranslatorBosqueFStar.noneType;
                throw new Error("The case " + stringConst + " is not implemented yet");
            }
        }
    }

    static argumentToExpr(arg: MIRArgument, fkey: string, ty: TypeExpr | undefined): TermExpr {
        // This branch handles variables
        if (arg instanceof MIRRegisterArgument) {
            if (ty instanceof TypeExpr) {
                TranslatorBosqueFStar.types_seen.set(sanitizeName(arg.nameID + fkey), ty);
                return new VarTerm(sanitizeName(arg.nameID), ty);
            }
            else {
                return new VarTerm(sanitizeName(arg.nameID),
                    (TranslatorBosqueFStar.types_seen.get(sanitizeName(arg.nameID + fkey)) as TypeExpr));
            }
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
            return (TranslatorBosqueFStar.types_seen.get(sanitizeName(arg.nameID + fkey)) as TypeExpr);
        }
        // This branch handles constants
        else {
            return TranslatorBosqueFStar.stringConstToType(arg.nameID);
        }
    }

    opToAssignment(op: MIROp, comingFrom: string, fkey: string): [VarTerm, TermExpr] {
        switch (op.tag) {
            case MIROpTag.MIRLoadConst: {
                const opMIRLoadConst = op as MIRLoadConst;
                opMIRLoadConst;
                TranslatorBosqueFStar.debugging("LoadConst Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_LoadConst", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRLoadConstTypedString: {
                const opMIRLoadConstTypedString = op as MIRLoadConstTypedString;
                console.log(opMIRLoadConstTypedString);
                // console.log("The following provides the _location_ of the entity used");
                // console.log(opMIRLoadConstTypedString.tkey);
                // console.log("The following provides the _type_ of the Typed String declared");
                // console.log(opMIRLoadConstTypedString.tskey);
                return [
                    TranslatorBosqueFStar.argumentToExpr(opMIRLoadConstTypedString.trgt, opMIRLoadConstTypedString.tkey, TranslatorBosqueFStar.intType),
                    new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            // case MIROpTag.AccessConstField:
            case MIROpTag.MIRLoadFieldDefaultValue: { // IMPLEMENT:
                const opMIRLoadFieldDefaultValue = op as MIRLoadFieldDefaultValue;
                console.log(opMIRLoadFieldDefaultValue);
                // CONTINUE2:

                // return [TranslatorBosqueFStar.argumentToExpr(opMIRLoadFieldDefaultValue.trgt, fkey, 
                //     TranslatorBosqueFStar.typeArgumentToType(opReturnAssign.src, fkey)),
                // TranslatorBosqueFStar.argumentToExpr(opReturnAssign.src, fkey, undefined)];

                TranslatorBosqueFStar.debugging("LoadFieldDefaultValue Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_LoadFieldDefaultValue", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            // case MIROpTag.AccessCapturedVariable: { // IMPLEMENT:
            //     TranslatorBosqueFStar.debugging("AcessCapturedVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_AccessCapturedVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            // }
            case MIROpTag.MIRAccessArgVariable: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("AccessArgVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_AccessArgVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRAccessLocalVariable: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("AcessLocalVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_AcessLocalVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRConstructorPrimary: { // IMPLEMENT:
                const opConstructorPrimary = op as MIRConstructorPrimary;
                const current_tkey = opConstructorPrimary.tkey
                const current_entity_decl = this.mapEntityDeclarations.get(current_tkey) as MIREntityTypeDecl;
                const resultPairTypeArray = current_entity_decl.fields.map(x => [x.name,
                    TranslatorBosqueFStar.stringTypeToType(x.declaredType)]) as [string, TypeExpr][];
                const argsExpr = opConstructorPrimary.args.map(x => TranslatorBosqueFStar.argumentToExpr(x, fkey, undefined));
                if (!this.isEkeyDeclared.has(current_tkey)) {
                    this.isEkeyDeclared.add(current_tkey);
                    this.entity_declarations.push(new EntityDeclaration(current_entity_decl));
                }

                console.log(opConstructorPrimary.args); 
                console.log("Reee");
                console.log(current_entity_decl.name);
                console.log(resultPairTypeArray); // TODO: Keep working here

                return [
                    TranslatorBosqueFStar.argumentToExpr(opConstructorPrimary.trgt, fkey,
                        new ConstructorType(current_tkey, resultPairTypeArray)),

                    new FuncTerm("B" + sanitizeName(current_tkey), argsExpr, new ConstructorType(current_tkey, resultPairTypeArray))
                ];
            }
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionEmpty Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionEmpty", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionSingletons Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionSingletons", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionCopies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionCopies", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionMixed Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionMixed", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRConstructorTuple: {
                const opConstructorTuple = op as MIRConstructorTuple;
                const types = opConstructorTuple.args.map(x => TranslatorBosqueFStar.typeArgumentToType(x, fkey));
                return [TranslatorBosqueFStar.argumentToExpr(opConstructorTuple.trgt, fkey, new TupleType(false, types)),
                new FuncTerm("Mktuple__" + opConstructorTuple.args.length,
                    opConstructorTuple.args.map(x => TranslatorBosqueFStar.argumentToExpr(x, fkey, undefined)),
                    new TupleType(false, types))];
            }
            case MIROpTag.MIRConstructorRecord: {
                const opConstructorRecord = op as MIRConstructorRecord;
                const elements = opConstructorRecord.args.map(x => [x[0], TranslatorBosqueFStar.typeArgumentToType(x[1], fkey)]) as [string, TypeExpr][];
                return [TranslatorBosqueFStar.argumentToExpr(opConstructorRecord.trgt, fkey, new RecordType(elements)),
                new FuncTerm("Mkrecord__" + opConstructorRecord.args.map(x => x[0]).join("_"),
                    opConstructorRecord.args.map(x => TranslatorBosqueFStar.argumentToExpr(x[1], fkey, undefined)),
                    new RecordType(elements))];
            }
            // case MIROpTag.ConstructorLambda: { // IMPLEMENT:
            //     // TranslatorBosqueFStar.debugging("ConstructorLambda Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     // const opConstructorLambda = op as MIRConstructorLambda;
            //     // console.log(opConstructorLambda);
            //     return [new VarTerm("_ConstructorLambda", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            // }

            case MIROpTag.MIRInvokeFixedFunction: {
                const opCallNamespaceFunction = op as MIRInvokeFixedFunction;
                const currentFunctionKey = opCallNamespaceFunction.mkey;
                // The following line will keep pushing to 
                // the stack_expressions stack
                this.collectExpr(currentFunctionKey);
                const resultType = TranslatorBosqueFStar.stringTypeToType((this.mapFuncDeclarations.get(currentFunctionKey) as MIRInvokeBodyDecl).resultType);
                return [TranslatorBosqueFStar.argumentToExpr(opCallNamespaceFunction.trgt, fkey, resultType),
                new FuncTerm(sanitizeName(currentFunctionKey),
                    opCallNamespaceFunction.args.map(x => TranslatorBosqueFStar.argumentToExpr(x, fkey, undefined)),
                    resultType)];
            }
            // case MIROpTag.CallStaticFunction: { // IMPLEMENT:
            //     TranslatorBosqueFStar.debugging("CallStaticFunction Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_CallStaticFunction", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            // }
            case MIROpTag.MIRAccessFromIndex: {
                // const opMIRAccessFromIndex = op as MIRAccessFromIndex;
                // console.log(opMIRAccessFromIndex);
                // const typeOfTuple = TranslatorBosqueFStar.types_seen.get(sanitizeName(opMIRAccessFromIndex.arg.nameID + fkey)) as TypeExpr;
                // if (typeOfTuple instanceof TupleType) {
                //     TranslatorBosqueFStar.types_seen.set(sanitizeName(opMIRAccessFromIndex.trgt.nameID + fkey),
                //         typeOfTuple.elements[opMIRAccessFromIndex.idx]);
                //     return [TranslatorBosqueFStar.argumentToExpr(opMIRAccessFromIndex.trgt, fkey),
                //     new FuncTerm("Mktuple__" + typeOfTuple.elements.length + "?._" + (opMIRAccessFromIndex.idx + 1),
                //         [TranslatorBosqueFStar.argumentToExpr(opMIRAccessFromIndex.arg, fkey)],
                //         typeOfTuple.elements[opMIRAccessFromIndex.idx])];
                // }
                // else {
                //     throw new Error("Type " + typeOfTuple + " is not a TupleType");
                // }
                TranslatorBosqueFStar.debugging("MIRAccessFromIndex Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRAccessFromIndex", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRProjectFromIndecies: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRProjectFromIndecies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromIndecies", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRAccessFromProperty: {
                // const opMIRAccessFromProperty = op as MIRAccessFromProperty;
                // console.log(opMIRAccessFromProperty);
                // const typeOfTuple = TranslatorBosqueFStar.types_seen.get(sanitizeName(opMIRAccessFromProperty.arg.nameID + fkey)) as TypeExpr;
                // if (typeOfTuple instanceof RecordType) {
                //     const keyTypes = new Map(typeOfTuple.elements);
                //     TranslatorBosqueFStar.types_seen.set(sanitizeName(opMIRAccessFromProperty.trgt.nameID + fkey),
                //         (keyTypes.get(opMIRAccessFromProperty.property) as TypeExpr));
                //     return [TranslatorBosqueFStar.argumentToExpr(opMIRAccessFromProperty.trgt, fkey),
                //     new FuncTerm("Mkrecord__" + typeOfTuple.signature + "?." + opMIRAccessFromProperty.property,
                //         [TranslatorBosqueFStar.argumentToExpr(opMIRAccessFromProperty.arg, fkey)],
                //         (keyTypes.get(opMIRAccessFromProperty.property) as TypeExpr))];
                // }
                // else {
                //     throw new Error("Type " + typeOfTuple + " is not a RecordType");
                // }
                TranslatorBosqueFStar.debugging("MIRAccessFromProperty Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRAccessFromProperty", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
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
            // case MIROpTag.MIRInvokeKnownTarget: { // IMPLEMENT:
            //     TranslatorBosqueFStar.debugging("MIRInvokeKnownTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_MIRInvokeKnownTarget", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            // }
            case MIROpTag.MIRInvokeVirtualTarget: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRInvokeVirtualTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRInvokeVirtualTarget", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            // case MIROpTag.MIRCallLambda: { // IMPLEMENT:
            //     TranslatorBosqueFStar.debugging("MIRCallLambda Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_MIRCallLambda", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            // }
            case MIROpTag.MIRPrefixOp: {
                const opPrefixOp = op as MIRPrefixOp;
                return [TranslatorBosqueFStar.argumentToExpr(opPrefixOp.trgt, fkey, TranslatorBosqueFStar.typeArgumentToType(opPrefixOp.arg, fkey)),
                new FuncTerm(TermExpr.unaryOpToFStar.get(opPrefixOp.op) as string,
                    [TranslatorBosqueFStar.argumentToExpr(opPrefixOp.arg, fkey, undefined)],
                    TranslatorBosqueFStar.typeArgumentToType(opPrefixOp.arg, fkey))];
            }
            case MIROpTag.MIRBinOp: {
                const opBinOp = op as MIRBinOp;
                const lhs = TranslatorBosqueFStar.argumentToExpr(opBinOp.lhs, fkey, undefined);
                const rhs = TranslatorBosqueFStar.argumentToExpr(opBinOp.rhs, fkey, undefined);
                return [TranslatorBosqueFStar.argumentToExpr(opBinOp.trgt, fkey, TranslatorBosqueFStar.intType),
                new FuncTerm(TermExpr.binOpToFStar.get(opBinOp.op) as string,
                    [lhs, rhs],
                    TranslatorBosqueFStar.intType)];
                // new FuncTerm("hahah", [], TranslatorBosqueFStar.boolType)
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
                const lhs = TranslatorBosqueFStar.argumentToExpr(opBinCmp.lhs, fkey, undefined);
                const rhs = TranslatorBosqueFStar.argumentToExpr(opBinCmp.rhs, fkey, undefined);
                // Q: Is still necessary check if the type is either
                // an int or a string?
                // A: Yes, because that will tell which `operation code` should be used
                // TODO: Implement the above
                return [TranslatorBosqueFStar.argumentToExpr(opBinCmp.trgt, fkey, TranslatorBosqueFStar.boolType),
                new FuncTerm("extractBool",
                    [new FuncTerm((TermExpr.binOpToFStar.get(opBinCmp.op) as string), [lhs, rhs], TranslatorBosqueFStar.boolType)],
                    TranslatorBosqueFStar.boolType)];
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
                return [TranslatorBosqueFStar.argumentToExpr(opVarStore.name, fkey, TranslatorBosqueFStar.typeArgumentToType(opVarStore.src, fkey)),
                TranslatorBosqueFStar.argumentToExpr(opVarStore.src, fkey, undefined)];
            }
            case MIROpTag.MIRReturnAssign: {
                const opReturnAssign = op as MIRReturnAssign;
                return [TranslatorBosqueFStar.argumentToExpr(opReturnAssign.name, fkey, TranslatorBosqueFStar.typeArgumentToType(opReturnAssign.src, fkey)),
                TranslatorBosqueFStar.argumentToExpr(opReturnAssign.src, fkey, undefined)];
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
                const currentType = TranslatorBosqueFStar.types_seen.get(sanitizeName(opPhi.trgt.nameID + fkey));
                const typeFromSrc = TranslatorBosqueFStar.typeArgumentToType(opPhi.src.get(comingFrom) as MIRRegisterArgument, fkey);
                if (currentType == undefined) {
                    TranslatorBosqueFStar.types_seen.set(sanitizeName(opPhi.trgt.nameID + fkey), typeFromSrc);
                }
                else {
                    if (!currentType.equalTo(typeFromSrc)) {
                        if (currentType instanceof UnionType) {
                            if (typeFromSrc instanceof UnionType) {
                                const previousElementsSet = new Set(Array.from(typeFromSrc.elements));
                                currentType.elements.forEach(x => previousElementsSet.add(x));
                                TranslatorBosqueFStar.types_seen.set(sanitizeName(opPhi.trgt.nameID + fkey),
                                    new UnionType(previousElementsSet));
                            }
                            else {
                                currentType.elements.add(typeFromSrc);
                                TranslatorBosqueFStar.types_seen.set(sanitizeName(opPhi.trgt.nameID + fkey),
                                    new UnionType(currentType.elements));
                            }
                        }
                        else {
                            if (typeFromSrc instanceof UnionType) {
                                const previousElementsSet = new Set(Array.from(typeFromSrc.elements));
                                previousElementsSet.add(currentType);
                                TranslatorBosqueFStar.types_seen.set(sanitizeName(opPhi.trgt.nameID + fkey),
                                    new UnionType(previousElementsSet));
                            }
                            else {
                                TranslatorBosqueFStar.types_seen.set(sanitizeName(opPhi.trgt.nameID + fkey),
                                    new UnionType(new Set<TypeExpr>([typeFromSrc, currentType])));
                            }
                        }
                    }
                }
                return [TranslatorBosqueFStar.argumentToExpr(opPhi.trgt, fkey,
                    undefined),
                TranslatorBosqueFStar.argumentToExpr(opPhi.src.get(comingFrom) as MIRRegisterArgument, fkey, undefined)];
            }
            case MIROpTag.MIRIsTypeOfNone: { // IMPLEMENT:
                const opIsTypeOfNone = op as MIRIsTypeOfNone;
                // console.log(opIsTypeOfNone);
                // FIX: This is not properly implemented, it shouldnt return true all the time ... 
                return [TranslatorBosqueFStar.argumentToExpr(opIsTypeOfNone.trgt, fkey, TranslatorBosqueFStar.boolType),
                new ConstTerm("true", TranslatorBosqueFStar.boolType)];
                // const regName = section + "_" + opIsTypeOfNone.trgt.nameID;
                // stringVariableToStringType.set(regName, "NSCore::Bool");

                // return new EqualityTerm(new VarExpr(regName, new TranslatorBosqueFStar.boolType()),
                //     BoxFormulaExpr(new EqualityTerm(new FuncExpr("HasType", new UninterpretedType("BType"),
                //         [argumentToTermExpr(opIsTypeOfNone.arg, section)]), BNone)));
                // return [new VarTerm("_MIRIsTypeOfNone", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
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
            // PRIORITY:
            case MIROpTag.MIRAccessConstantValue: {
                TranslatorBosqueFStar.debugging("MIRAccessConstantValue Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRAccessConstantValue", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            default:
                console.log(op);
                throw new Error("Operation " + op + " not defined");
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

    collectExpr(fkey: string) {
        const declarations = (this.mapFuncDeclarations.get(fkey) as MIRInvokeBodyDecl);
        const mapBlocks = (declarations.body as MIRBody).body;
        // ---------------------------------------------------------
        // Checking vtypes -----------------------------------------
        // const valueTypes = (declarations.body as MIRBody).vtypes;
        // console.log(`Inside ${fkey}`);
        // console.log(valueTypes);
        // console.log("\n");
        // ---------------------------------------------------------
        if (typeof (mapBlocks) === "string") {
            throw new Error("The program with fkey " + fkey + " is just a string");
        }
        else {
            declarations.params.map(x =>
                TranslatorBosqueFStar.types_seen.set(sanitizeName(x.name + fkey),
                    TranslatorBosqueFStar.stringTypeToType(x.type)));
            const returnType = TranslatorBosqueFStar.stringTypeToType(declarations.resultType);
            const flow = computeBlockLinks(mapBlocks);

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
                        throw new Error("Wrong Control-Flow graph. The out-degree of any node cannot be more than 2 in block: " + block);
                    }
                }
            }

            if (!this.isFkeyDeclared.has(fkey)) {
                this.isFkeyDeclared.add(fkey);
                this.function_declarations.push(
                    new FunctionDeclaration(declarations,
                        traverse(mapBlocks.get("entry") as MIRBasicBlock, "entry")));
            }
        }
    }

    generateFStarCode(fkey: string) {
        this.collectExpr(fkey);

        const fd = FS.openSync("fstar_files/" + this.fileName, 'w');

        // Check Concepts and Entities before emmiting Prelude
        this.printPrelude(fd);
        FS.writeSync(fd, "\n");

        FS.writeSync(fd, "(* Type names *)\n");
        TypeExpr.declareTypeNames(fd);
        FS.writeSync(fd, "\n");

        FS.writeSync(fd, "(* Concept Declarations *)\n");
        // TODO: Implement
        FS.writeSync(fd, "\n");

        FS.writeSync(fd, "(* Entity Declarations *)\n");
        // TODO: Implement
        FS.writeSync(fd, "\n");

        FS.writeSync(fd, "(* Constant Declarations *)\n");
        this.mapConstantDeclarations.forEach(constant_decl => {
            // Constant declaration generally have only two blocks: entry and exit
            // We just `declare` the entry block
            constant_decl.value.body.forEach(basicBlock => {
                if (basicBlock.label == "entry") {
                    const returnType = TranslatorBosqueFStar.stringTypeToType(constant_decl.declaredType);
                    const continuation = () => new ReturnExpr(new VarTerm("__ir_ret__", returnType));
                    TranslatorBosqueFStar.types_seen.set(sanitizeName(constant_decl.cname), returnType);
                    FS.writeSync(fd, `let ${sanitizeName(constant_decl.cname)} = \n${this.opsToExpr(basicBlock.ops, "entry", "", continuation).toML(1, 0)}\n`);
                }
            });
        });
        FS.writeSync(fd, "\n");

        FS.writeSync(fd, "(* Function Declarations *)\n");
        this.function_declarations.map(x => x.print(fd));

        TranslatorBosqueFStar.closeFS(fd);
    }
}

export { TranslatorBosqueFStar }