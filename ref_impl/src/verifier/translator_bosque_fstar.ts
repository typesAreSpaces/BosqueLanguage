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
import { MIRBasicBlock, MIRJumpCond, MIROp, MIROpTag, MIRVarStore, MIRRegisterArgument, MIRReturnAssign, MIRPhi, MIRBinCmp, MIRArgument, MIRBinOp, MIRPrefixOp, MIRBody, MIRConstructorTuple, MIRConstructorRecord, MIRInvokeFixedFunction, MIRIsTypeOfNone, MIRLoadFieldDefaultValue, MIRLoadConstTypedString, MIRLoadConst, MIRConstructorPrimary, MIRIsTypeOfSome, MIRVariable, MIRAccessFromIndex } from "../compiler/mir_ops";
import { computeBlockLinks, FlowLink } from "../compiler/mir_info";
import { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr } from "./expression_expr";
import { IntType, BoolType, FuncType, TypeExpr, TupleType, TypedStringType, RecordType, UnionType, NoneType, AnyType, SomeType, ConstructorType } from "./type_expr";
import { ConstTerm, VarTerm, FuncTerm, TermExpr, TupleTerm, TupleProjExpr } from "./term_expr";
import { sanitizeName } from "./util";
import { MIRInvokeBodyDecl, MIRAssembly, MIRConceptTypeDecl, MIREntityTypeDecl, MIRConstantDecl } from "../compiler/mir_assembly";

type StringTypeMangleNameWithFkey = string;

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
    readonly types_seen: Map<StringTypeMangleNameWithFkey, TypeExpr>;

    readonly mapFuncDeclarations: Map<string, MIRInvokeBodyDecl>;
    static mapConceptDeclarations: Map<string, MIRConceptTypeDecl>;
    static mapEntityDeclarations: Map<string, MIREntityTypeDecl>;
    readonly mapConstantDeclarations: Map<string, MIRConstantDecl>;

    static conceptsUsed: Set<string>;
    static entitiesUsed: Set<string>;

    readonly isFkeyDeclared: Set<string> = new Set<string>();
    readonly isCkeyDeclared: Set<string> = new Set<string>();
    readonly isEkeyDeclared: Set<string> = new Set<string>();
    readonly function_declarations = [] as FunctionDeclaration[];
    readonly concept_declarations = [] as ConceptDeclaration[];
    readonly entity_declarations = [] as EntityDeclaration[];

    readonly fileName: string;

    constructor(masm: MIRAssembly, fileName: string) {
        this.types_seen = new Map<StringTypeMangleNameWithFkey, TypeExpr>();
        this.mapFuncDeclarations = masm.invokeDecls;
        TranslatorBosqueFStar.mapConceptDeclarations = masm.conceptDecls;
        TranslatorBosqueFStar.mapEntityDeclarations = masm.entityDecls;
        this.mapConstantDeclarations = masm.constantDecls;

        TranslatorBosqueFStar.conceptsUsed = new Set<string>();
        TranslatorBosqueFStar.entitiesUsed = new Set<string>();

        TranslatorBosqueFStar.mapConceptDeclarations.forEach((_, index) => {
            if (!index.includes("NSCore"))
                TranslatorBosqueFStar.conceptsUsed.add(index);
        });
        TranslatorBosqueFStar.mapEntityDeclarations.forEach((_, index) => {
            if (!index.includes("NSCore"))
                TranslatorBosqueFStar.entitiesUsed.add(index);
        });

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
        FS.writeSync(fd, `open Util\n`);
    }

    static debugging(message: string, flag: boolean): void {
        if (flag) {
            console.log(message);
        }
    }

    static optionalTupleSugaring(isOpen: boolean, nonOptionals: string, optionals: string[]): UnionType {
        const set_of_types = new Set<TypeExpr>();
        set_of_types.add(new TupleType(false, nonOptionals.split(", ").map(TranslatorBosqueFStar.stringVarToTypeExpr)));
        let accum = nonOptionals;
        const secondLastIndex = optionals.length - 2;
        for (let index = 0; index < secondLastIndex; ++index) {
            accum += ", " + optionals[index];
            set_of_types.add(new TupleType(false, accum.split(", ").map(TranslatorBosqueFStar.stringVarToTypeExpr)));
        }
        accum += ", " + optionals[secondLastIndex + 1];
        set_of_types.add(new TupleType(isOpen, accum.split(", ").map(TranslatorBosqueFStar.stringVarToTypeExpr)));
        return new UnionType(set_of_types);;
    }

    // TODO: Add more types as needed
    // String[Type] means that the string is a type which 
    // description comes from a Type expression
    // stringVarToTypeExpr : String[Type] -> TypeExpr
    static stringVarToTypeExpr(s: string): TypeExpr {

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
                // Concept and Entities 
                if (TranslatorBosqueFStar.conceptsUsed.has(s)) {
                    const description = TranslatorBosqueFStar.mapConceptDeclarations.get(s) as MIREntityTypeDecl;
                    return new ConstructorType(sanitizeName(description.tkey),
                        description.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]) as [string, TypeExpr][]);
                }

                if (TranslatorBosqueFStar.entitiesUsed.has(s)) {
                    const description = TranslatorBosqueFStar.mapEntityDeclarations.get(s) as MIREntityTypeDecl;
                    return new ConstructorType(sanitizeName(description.tkey),
                        description.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]) as [string, TypeExpr][]);
                }

                // Tuple
                if (s.charAt(0) == '[') {
                    s = s.slice(1, -1);
                    let isOpen = false;
                    // Open Tuple check
                    if (s.includes("...")) {
                        s = s.slice(0, -5); // Getting rid of the ellipsis and comma
                        isOpen = true;
                    }
                    if (s.includes("?:")) {
                        // This is based on the assumption that 
                        // concrete types cannot follow optional types
                        // inside tuples
                        const types = s.split("?:");
                        const nonOptionals = types[0].slice(0, -2); // Getting rid of a comma
                        const optionals = types.slice(1);
                        return TranslatorBosqueFStar.optionalTupleSugaring(isOpen, nonOptionals, optionals.map(x => x.includes(",") ? x.slice(0, -2) : x));
                    }
                    else {
                        return new TupleType(isOpen, s.split(", ").map(TranslatorBosqueFStar.stringVarToTypeExpr));
                    }
                }
                // Record
                if (s.charAt(0) == '{') {
                    // FIX: Implement record type
                    return TranslatorBosqueFStar.noneType;
                }
                // Union
                if (s.includes("|")) {
                    return new UnionType(new Set(s
                        .split(" | ")
                        .map(TranslatorBosqueFStar.stringVarToTypeExpr)
                    ));
                }
                // String 
                if (s.includes("NSCore::String")) {
                    const index = s.indexOf("=");
                    // This branch handles untyped strings
                    if (index == -1) {
                        return new TypedStringType(TranslatorBosqueFStar.anyType);
                    }
                    // This branch handles typed strings
                    else {
                        s = s.substr(index + 1, s.length - index - 2);
                        return new TypedStringType(TranslatorBosqueFStar.stringVarToTypeExpr(s));
                    }

                }
                // FIX: This is wrong, but temporarily useful
                console.log(`------ ERROR: Unknown typed ${s} found while executing stringVarToTypeExpr ------`);
                return TranslatorBosqueFStar.noneType;
            }
        }
    }

    // TODO: Add more types as needed
    // String[ValueType] means that the string is a type which
    // description comes from a Value expression
    // stringConstToTypeExpr : String[ValueType] -> TypeExpr
    static stringConstToTypeExpr(s: string): TypeExpr {

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

    // This function is designed given a MIRArgument, returns a TermExpr.
    // -) If the MIRArgument is a 'variable'
    // --) If the MIRArgument 'hasn't been recorded before', then the user
    // is supposed to use this method providing a TypeExpr, and the method
    // will add this MIRArgument to the types_seen collection.
    // --) If the MIIArgument 'has been recorded before', then the user
    // is supposed to pass undefined in ty, and the method will give back a
    // TermExpr by looking up the collection types_seen
    // -) If the MIRArgument is a 'constant', we rely on the stringify method
    // to make it work
    // The fkey string helps to keep track the function where the variable came 
    // from
    MIRArgumentToTermExpr(arg: MIRArgument, fkey: string, ty: TypeExpr | undefined): TermExpr {
        
        // This branch handles variables
        if (arg instanceof MIRRegisterArgument) {
            if (ty instanceof TypeExpr) {
                this.types_seen.set(sanitizeName(arg.nameID + fkey), ty);
                return new VarTerm(sanitizeName(arg.nameID), ty);
            }
            else {
                return new VarTerm(sanitizeName(arg.nameID), this.types_seen.get(sanitizeName(arg.nameID + fkey)) as TypeExpr);
            }
        }
        // This branch handles constants
        else {
            return new ConstTerm(arg.stringify(), TranslatorBosqueFStar.stringConstToTypeExpr(arg.nameID));
        }
    }

    // MIRArgumentToTypeExpr : MIRArgument -> TypeExpr
    MIRArgumentToTypeExpr(arg: MIRArgument, fkey: string): TypeExpr {
        // This branch handles variables
        
        if (arg instanceof MIRRegisterArgument) {
            return (this.types_seen.get(sanitizeName(arg.nameID + fkey)) as TypeExpr);
        }
        // This branch handles constants
        else {
            return TranslatorBosqueFStar.stringConstToTypeExpr(arg.nameID);
        }
    }

    opToAssignment(op: MIROp, comingFrom: string, fkey: string): [VarTerm, TermExpr] | [VarTerm, TermExpr][] {
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
                    this.MIRArgumentToTermExpr(opMIRLoadConstTypedString.trgt, opMIRLoadConstTypedString.tkey, TranslatorBosqueFStar.intType),
                    // This is WRONG
                    new ConstTerm("0", TranslatorBosqueFStar.intType)
                ];
            }
            // case MIROpTag.AccessConstField:
            case MIROpTag.MIRLoadFieldDefaultValue: { // IMPLEMENT:
                const opMIRLoadFieldDefaultValue = op as MIRLoadFieldDefaultValue;
                console.log(opMIRLoadFieldDefaultValue);

                // return [this.MIRArgumentToTermExpr(opMIRLoadFieldDefaultValue.trgt, fkey, 
                //     this.MIRArgumentToTypeExpr(opReturnAssign.src, fkey)),
                // this.MIRArgumentToTermExpr(opReturnAssign.src, fkey, undefined)];

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
            case MIROpTag.MIRConstructorPrimary: {
                const opConstructorPrimary = op as MIRConstructorPrimary;
                const current_tkey = opConstructorPrimary.tkey
                const current_entity_decl = TranslatorBosqueFStar.mapEntityDeclarations.get(current_tkey) as MIREntityTypeDecl;
                const field_types = current_entity_decl.fields.map(x => [x.name,
                TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]) as [string, TypeExpr][];
                const assignments = opConstructorPrimary.args.map((x, index) => [this.MIRArgumentToTermExpr(new MIRVariable(opConstructorPrimary.trgt.nameID + "_arg_" + index), fkey, this.MIRArgumentToTypeExpr(x, fkey))
                    , this.MIRArgumentToTermExpr(x, fkey, undefined)]) as [VarTerm, TermExpr][];

                if (!this.isEkeyDeclared.has(current_tkey)) {
                    this.isEkeyDeclared.add(current_tkey);
                    this.entity_declarations.push(new EntityDeclaration(current_entity_decl));
                }

                assignments.unshift([
                    this.MIRArgumentToTermExpr(opConstructorPrimary.trgt, fkey, new ConstructorType(current_tkey, field_types)),
                    new FuncTerm("B" + sanitizeName(current_tkey), assignments.map(x => x[0]), new ConstructorType(current_tkey, field_types))
                ]);
                return assignments;
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
                const types = opConstructorTuple.args.map(x => this.MIRArgumentToTypeExpr(x, fkey));
                return [this.MIRArgumentToTermExpr(opConstructorTuple.trgt, fkey, new TupleType(false, types)),
                new TupleTerm(opConstructorTuple.args.map(x => this.MIRArgumentToTermExpr(x, fkey, undefined)))];
            }
            case MIROpTag.MIRConstructorRecord: {
                const opConstructorRecord = op as MIRConstructorRecord;
                const elements = opConstructorRecord.args.map(x => [x[0], this.MIRArgumentToTypeExpr(x[1], fkey)]) as [string, TypeExpr][];
                // FIX: This is wrong
                return [this.MIRArgumentToTermExpr(opConstructorRecord.trgt, fkey, new RecordType(elements)),
                new FuncTerm("Mkrecord__" + opConstructorRecord.args.map(x => x[0]).join("_"),
                    opConstructorRecord.args.map(x => this.MIRArgumentToTermExpr(x[1], fkey, undefined)),
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
                const resultType = TranslatorBosqueFStar.stringVarToTypeExpr((this.mapFuncDeclarations.get(currentFunctionKey) as MIRInvokeBodyDecl).resultType);

                return [this.MIRArgumentToTermExpr(opCallNamespaceFunction.trgt, fkey, resultType),
                new FuncTerm(sanitizeName(currentFunctionKey),
                    opCallNamespaceFunction.args.map(x => this.MIRArgumentToTermExpr(x, fkey, undefined)),
                    resultType)];
            }
            // case MIROpTag.CallStaticFunction: { // IMPLEMENT:
            //     TranslatorBosqueFStar.debugging("CallStaticFunction Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_CallStaticFunction", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            // }
            case MIROpTag.MIRAccessFromIndex: {
                const opMIRAccessFromIndex = op as MIRAccessFromIndex;
                const dimension = (this.MIRArgumentToTypeExpr(opMIRAccessFromIndex.arg, fkey) as TupleType).elements.length;

                return [
                    this.MIRArgumentToTermExpr(opMIRAccessFromIndex.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opMIRAccessFromIndex.resultAccessType)),
                    new TupleProjExpr(opMIRAccessFromIndex.idx, dimension,
                        this.MIRArgumentToTermExpr(opMIRAccessFromIndex.arg, fkey, undefined),
                        TranslatorBosqueFStar.stringVarToTypeExpr(opMIRAccessFromIndex.resultAccessType))
                ];
                //new FuncTerm("nthTuple", [opMIRAccessFromIndex.idx, this.MIRArgumentToTermExpr(opMIRAccessFromIndex.arg)], TranslatorBosqueFStar.intType)
            }
            case MIROpTag.MIRProjectFromIndecies: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRProjectFromIndecies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromIndecies", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            }
            case MIROpTag.MIRAccessFromProperty: {
                // const opMIRAccessFromProperty = op as MIRAccessFromProperty;
                // console.log(opMIRAccessFromProperty);
                // const typeOfTuple = this.types_seen.get(sanitizeName(opMIRAccessFromProperty.arg.nameID + fkey)) as TypeExpr;
                // if (typeOfTuple instanceof RecordType) {
                //     const keyTypes = new Map(typeOfTuple.elements);
                //     this.types_seen.set(sanitizeName(opMIRAccessFromProperty.trgt.nameID + fkey),
                //         (keyTypes.get(opMIRAccessFromProperty.property) as TypeExpr));
                //     return [this.MIRArgumentToTermExpr(opMIRAccessFromProperty.trgt, fkey),
                //     new FuncTerm("Mkrecord__" + typeOfTuple.signature + "?." + opMIRAccessFromProperty.property,
                //         [this.MIRArgumentToTermExpr(opMIRAccessFromProperty.arg, fkey)],
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
                return [this.MIRArgumentToTermExpr(opPrefixOp.trgt, fkey, this.MIRArgumentToTypeExpr(opPrefixOp.arg, fkey)),
                new FuncTerm(TermExpr.unaryOpToFStar.get(opPrefixOp.op) as string,
                    [this.MIRArgumentToTermExpr(opPrefixOp.arg, fkey, undefined)],
                    this.MIRArgumentToTypeExpr(opPrefixOp.arg, fkey))];
            }
            case MIROpTag.MIRBinOp: {
                const opBinOp = op as MIRBinOp;
                const lhs = this.MIRArgumentToTermExpr(opBinOp.lhs, fkey, undefined);
                const rhs = this.MIRArgumentToTermExpr(opBinOp.rhs, fkey, undefined);
                return [this.MIRArgumentToTermExpr(opBinOp.trgt, fkey, TranslatorBosqueFStar.intType),
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
                const lhs = this.MIRArgumentToTermExpr(opBinCmp.lhs, fkey, undefined);
                const rhs = this.MIRArgumentToTermExpr(opBinCmp.rhs, fkey, undefined);
                // Q: Is still necessary check if the type is either
                // an int or a string?
                // A: Yes, because that will tell which `operation code` should be used
                // TODO: Implement the above
                return [this.MIRArgumentToTermExpr(opBinCmp.trgt, fkey, TranslatorBosqueFStar.boolType),
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
                return [this.MIRArgumentToTermExpr(opVarStore.name, fkey, this.MIRArgumentToTypeExpr(opVarStore.src, fkey)),
                this.MIRArgumentToTermExpr(opVarStore.src, fkey, undefined)];
            }
            case MIROpTag.MIRReturnAssign: {
                const opReturnAssign = op as MIRReturnAssign;
                return [this.MIRArgumentToTermExpr(opReturnAssign.name, fkey, this.MIRArgumentToTypeExpr(opReturnAssign.src, fkey)),
                this.MIRArgumentToTermExpr(opReturnAssign.src, fkey, undefined)];
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
                const currentType = this.types_seen.get(sanitizeName(opPhi.trgt.nameID + fkey));
                const typeFromSrc = this.MIRArgumentToTypeExpr(opPhi.src.get(comingFrom) as MIRRegisterArgument, fkey);
                if (currentType == undefined) {
                    this.types_seen.set(sanitizeName(opPhi.trgt.nameID + fkey), typeFromSrc);
                }
                else {
                    if (!currentType.equalTo(typeFromSrc)) {
                        if (currentType instanceof UnionType) {
                            if (typeFromSrc instanceof UnionType) {
                                const previousElementsSet = new Set(Array.from(typeFromSrc.elements));
                                currentType.elements.forEach(x => previousElementsSet.add(x));
                                this.types_seen.set(sanitizeName(opPhi.trgt.nameID + fkey),
                                    new UnionType(previousElementsSet));
                            }
                            else {
                                currentType.elements.add(typeFromSrc);
                                this.types_seen.set(sanitizeName(opPhi.trgt.nameID + fkey),
                                    new UnionType(currentType.elements));
                            }
                        }
                        else {
                            if (typeFromSrc instanceof UnionType) {
                                const previousElementsSet = new Set(Array.from(typeFromSrc.elements));
                                previousElementsSet.add(currentType);
                                this.types_seen.set(sanitizeName(opPhi.trgt.nameID + fkey),
                                    new UnionType(previousElementsSet));
                            }
                            else {
                                this.types_seen.set(sanitizeName(opPhi.trgt.nameID + fkey),
                                    new UnionType(new Set<TypeExpr>([typeFromSrc, currentType])));
                            }
                        }
                    }
                }
                return [this.MIRArgumentToTermExpr(opPhi.trgt, fkey,
                    undefined),
                this.MIRArgumentToTermExpr(opPhi.src.get(comingFrom) as MIRRegisterArgument, fkey, undefined)];
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const opIsTypeOfNone = op as MIRIsTypeOfNone;
                return [this.MIRArgumentToTermExpr(opIsTypeOfNone.trgt, fkey, TranslatorBosqueFStar.boolType),
                new FuncTerm("isNone",
                    [this.MIRArgumentToTermExpr(opIsTypeOfNone.arg, fkey, undefined)],
                    TranslatorBosqueFStar.boolType)];
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const opIsTypeOfSome = op as MIRIsTypeOfSome;
                return [this.MIRArgumentToTermExpr(opIsTypeOfSome.trgt, fkey, TranslatorBosqueFStar.boolType),
                new FuncTerm("isSome",
                    [this.MIRArgumentToTermExpr(opIsTypeOfSome.arg, fkey, undefined)],
                    TranslatorBosqueFStar.boolType)];
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
            const result = this.opToAssignment(ops[0], comingFrom, fkey);
            if (result[0] instanceof VarTerm) {
                const [lval, rval] = result as [VarTerm, TermExpr];
                if (lval.symbolName == "_skip") {
                    return this.opsToExpr(ops.slice(1), comingFrom, fkey, program);
                }
                else {
                    return new AssignmentExpr(lval, rval, this.opsToExpr(ops.slice(1), comingFrom, fkey, program));
                }
            }
            else {
                return (result as [VarTerm, TermExpr][]).reduce((rest_expression, current_assignment) => {
                    return new AssignmentExpr(current_assignment[0], current_assignment[1], rest_expression)
                }, this.opsToExpr(ops.slice(1), comingFrom, fkey, program));
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
                this.types_seen.set(sanitizeName(x.name + fkey),
                    TranslatorBosqueFStar.stringVarToTypeExpr(x.type)));
            const returnType = TranslatorBosqueFStar.stringVarToTypeExpr(declarations.resultType);
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
                        const condition = new VarTerm(regName, TranslatorBosqueFStar.boolType);
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

        const fd = FS.openSync("fstar_files/" + this.fileName, 'w');

        // Check Concepts and Entities before emmiting Prelude

        this.collectExpr(fkey);

        this.printPrelude(fd);
        FS.writeSync(fd, "\n");

        FS.writeSync(fd, "(* Type names *)\n");
        TypeExpr.declareTypeNames(fd);
        FS.writeSync(fd, "\n");

        // TODO: Concept Declarations needs testing
        FS.writeSync(fd, "(* Concept Declarations *)\n");
        TranslatorBosqueFStar.conceptsUsed.forEach(x => {
            const entry = TranslatorBosqueFStar.mapConceptDeclarations.get(x) as MIRConceptTypeDecl;
            const entityName = sanitizeName(entry.tkey);
            const fieldArrows = entry.fields.map ( y => {
                const type = TranslatorBosqueFStar.stringVarToTypeExpr(y.declaredType).getFStarTypeName();
                return y.name + " : " + ((y.declaredType.includes("NSCore")) ? ("bosqueTerm{" + type + " = (getType " + y.name + ")" + "}") : type ) + " -> \n" ;
            }).join("");
            FS.writeSync(fd, "type " + entityName + " = \n| B" + sanitizeName(entry.tkey) + " : " + fieldArrows + entityName + "\n");
        });
        FS.writeSync(fd, "\n");

        FS.writeSync(fd, "(* Entity Declarations *)\n");
        TranslatorBosqueFStar.entitiesUsed.forEach(x => {
            const entry = TranslatorBosqueFStar.mapEntityDeclarations.get(x) as MIREntityTypeDecl;
            const entityName = sanitizeName(entry.tkey);
            const fieldArrows = entry.fields.map ( y => {
                const type = TranslatorBosqueFStar.stringVarToTypeExpr(y.declaredType).getFStarTypeName();
                return y.name + " : " + ((y.declaredType.includes("NSCore")) ? ("bosqueTerm{" + type + " = (getType " + y.name + ")" + "}") : type ) + " -> \n" ;
            }).join("");
            FS.writeSync(fd, "type " + entityName + " = \n| B" + sanitizeName(entry.tkey) + " : " + fieldArrows + entityName + "\n");
        });
        FS.writeSync(fd, "\n");

        FS.writeSync(fd, "(* Constant Declarations *)\n");
        this.mapConstantDeclarations.forEach(constant_decl => {
            // Constant declaration generally have only two blocks: entry and exit
            // We just `declare` the entry block
            constant_decl.value.body.forEach(basicBlock => {
                if (basicBlock.label == "entry") {
                    const returnType = TranslatorBosqueFStar.stringVarToTypeExpr(constant_decl.declaredType);
                    const continuation = () => new ReturnExpr(new VarTerm("__ir_ret__", returnType));
                    this.types_seen.set(sanitizeName(constant_decl.cname), returnType);
                    FS.writeSync(fd, `let ${sanitizeName(constant_decl.cname)} = \n${this.opsToExpr(basicBlock.ops, "entry", "", continuation).toML(1, 0)}\n`);
                }
            });
        });
        FS.writeSync(fd, "\n");

        FS.writeSync(fd, "(* Function Declarations *)\n");
        this.function_declarations.map(x => x.print(fd));

        FS.closeSync(fd);
    }
}

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
        const type = new FuncType(
            this.declarations.params.map(x => TranslatorBosqueFStar.stringVarToTypeExpr(x.type)),
            TranslatorBosqueFStar.stringVarToTypeExpr(this.declarations.resultType));
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

export { TranslatorBosqueFStar }
