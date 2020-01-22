//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

// PRIORITIES:
// LoadFieldDefaultValue Not implemented yet
// MIRAccessConstantValue Not implemented yet
// MIRAccessFromField Not implemented yet
// MIRModifyWithFields Not implemented yetcat
// MIRIsTypeOfSome Not implemented yet
// ConstructorPrimaryCollectionSingletons Not implemented yet

import * as FS from "fs";
import {
    MIRBasicBlock, MIRJumpCond, MIROp, MIROpTag, MIRVarStore, MIRRegisterArgument, MIRReturnAssign, MIRPhi, MIRBinCmp, MIRArgument,
    MIRBinOp, MIRPrefixOp, MIRBody, MIRConstructorTuple, MIRConstructorRecord, MIRInvokeFixedFunction, MIRIsTypeOfNone, MIRLoadFieldDefaultValue,
    MIRLoadConstTypedString, MIRLoadConst, MIRConstructorPrimary, MIRIsTypeOfSome, MIRVariable, MIRAccessFromIndex, MIRProjectFromIndecies,
    MIRAccessFromProperty,
    MIRProjectFromProperties,
    MIRProjectFromTypeConcept,
    MIRModifyWithFields,
    MIRAccessFromField,
    MIRProjectFromFields,
    MIRConstructorPrimaryCollectionSingletons
} from "../compiler/mir_ops";
import { computeBlockLinks, FlowLink } from "../compiler/mir_info";
import { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr } from "./expression_expr";
import {
    IntType, BoolType, FuncType, TypeExpr, TupleType, TypedStringType, RecordType, UnionType, NoneType, AnyType, SomeType,
    ConstructorType, ParsableType, GUIDType, TruthyType, ObjectType
} from "./type_expr";
import { ConstTerm, VarTerm, FuncTerm, TermExpr, TupleTerm, TupleProjExpr, RecordTerm, RecordProjExpr } from "./term_expr";
import { sanitizeName, topologicalOrder } from "./util";
import { MIRInvokeBodyDecl, MIRAssembly, MIRConceptTypeDecl, MIREntityTypeDecl, MIRConstantDecl } from "../compiler/mir_assembly";
import { printBosqueTypesFST } from "./bosqueTypesFST";
import { printBosqueTermsFST } from "./bosqueTermsFST";

type StringTypeMangleNameWithFkey = string;

class TranslatorBosqueFStar {
    static readonly anyType = new AnyType();
    static readonly someType = new SomeType();
    static readonly truthyType = new TruthyType();
    static readonly noneType = new NoneType();
    static readonly parsableType = new ParsableType();
    static readonly boolType = new BoolType();
    static readonly intType = new IntType();
    static readonly guidType = new GUIDType();
    static readonly objectType = new ObjectType();
    static readonly stringType = new TypedStringType(TranslatorBosqueFStar.anyType);
    static readonly skipCommand = new VarTerm("_skip", TranslatorBosqueFStar.boolType, "_global");
    static readonly DEBUGGING = true;

    static fresh_count = 0;

    // String[MangledNamewithFkey] means that the string
    // takes into consideration the scope where it comes from
    // types_seen : String[MangledNamewithFkey] -> TypeExpr
    readonly types_seen: Map<StringTypeMangleNameWithFkey, TypeExpr>;

    readonly mapFuncDeclarations: Map<string, MIRInvokeBodyDecl>;
    static mapConceptDeclarations: Map<string, MIRConceptTypeDecl>;
    static mapEntityDeclarations: Map<string, MIREntityTypeDecl>;
    readonly mapConstantDeclarations: Map<string, MIRConstantDecl>;

    readonly isFkeyDeclared: Set<string> = new Set<string>();
    readonly function_declarations = [] as FunctionDeclaration[];

    readonly fileName: string;
    readonly fstar_files_directory: string;

    constructor(masm: MIRAssembly, fileName: string, fstar_files_directory: string) {
        this.types_seen = new Map<StringTypeMangleNameWithFkey, TypeExpr>();

        this.mapFuncDeclarations = masm.invokeDecls;
        TranslatorBosqueFStar.mapConceptDeclarations = masm.conceptDecls;
        TranslatorBosqueFStar.mapEntityDeclarations = masm.entityDecls;
        this.mapConstantDeclarations = masm.constantDecls;

        // ---------------------------------------------------------------------------------------------------------
        // masm.primitiveInvokeDecls contains all the functions
        // used in the Bosque File from the Core and Collection library

        // FIX: This is wrong, because these function should have
        // its actual FStar implementation. It's useful because
        // momentarily these functions have 'valid definitions'.
        masm.primitiveInvokeDecls.forEach((_, index) => {
            this.mapFuncDeclarations.set(index, (this.mapFuncDeclarations.get("NSMain::id") as MIRInvokeBodyDecl))
        });
        // ---------------------------------------------------------------------------------------------------------

        this.fileName = fileName;
        this.fstar_files_directory = fstar_files_directory;
    }

    extractProvidesRelation(declarations: Map<string, MIREntityTypeDecl | MIRConceptTypeDecl>): Map<string, Set<string>> {
        const nodesNeighbors = new Map<string, Set<string>>();

        declarations.forEach((value, index) => {
            if (!index.includes("NSCore")) {
                if (nodesNeighbors.get(index) == undefined) {
                    nodesNeighbors.set(index, new Set<string>());
                }

                value.provides.map(x => {
                    if (nodesNeighbors.get(x) == undefined) {
                        nodesNeighbors.set(x, new Set<string>());
                    }
                    (nodesNeighbors.get(x) as Set<string>).add(index)
                });
            }
        });
        return nodesNeighbors;
    }

    serializeTypes(declarations: Map<string, MIREntityTypeDecl | MIRConceptTypeDecl>): Set<string> {
        const nodesNeighbors = this.extractProvidesRelation(declarations);
        return new Set(topologicalOrder(nodesNeighbors));
    }

    static debugging(message: string, flag: boolean): void {
        if (flag) {
            console.log(message);
        }
    }

    static optionalTupleSugaring(nonOptionals: TypeExpr[], optionals: TypeExpr[]): UnionType {
        const set_of_types = new Set<TypeExpr>();
        // set_of_types.add(new TupleType(false, nonOptionals));

        const num_optionals = optionals.length;
        for (let index = 0; index < num_optionals; ++index) {
            // Copy nonOptionals
            let temp: TypeExpr[] = [];
            for (let i = 0; i < nonOptionals.length; ++i) {
                temp.push(nonOptionals[i]);
            }
            // Copy optionals
            for (let i = 0; i < index; ++i) {
                temp.push(optionals[i]);
            }
            set_of_types.add(new TupleType(false, temp));
        }

        return new UnionType(set_of_types);
    }

    static optionalRecordSugaring(nonOptionalProperties: string[], nonOptionalTypes: TypeExpr[], optionalProperties: string[], optionalTypes: TypeExpr[]): UnionType {
        const set_of_types = new Set<TypeExpr>();

        const total = Math.pow(2, optionalProperties.length);
        for (let i = 0; i < total; i++) {

            let tempSetProperties: string[] = [];
            let tempSetTypes: TypeExpr[] = [];

            // Copy nonOptionals
            for (let i = 0; i < nonOptionalProperties.length; ++i) {
                tempSetProperties.push(nonOptionalProperties[i]);
                tempSetTypes.push(nonOptionalTypes[i])
            }

            let num = i.toString(2);
            while (num.length < optionalProperties.length) {
                num = '0' + num;
            }
            for (let b = 0; b < num.length; b++) {
                if (num[b] === '1') {
                    // Copy optionals
                    tempSetProperties.push(optionalProperties[b]);
                    tempSetTypes.push(optionalTypes[b]);
                }
            }
            const entriesTemp = tempSetProperties.map((value, index) => [value, tempSetTypes[index]]) as [string, TypeExpr][];
            entriesTemp.sort((x, y) => x[0].localeCompare(y[0]))
            set_of_types.add(new RecordType(false, entriesTemp.map(x => x[0]), entriesTemp.map(x => x[1])));
        }

        return new UnionType(set_of_types);
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
            case "NSCore::Truthy": {
                return TranslatorBosqueFStar.truthyType;
            }
            case "NSCore::None": {
                return TranslatorBosqueFStar.noneType;
            }
            case "NSCore::Parsable": {
                return TranslatorBosqueFStar.parsableType;
            }
            case "NSCore::Bool": {
                return TranslatorBosqueFStar.boolType;
            }
            case "NSCore::Int": {
                return TranslatorBosqueFStar.intType;
            }
            case "NSCore::GUID": {
                return TranslatorBosqueFStar.guidType;
            }
            case "NSCore::Object": {
                return TranslatorBosqueFStar.objectType;
            }
            default: {
                // Concept
                if (TranslatorBosqueFStar.mapConceptDeclarations.has(s) && !s.includes("NSCore")) {
                    const description = TranslatorBosqueFStar.mapConceptDeclarations.get(s) as MIRConceptTypeDecl;
                    return new ConstructorType(description.tkey,
                        description.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]) as [string, TypeExpr][]);
                }
                // Entities
                if (TranslatorBosqueFStar.mapEntityDeclarations.has(s) && !s.includes("NSCore")) {
                    const description = TranslatorBosqueFStar.mapEntityDeclarations.get(s) as MIREntityTypeDecl;
                    return new ConstructorType(description.tkey,
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
                        const nonOptionals = types[0];
                        const optionals = types.slice(1);
                        if (nonOptionals.length == 0) {
                            return this.optionalTupleSugaring([],
                                optionals.map(x => x.includes(",") ? x.slice(0, -2) : x).map(TranslatorBosqueFStar.stringVarToTypeExpr));
                        }
                        else {
                            return this.optionalTupleSugaring(nonOptionals.slice(0, -2).split(", ").map(TranslatorBosqueFStar.stringVarToTypeExpr),
                                optionals.map(x => x.includes(",") ? x.slice(0, -2) : x).map(TranslatorBosqueFStar.stringVarToTypeExpr));
                        }
                    }
                    else {
                        return new TupleType(isOpen, s.split(", ").map(TranslatorBosqueFStar.stringVarToTypeExpr));
                    }
                }
                // Record
                if (s.charAt(0) == '{') {
                    s = s.slice(1, -1);
                    let isOpen = false;
                    // Open Record check
                    if (s.includes("...")) {
                        s = s.slice(0, -5); // Getting rid of the ellipsis and comma
                        isOpen = true;
                    }
                    const entries = s.split(", ");
                    if (s.includes("?:")) {
                        // This is based on the assumption that 
                        // concrete types cannot follow optional types
                        // inside tuples

                        const nonOptionalEntries = entries.filter(x => !x.includes("?:"));
                        const optionalEntries = entries.filter(x => x.includes("?:"));
                        const nonOptional_field_names = nonOptionalEntries.map(x => x.substring(0, x.indexOf(":")));
                        const optional_field_names = optionalEntries.map(x => x.substring(0, x.indexOf("?:")));
                        const nonOptional_types = nonOptionalEntries.map(x => x.substring(x.indexOf(":") + 1)).map(TranslatorBosqueFStar.stringVarToTypeExpr);
                        const optional_types = optionalEntries.map(x => x.substring(x.indexOf("?:") + 2)).map(TranslatorBosqueFStar.stringVarToTypeExpr);

                        return this.optionalRecordSugaring(nonOptional_field_names, nonOptional_types, optional_field_names, optional_types);
                    }
                    else {
                        const field_names = entries.map(x => x.substring(0, x.indexOf(":")));
                        const types = entries.map(x => x.substring(x.indexOf(":") + 1)).map(TranslatorBosqueFStar.stringVarToTypeExpr);
                        return new RecordType(isOpen, field_names, types);
                    }
                }
                // Union
                if (s.includes("|")) {
                    return new UnionType(new Set(s
                        .split(" | ")
                        .map(TranslatorBosqueFStar.stringVarToTypeExpr)
                    ));
                }
                // Typed String 
                if (s.includes("NSCore::String")) {
                    const index = s.indexOf("=");
                    // This branch handles untyped strings
                    if (index == -1) {
                        return TranslatorBosqueFStar.stringType;
                    }
                    // This branch handles typed strings
                    else {
                        s = s.substr(index + 1, s.length - index - 2);
                        return new TypedStringType(TranslatorBosqueFStar.stringVarToTypeExpr(s));
                    }

                }
                console.log(`------ ERROR: Unknown typed ${s} found while executing stringVarToTypeExpr ------`);
                throw new Error("------ ERROR: Unknown typed found while executing stringVarToTypeExpr ------");
            }
        }
    }

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
                console.log("The case " + stringConst + " is not implemented yet");
                throw new Error("The case " + stringConst + " is not implemented yet");
            }
        }
    }

    // Given a MIRArgument, this function returns a TermExpr.
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
    MIRArgumentToTermExpr(arg: MIRArgument | string, fkey: string, ty: TypeExpr | undefined): TermExpr {
        // This branch handles string names
        // These encode fresh names
        if (typeof arg === "string") {
            const m_ty = ty as TypeExpr;
            this.types_seen.set(sanitizeName(arg + fkey), m_ty);
            return new VarTerm(sanitizeName(arg + fkey), m_ty, fkey);
        }
        // This branch handles variables
        if (arg instanceof MIRRegisterArgument) {
            if (ty instanceof TypeExpr) {
                this.types_seen.set(sanitizeName(arg.nameID + fkey), ty);
                return new VarTerm(sanitizeName(arg.nameID), ty, fkey);
            }
            else {
                return new VarTerm(sanitizeName(arg.nameID), this.types_seen.get(sanitizeName(arg.nameID + fkey)) as TypeExpr, fkey);
            }
        }
        // This branch handles constants
        else {
            return new ConstTerm(arg.stringify(), TranslatorBosqueFStar.stringConstToTypeExpr(arg.nameID), fkey);
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
                const opLoadConst = op as MIRLoadConst;
                console.log(opLoadConst);
                const second_equal_sign_position = opLoadConst.src.nameID.indexOf("=", 1);
                const name_length = opLoadConst.src.nameID.length;
                const value_type = opLoadConst.src.nameID.slice(1, second_equal_sign_position - name_length);
                let value: string;
                if (value_type == "int" || value_type == "string") {
                    value = opLoadConst.src.nameID.slice(second_equal_sign_position + 1);
                }
                else {
                    value = value_type;
                }
                return [this.MIRArgumentToTermExpr(opLoadConst.trgt, fkey, TranslatorBosqueFStar.stringConstToTypeExpr(opLoadConst.src.nameID)),
                new ConstTerm(value, TranslatorBosqueFStar.stringConstToTypeExpr(opLoadConst.src.nameID), fkey)];
            }
            case MIROpTag.MIRLoadConstTypedString: {
                const opMIRLoadConstTypedString = op as MIRLoadConstTypedString;
                const current_tkey = opMIRLoadConstTypedString.tkey;
                const partial_decl = TranslatorBosqueFStar.mapEntityDeclarations.get(current_tkey);
                let current_type: ConstructorType;

                if (partial_decl == undefined) {
                    const actual_decl = TranslatorBosqueFStar.mapConceptDeclarations.get(current_tkey) as MIRConceptTypeDecl;
                    current_type = new ConstructorType(actual_decl.tkey,
                        actual_decl.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]) as [string, TypeExpr][]);
                }
                else {
                    current_type = new ConstructorType(partial_decl.tkey,
                        partial_decl.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]) as [string, TypeExpr][]);
                }

                return [
                    this.MIRArgumentToTermExpr(opMIRLoadConstTypedString.trgt, fkey, new TypedStringType(current_type)),
                    new ConstTerm("\"" + opMIRLoadConstTypedString.ivalue.slice(1, -1) + "\"", new TypedStringType(current_type), fkey)
                ];
            }
            // case MIROpTag.AccessConstField:



            // ----------------------------------------------------------------------------------------------------------------------------------------------------
            case MIROpTag.MIRLoadFieldDefaultValue: { // IMPLEMENT:
                const opLoadFieldDefaultValue = op as MIRLoadFieldDefaultValue;
                console.log(opLoadFieldDefaultValue);

                // return [this.MIRArgumentToTermExpr(opMIRLoadFieldDefaultValue.trgt, fkey, 
                //     this.MIRArgumentToTypeExpr(opReturnAssign.src, fkey)),
                // this.MIRArgumentToTermExpr(opReturnAssign.src, fkey, undefined)];

                TranslatorBosqueFStar.debugging("LoadFieldDefaultValue Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_LoadFieldDefaultValue", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            // ----------------------------------------------------------------------------------------------------------------------------------------------------




            // case MIROpTag.AccessCapturedVariable: { // IMPLEMENT:
            //     TranslatorBosqueFStar.debugging("AcessCapturedVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_AccessCapturedVariable", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            // }


            // ----------------------------------------------------------------------------------------------------------------------------------------------------
            case MIROpTag.MIRAccessArgVariable: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("AccessArgVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_AccessArgVariable", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            case MIROpTag.MIRAccessLocalVariable: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("AcessLocalVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_AcessLocalVariable", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            // ----------------------------------------------------------------------------------------------------------------------------------------------------





            case MIROpTag.MIRConstructorPrimary: {
                const opConstructorPrimary = op as MIRConstructorPrimary;
                const current_tkey = opConstructorPrimary.tkey

                const current_entity_decl = TranslatorBosqueFStar.mapEntityDeclarations.get(current_tkey) as MIREntityTypeDecl;
                const field_types = current_entity_decl.fields.map(x => [x.name,
                TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]) as [string, TypeExpr][];
                const assignments = opConstructorPrimary.args.map((x, index) => [this.MIRArgumentToTermExpr(new MIRVariable(opConstructorPrimary.trgt.nameID + "_arg_" + index), fkey, this.MIRArgumentToTypeExpr(x, fkey))
                    , this.MIRArgumentToTermExpr(x, fkey, undefined)]) as [VarTerm, TermExpr][];

                assignments.unshift([
                    this.MIRArgumentToTermExpr(opConstructorPrimary.trgt, fkey, new ConstructorType(current_tkey, field_types)),
                    new FuncTerm("B" + sanitizeName(current_tkey), assignments.map(x => x[0]), new ConstructorType(current_tkey, field_types), fkey)
                ]);
                return assignments;
            }



            // ----------------------------------------------------------------------------------------------------------------------------------------------------
            case MIROpTag.MIRConstructorPrimaryCollectionEmpty: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionEmpty Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionEmpty", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            case MIROpTag.MIRConstructorPrimaryCollectionSingletons: { // IMPLEMENTING
                const opConstructorPrimaryCollectionsSingletons = op as MIRConstructorPrimaryCollectionSingletons;
                console.log(opConstructorPrimaryCollectionsSingletons);
                return [new VarTerm("_ConstructorPrimaryCollectionSingletons", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            case MIROpTag.MIRConstructorPrimaryCollectionCopies: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionCopies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionCopies", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            case MIROpTag.MIRConstructorPrimaryCollectionMixed: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionMixed Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_ConstructorPrimaryCollectionMixed", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            // ----------------------------------------------------------------------------------------------------------------------------------------------------



            case MIROpTag.MIRConstructorTuple: {
                const opConstructorTuple = op as MIRConstructorTuple;
                const types = opConstructorTuple.args.map(x => this.MIRArgumentToTypeExpr(x, fkey));
                const elements = opConstructorTuple.args.map(x => this.MIRArgumentToTermExpr(x, fkey, undefined));
                return [this.MIRArgumentToTermExpr(opConstructorTuple.trgt, fkey, new TupleType(false, types)),
                new TupleTerm(elements, fkey)];
            }
            case MIROpTag.MIRConstructorRecord: {
                const opConstructorRecord = op as MIRConstructorRecord;
                const field_names = opConstructorRecord.args.map(x => x[0]);
                const types_of_elements = opConstructorRecord.args.map(x => this.MIRArgumentToTypeExpr(x[1], fkey));
                const elements = opConstructorRecord.args.map(x => this.MIRArgumentToTermExpr(x[1], fkey, undefined));
                return [this.MIRArgumentToTermExpr(opConstructorRecord.trgt, fkey, new RecordType(false, field_names, types_of_elements)),
                new RecordTerm(field_names, elements, fkey)];
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
                    resultType, fkey)];
            }
            // case MIROpTag.CallStaticFunction: { // IMPLEMENT:
            //     TranslatorBosqueFStar.debugging("CallStaticFunction Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_CallStaticFunction", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            // }
            case MIROpTag.MIRAccessFromIndex: {
                const opAccessFromIndex = op as MIRAccessFromIndex;
                const dimension = (this.MIRArgumentToTypeExpr(opAccessFromIndex.arg, fkey) as TupleType).elements.length;

                return [
                    this.MIRArgumentToTermExpr(opAccessFromIndex.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromIndex.resultAccessType)),
                    new TupleProjExpr(opAccessFromIndex.idx, dimension,
                        this.MIRArgumentToTermExpr(opAccessFromIndex.arg, fkey, undefined),
                        TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromIndex.resultAccessType), fkey)
                ];
            }
            case MIROpTag.MIRProjectFromIndecies: {
                const opProjectFromIndecies = op as MIRProjectFromIndecies;
                const arg_dimension = (this.MIRArgumentToTypeExpr(opProjectFromIndecies.arg, fkey) as TupleType).elements.length;
                const actual_type_array = opProjectFromIndecies.resultProjectType.slice(1, -1).split(", ");

                const projected_args = opProjectFromIndecies.indecies.map((value, index) => [
                    this.MIRArgumentToTermExpr("__fresh_name" + (TranslatorBosqueFStar.fresh_count + index), fkey, TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index])),
                    new TupleProjExpr(value, arg_dimension,
                        this.MIRArgumentToTermExpr(opProjectFromIndecies.arg, fkey, undefined),
                        TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index]), fkey)
                ]) as [VarTerm, TermExpr][];

                TranslatorBosqueFStar.fresh_count += projected_args.length;

                const lhs_term = this.MIRArgumentToTermExpr(opProjectFromIndecies.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opProjectFromIndecies.resultProjectType));
                const rhs_term = new TupleTerm(projected_args.map(x => x[0]), fkey);

                projected_args.unshift([lhs_term, rhs_term]);

                return projected_args;
            }
            case MIROpTag.MIRAccessFromProperty: {
                const opAccessFromProperty = op as MIRAccessFromProperty;
                const dimension = (this.MIRArgumentToTypeExpr(opAccessFromProperty.arg, fkey) as RecordType).elements.length;

                return [
                    this.MIRArgumentToTermExpr(opAccessFromProperty.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromProperty.resultAccessType)),
                    new RecordProjExpr(opAccessFromProperty.property, dimension,
                        this.MIRArgumentToTermExpr(opAccessFromProperty.arg, fkey, undefined),
                        TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromProperty.resultAccessType), fkey)
                ];
            }
            case MIROpTag.MIRProjectFromProperties: {
                const opProjectFromIndecies = op as MIRProjectFromProperties;
                const arg_dimension = (this.MIRArgumentToTypeExpr(opProjectFromIndecies.arg, fkey) as RecordType).elements.length;
                const actual_type_array = opProjectFromIndecies.resultProjectType.slice(1, -1).split(", ").map(x => {
                    const index = x.indexOf(":") + 1;
                    return x.substring(index);
                });

                const projected_args = opProjectFromIndecies.properties.map((value, index) => [
                    this.MIRArgumentToTermExpr("__fresh_name" + (TranslatorBosqueFStar.fresh_count + index), fkey, TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index])),
                    new RecordProjExpr(value, arg_dimension,
                        this.MIRArgumentToTermExpr(opProjectFromIndecies.arg, fkey, undefined),
                        TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index]), fkey)
                ]) as [VarTerm, TermExpr][];

                const lhs_term = this.MIRArgumentToTermExpr(opProjectFromIndecies.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opProjectFromIndecies.resultProjectType));
                const rhs_term = new RecordTerm(opProjectFromIndecies.properties, projected_args.map(x => x[0]), fkey);

                projected_args.unshift([lhs_term, rhs_term]);
                return projected_args;
            }
            case MIROpTag.MIRAccessFromField: {
                const opAccessFromField = op as MIRAccessFromField;

                const last_index_point = opAccessFromField.field.lastIndexOf(".");
                const field_name = opAccessFromField.field.substr(last_index_point + 1);
                const type_src = (this.types_seen.get(sanitizeName(opAccessFromField.arg.nameID + fkey)) as ConstructorType);
                const scope_name = sanitizeName(type_src.original_name);

                return [this.MIRArgumentToTermExpr(opAccessFromField.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromField.resultAccessType)),
                new FuncTerm(`projectB${scope_name}_${field_name}`,
                    [this.MIRArgumentToTermExpr(opAccessFromField.arg, fkey, undefined)],
                    TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromField.resultAccessType), fkey)
                ];
            }

            case MIROpTag.MIRProjectFromFields: {
                const opProjectFromFields = op as MIRProjectFromFields;

                const actual_type_array = opProjectFromFields.resultProjectType.slice(1, -1).split(", ").map(x => {
                    const index = x.indexOf(":") + 1;
                    return x.substring(index);
                });
                const type_src = (this.types_seen.get(sanitizeName(opProjectFromFields.arg.nameID + fkey)) as ConstructorType);
                const scope_name = sanitizeName(type_src.original_name);

                const properties = opProjectFromFields.fields.map((value, _) => {
                    const last_index_point = value.lastIndexOf(".");
                    return value.substr(last_index_point + 1)
                });

                const projected_args = opProjectFromFields.fields.map((_, index) => {
                    return [
                        this.MIRArgumentToTermExpr("__fresh_name" + (TranslatorBosqueFStar.fresh_count + index),
                            fkey, TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index])),

                        new FuncTerm(`projectB${scope_name}_${properties[index]}`,
                            [this.MIRArgumentToTermExpr(opProjectFromFields.arg, fkey, undefined)],
                            TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index]), fkey)
                    ]
                }) as [VarTerm, TermExpr][];

                TranslatorBosqueFStar.fresh_count += projected_args.length;

                const lhs_term = this.MIRArgumentToTermExpr(opProjectFromFields.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opProjectFromFields.resultProjectType));
                const rhs_term = new RecordTerm(properties, projected_args.map(x => x[0]), fkey);
                projected_args.unshift([lhs_term, rhs_term]);

                return projected_args;
            }




            // ----------------------------------------------------------------------------------------------------------------------------------------------------
            case MIROpTag.MIRProjectFromTypeTuple: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeTuple Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromTypeTuple", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            case MIROpTag.MIRProjectFromTypeRecord: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeRecord Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRProjectFromTypeRecord", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            case MIROpTag.MIRProjectFromTypeConcept: { // IMPLEMET:
                const opProjectFromTypeConcept = op as MIRProjectFromTypeConcept;
                console.log(opProjectFromTypeConcept);

                console.log(this.types_seen.get(sanitizeName(opProjectFromTypeConcept.arg.nameID + fkey)));

                return [new VarTerm("_MIRProjectFromTypeConcept", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];

                // return [this.MIRArgumentToTermExpr(opProjectFromTypeConcept.trgt, fkey, ), // KEEP WORKING HERE
                //     TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            // ----------------------------------------------------------------------------------------------------------------------------------------------------






            // ----------------------------------------------------------------------------------------------------------------------------------------------------
            case MIROpTag.MIRModifyWithIndecies: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRModifyWithIndecies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRModifyWithIndecies", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            case MIROpTag.MIRModifyWithProperties: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRModifyWithProperties Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRModifyWithProperties", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            case MIROpTag.MIRModifyWithFields: { // IMPLEMENT:
                const opModifyWithFields = op as MIRModifyWithFields;
                console.log(opModifyWithFields);

                return [new VarTerm("_MIRModifyWithFields", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            // ----------------------------------------------------------------------------------------------------------------------------------------------------





            // ----------------------------------------------------------------------------------------------------------------------------------------------------
            case MIROpTag.MIRStructuredExtendTuple: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRStructuredExtendedTuple Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRStructuredExtendTuple", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            case MIROpTag.MIRStructuredExtendRecord: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRStructuredExtendRecord Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRStructuredExtendRecord", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            case MIROpTag.MIRStructuredExtendObject: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRStructuredExtendObject Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRStructuredExtendObject", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            // ----------------------------------------------------------------------------------------------------------------------------------------------------



            // case MIROpTag.MIRInvokeKnownTarget: { // IMPLEMENT:
            //     TranslatorBosqueFStar.debugging("MIRInvokeKnownTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_MIRInvokeKnownTarget", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            // }



            // ----------------------------------------------------------------------------------------------------------------------------------------------------
            case MIROpTag.MIRInvokeVirtualTarget: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRInvokeVirtualTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRInvokeVirtualTarget", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            // ----------------------------------------------------------------------------------------------------------------------------------------------------



            // case MIROpTag.MIRCallLambda: { // IMPLEMENT:
            //     TranslatorBosqueFStar.debugging("MIRCallLambda Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_MIRCallLambda", TranslatorBosqueFStar.intType), new ConstTerm("0", TranslatorBosqueFStar.intType)];
            // }
            case MIROpTag.MIRPrefixOp: {
                const opPrefixOp = op as MIRPrefixOp;
                return [this.MIRArgumentToTermExpr(opPrefixOp.trgt, fkey, this.MIRArgumentToTypeExpr(opPrefixOp.arg, fkey)),
                new FuncTerm(TermExpr.unaryOpToFStar.get(opPrefixOp.op) as string,
                    [this.MIRArgumentToTermExpr(opPrefixOp.arg, fkey, undefined)],
                    this.MIRArgumentToTypeExpr(opPrefixOp.arg, fkey), fkey)];
            }
            case MIROpTag.MIRBinOp: {
                const opBinOp = op as MIRBinOp;
                const lhs = this.MIRArgumentToTermExpr(opBinOp.lhs, fkey, undefined);
                const rhs = this.MIRArgumentToTermExpr(opBinOp.rhs, fkey, undefined);
                return [this.MIRArgumentToTermExpr(opBinOp.trgt, fkey, TranslatorBosqueFStar.intType),
                new FuncTerm(TermExpr.binOpToFStar.get(opBinOp.op) as string,
                    [lhs, rhs],
                    TranslatorBosqueFStar.intType, fkey)];
            }




            // ----------------------------------------------------------------------------------------------------------------------------------------------------
            case MIROpTag.MIRBinEq: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRBinEq Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRBinEq", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            // ----------------------------------------------------------------------------------------------------------------------------------------------------



            case MIROpTag.MIRBinCmp: { // DOUBLE CHECK regarding strings
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
                new FuncTerm((TermExpr.binOpToFStar.get(opBinCmp.op) as string), [lhs, rhs], TranslatorBosqueFStar.boolType, fkey)];
                // return [this.MIRArgumentToTermExpr(opBinCmp.trgt, fkey, TranslatorBosqueFStar.boolType),
                //     new FuncTerm("extractBool",
                //         [new FuncTerm((TermExpr.binOpToFStar.get(opBinCmp.op) as string), [lhs, rhs], TranslatorBosqueFStar.boolType, fkey)],
                //         TranslatorBosqueFStar.boolType, fkey)];
            }





            // ----------------------------------------------------------------------------------------------------------------------------------------------------
            case MIROpTag.MIRRegAssign: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRRegAssign Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRRegAssign", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            case MIROpTag.MIRTruthyConvert: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRTruthyConvert Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRTruthyConvert", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            // ----------------------------------------------------------------------------------------------------------------------------------------------------






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




            // ----------------------------------------------------------------------------------------------------------------------------------------------------
            case MIROpTag.MIRAbort: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRAbort Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRAbort", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
                // Returns error
            }
            case MIROpTag.MIRDebug: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRDDebug Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRDebug", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
                // Print ignore
            }
            // ----------------------------------------------------------------------------------------------------------------------------------------------------



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
            case MIROpTag.MIRPhi: { // DOUBLE CHECK
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
                return [this.MIRArgumentToTermExpr(opPhi.trgt, fkey, undefined),
                this.MIRArgumentToTermExpr(opPhi.src.get(comingFrom) as MIRRegisterArgument, fkey, undefined)];
            }
            case MIROpTag.MIRIsTypeOfNone: {
                const opIsTypeOfNone = op as MIRIsTypeOfNone;
                return [this.MIRArgumentToTermExpr(opIsTypeOfNone.trgt, fkey, TranslatorBosqueFStar.boolType),
                new FuncTerm("isNone",
                    [this.MIRArgumentToTermExpr(opIsTypeOfNone.arg, fkey, undefined)],
                    TranslatorBosqueFStar.boolType, fkey)];
            }
            case MIROpTag.MIRIsTypeOfSome: {
                const opIsTypeOfSome = op as MIRIsTypeOfSome;
                return [this.MIRArgumentToTermExpr(opIsTypeOfSome.trgt, fkey, TranslatorBosqueFStar.boolType),
                new FuncTerm("isSome",
                    [this.MIRArgumentToTermExpr(opIsTypeOfSome.arg, fkey, undefined)],
                    TranslatorBosqueFStar.boolType, fkey)];
            }



            // ----------------------------------------------------------------------------------------------------------------------------------------------------
            case MIROpTag.MIRIsTypeOf: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRIsTypeOf Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRIsTypeOf", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            // PRIORITY:
            case MIROpTag.MIRAccessConstantValue: { // IMPLEMENT
                TranslatorBosqueFStar.debugging("MIRAccessConstantValue Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new VarTerm("_MIRAccessConstantValue", TranslatorBosqueFStar.intType, fkey), new ConstTerm("0", TranslatorBosqueFStar.intType, fkey)];
            }
            // ----------------------------------------------------------------------------------------------------------------------------------------------------




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
                return (result as [VarTerm, TermExpr][])
                    .reduce((rest_expression, current_assignment) =>
                        new AssignmentExpr(current_assignment[0], current_assignment[1], rest_expression),
                        this.opsToExpr(ops.slice(1), comingFrom, fkey, program));
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
                this.types_seen.set(sanitizeName(x.name + fkey), TranslatorBosqueFStar.stringVarToTypeExpr(x.type))
            );

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
                        const continuation = () => new ReturnExpr(new VarTerm(regName, returnType, fkey));
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
                        const condition = new VarTerm(regName, TranslatorBosqueFStar.boolType, fkey);
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
                    new FunctionDeclaration(declarations, traverse(mapBlocks.get("entry") as MIRBasicBlock, "entry"))
                );
            }
        }
    }

    generateFStarCode(fkey: string) {

        const user_defined_types_map: Map<string, MIRConceptTypeDecl | MIREntityTypeDecl>
            = new Map([...TranslatorBosqueFStar.mapConceptDeclarations, ...TranslatorBosqueFStar.mapEntityDeclarations]);
        const user_defined_types = this.extractProvidesRelation(user_defined_types_map);

        // --------------------------------------------------------------------------------------------------------------
        // BosqueTypes files
        printBosqueTypesFST(this.fstar_files_directory, user_defined_types);
        // --------------------------------------------------------------------------------------------------------------
        // ---------------------------------------------------------------------
        // BosqueTerms files
        printBosqueTermsFST(this.fstar_files_directory, user_defined_types_map);
        // ---------------------------------------------------------------------

        const fd = FS.openSync(this.fstar_files_directory + this.fileName, 'w');
        this.collectExpr(fkey);

        // --------------------------------------------------------------------------------------------------
        // Main file
        // --------------------------------------------------------
        // Prelude
        FS.writeSync(fd, `module ${this.fileName.slice(0, -4)}\n`);
        FS.writeSync(fd, `open Sequence\n`);
        FS.writeSync(fd, `open BosqueTypes\n`);
        FS.writeSync(fd, `open BosqueTerms\n`);
        FS.writeSync(fd, `open Util\n`);
        FS.writeSync(fd, "\n");
        // --------------------------------------------------------
        // ------------------------------------
        FS.writeSync(fd, "(* Type names *)\n");
        TypeExpr.declareTypeNames(fd);
        FS.writeSync(fd, "\n");
        // ------------------------------------
        // --------------------------------------------------------------------------------------------------
        FS.writeSync(fd, "(* Constant Declarations *)\n");
        this.mapConstantDeclarations.forEach(constant_decl => {
            // Constant declaration generally have only two blocks: entry and exit
            // We just `declare` the entry block
            constant_decl.value.body.forEach(basicBlock => {
                if (basicBlock.label == "entry") {
                    const returnType = TranslatorBosqueFStar.stringVarToTypeExpr(constant_decl.declaredType);
                    const continuation = () => new ReturnExpr(new VarTerm("__ir_ret__", returnType, fkey));
                    this.types_seen.set(sanitizeName(constant_decl.cname), returnType);
                    FS.writeSync(fd,
                        `let ${sanitizeName(constant_decl.cname)} =\
                         \n${this.opsToExpr(basicBlock.ops, "entry", "", continuation).toML(1, 0)}\n`);
                }
            });
        });
        FS.writeSync(fd, "\n");
        // --------------------------------------------------------------------------------------------------
        // -----------------------------------------------
        FS.writeSync(fd, "(* Function Declarations *)\n");
        this.function_declarations.map(x => x.print(fd));
        // -----------------------------------------------
        // --------------------------------------------------------------------------------------------------

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
        FS.writeSync(fd, `val ${sanitizeName(fkey)} : ${type.valDeclare()}\n`);
        FS.writeSync(fd, `let ${sanitizeName(fkey)} ${args.join(" ")} = \n${this.program.toML(1, 1)}\n\n`);
    }
}

export { TranslatorBosqueFStar }