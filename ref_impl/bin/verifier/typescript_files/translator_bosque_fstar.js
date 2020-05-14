"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
// PRIORITIES:
// LoadFieldDefaultValue Not implemented yet
// MIRAccessConstantValue Not implemented yet
// MIRAccessFromField Not implemented yet
// MIRModifyWithFields Not implemented yetcat
// MIRIsTypeOfSome Not implemented yet
// ConstructorPrimaryCollectionSingletons Not implemented yet
const FS = require("fs");
const ChildProcess = require("child_process");
const Path = require("path");
const mir_ops_1 = require("../../compiler/mir_ops");
const mir_info_1 = require("../../compiler/mir_info");
const expression_expr_1 = require("./expression_expr");
const type_expr_1 = require("./type_expr");
const term_expr_1 = require("./term_expr");
const util_1 = require("./util");
const bosqueTypesFST_1 = require("./bosqueTypesFST");
const bosqueTermsFST_1 = require("./bosqueTermsFST");
class TranslatorBosqueFStar {
    constructor(masm, file_name) {
        // Revelant information about masm
        // masm.typeMap: Map containing all the types used in the programs to analyze
        // masm.entityDecls: Map containing entities
        // masm.conceptDecls: Map containing concepts
        // masm.primitiveInvokeDecls: Map containing ?
        // masm.invokeDecls: Map containing function declarations
        // masm.fieldDecls: Map containing declaration about field (in concepts and entities as well)
        this.is_fkey_declared = new Set();
        this.function_declarations = [];
        this.default_values = new Map();
        masm.fieldDecls.forEach(x => {
            if (x.value !== undefined) {
                console.log(x);
                this.default_values.set(x.fname, x.value);
            }
        });
        this.types_seen = new Map();
        this.func_declarations = masm.invokeDecls;
        TranslatorBosqueFStar.concept_declarations = masm.conceptDecls;
        TranslatorBosqueFStar.entity_declarations = masm.entityDecls;
        this.constant_declarations = masm.constantDecls;
        // ---------------------------------------------------------------------------------------------------------
        // masm.primitiveInvokeDecls contains all the functions
        // used in the Bosque File from the Core and Collection library
        // FIX: This is wrong, because these function should have
        // its actual FStar implementation. It's useful because
        // momentarily these functions have 'valid definitions'.
        masm.primitiveInvokeDecls.forEach((_, index) => {
            this.func_declarations.set(index, this.func_declarations.get("NSMain::id"));
        });
        // ---------------------------------------------------------------------------------------------------------
        this.file_name = file_name;
        this.fstar_files_directory = Path.join(Path.normalize(Path.join(__dirname, "../")), "/fstar_files").replace("bin", "src");
    }
    extractProvidesRelation(declarations) {
        const nodes_neighbors = new Map();
        declarations.forEach((value, index) => {
            if (!index.includes("NSCore")) {
                if (nodes_neighbors.get(index) == undefined) {
                    nodes_neighbors.set(index, new Set());
                }
                value.provides.map(x => {
                    if (nodes_neighbors.get(x) == undefined) {
                        nodes_neighbors.set(x, new Set());
                    }
                    nodes_neighbors.get(x).add(index);
                });
            }
        });
        return nodes_neighbors;
    }
    serializeTypes(declarations) {
        const nodes_neighbors = this.extractProvidesRelation(declarations);
        return new Set(util_1.topologicalOrder(nodes_neighbors));
    }
    static debugging(message, flag) {
        if (flag) {
            console.log(message);
        }
    }
    static optionalTupleSugaring(non_optionals, optionals) {
        const set_of_types = new Set();
        // set_of_types.add(new TupleType(false, non_optionals));
        const num_optionals = optionals.length;
        for (let index = 0; index < num_optionals; ++index) {
            // Copy non_optionals
            let temp = [];
            for (let i = 0; i < non_optionals.length; ++i) {
                temp.push(non_optionals[i]);
            }
            // Copy optionals
            for (let i = 0; i < index; ++i) {
                temp.push(optionals[i]);
            }
            set_of_types.add(new type_expr_1.TupleType(false, temp));
        }
        return new type_expr_1.UnionType(set_of_types);
    }
    static optionalRecordSugaring(non_optional_properties, non_optional_types, optional_properties, optional_types) {
        const set_of_types = new Set();
        const total = Math.pow(2, optional_properties.length);
        for (let i = 0; i < total; i++) {
            let temp_set_properties = [];
            let temp_set_types = [];
            // Copy non_optionals
            for (let i = 0; i < non_optional_properties.length; ++i) {
                temp_set_properties.push(non_optional_properties[i]);
                temp_set_types.push(non_optional_types[i]);
            }
            let num = i.toString(2);
            while (num.length < optional_properties.length) {
                num = '0' + num;
            }
            for (let b = 0; b < num.length; b++) {
                if (num[b] === '1') {
                    // Copy optionals
                    temp_set_properties.push(optional_properties[b]);
                    temp_set_types.push(optional_types[b]);
                }
            }
            const entries_temp = temp_set_properties.map((value, index) => [value, temp_set_types[index]]);
            entries_temp.sort((x, y) => x[0].localeCompare(y[0]));
            set_of_types.add(new type_expr_1.RecordType(false, entries_temp.map(x => x[0]), entries_temp.map(x => x[1])));
        }
        return new type_expr_1.UnionType(set_of_types);
    }
    // TOUPDATE: Add more types as needed
    // String[Type] means that the string is a type which 
    // description comes from a Type expression
    // stringVarToTypeExpr : String[Type] -> TypeExpr
    static stringVarToTypeExpr(s) {
        switch (s) {
            case "NSCore::Any": {
                return TranslatorBosqueFStar.any_type;
            }
            case "NSCore::Some": {
                return TranslatorBosqueFStar.some_type;
            }
            case "NSCore::Truthy": {
                return TranslatorBosqueFStar.truthy_type;
            }
            case "NSCore::None": {
                return TranslatorBosqueFStar.none_type;
            }
            case "NSCore::Parsable": {
                return TranslatorBosqueFStar.parsable_type;
            }
            case "NSCore::Bool": {
                return TranslatorBosqueFStar.bool_type;
            }
            case "NSCore::Int": {
                return TranslatorBosqueFStar.int_type;
            }
            case "NSCore::GUID": {
                return TranslatorBosqueFStar.guid_type;
            }
            case "NSCore::Object": {
                return TranslatorBosqueFStar.object_type;
            }
            default: {
                // Concept
                if (TranslatorBosqueFStar.concept_declarations.has(s) && !s.includes("NSCore")) {
                    const description = TranslatorBosqueFStar.concept_declarations.get(s);
                    return new type_expr_1.ConstructorType(description.tkey, description.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]));
                }
                // Entities
                if (TranslatorBosqueFStar.entity_declarations.has(s) && !s.includes("NSCore")) {
                    const description = TranslatorBosqueFStar.entity_declarations.get(s);
                    return new type_expr_1.ConstructorType(description.tkey, description.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]));
                }
                // Tuple
                if (s.charAt(0) == '[') {
                    s = s.slice(1, -1);
                    let is_open = false;
                    // Open Tuple check
                    if (s.includes("...")) {
                        s = s.slice(0, -5); // Getting rid of the ellipsis and comma
                        is_open = true;
                    }
                    if (s.includes("?:")) {
                        // This is based on the assumption that 
                        // concrete types cannot follow optional types
                        // inside tuples
                        const types = s.split("?:");
                        const non_optionals = types[0];
                        const optionals = types.slice(1);
                        if (non_optionals.length == 0) {
                            return this.optionalTupleSugaring([], optionals.map(x => x.includes(",") ? x.slice(0, -2) : x).map(TranslatorBosqueFStar.stringVarToTypeExpr));
                        }
                        else {
                            return this.optionalTupleSugaring(non_optionals.slice(0, -2).split(", ").map(TranslatorBosqueFStar.stringVarToTypeExpr), optionals.map(x => x.includes(",") ? x.slice(0, -2) : x).map(TranslatorBosqueFStar.stringVarToTypeExpr));
                        }
                    }
                    else {
                        return new type_expr_1.TupleType(is_open, s.split(", ").map(TranslatorBosqueFStar.stringVarToTypeExpr));
                    }
                }
                // Record
                if (s.charAt(0) == '{') {
                    s = s.slice(1, -1);
                    let is_open = false;
                    // Open Record check
                    if (s.includes("...")) {
                        s = s.slice(0, -5); // Getting rid of the ellipsis and comma
                        is_open = true;
                    }
                    const entries = s.split(", ");
                    if (s.includes("?:")) {
                        // This is based on the assumption that 
                        // concrete types cannot follow optional types
                        // inside tuples
                        const non_optional_entries = entries.filter(x => !x.includes("?:"));
                        const optional_entries = entries.filter(x => x.includes("?:"));
                        const non_optional_field_names = non_optional_entries.map(x => x.substring(0, x.indexOf(":")));
                        const optional_field_names = optional_entries.map(x => x.substring(0, x.indexOf("?:")));
                        const non_optional_types = non_optional_entries.map(x => x.substring(x.indexOf(":") + 1)).map(TranslatorBosqueFStar.stringVarToTypeExpr);
                        const optional_types = optional_entries.map(x => x.substring(x.indexOf("?:") + 2)).map(TranslatorBosqueFStar.stringVarToTypeExpr);
                        return this.optionalRecordSugaring(non_optional_field_names, non_optional_types, optional_field_names, optional_types);
                    }
                    else {
                        const field_names = entries.map(x => x.substring(0, x.indexOf(":")));
                        const types = entries.map(x => x.substring(x.indexOf(":") + 1)).map(TranslatorBosqueFStar.stringVarToTypeExpr);
                        return new type_expr_1.RecordType(is_open, field_names, types);
                    }
                }
                // Union
                if (s.includes("|")) {
                    return new type_expr_1.UnionType(new Set(s
                        .split(" | ")
                        .map(TranslatorBosqueFStar.stringVarToTypeExpr)));
                }
                // Typed String 
                if (s.includes("NSCore::String")) {
                    const index = s.indexOf("=");
                    // This branch handles untyped strings
                    if (index == -1) {
                        return TranslatorBosqueFStar.string_type;
                    }
                    // This branch handles typed strings
                    else {
                        s = s.substr(index + 1, s.length - index - 2);
                        return new type_expr_1.TypedStringType(TranslatorBosqueFStar.stringVarToTypeExpr(s));
                    }
                }
                console.log(s);
                console.log(`------ ERROR: Unknown type ${s} found while executing stringVarToTypeExpr ------`);
                throw new Error("------ ERROR: Unknown typed found while executin stringVarToTypeExpr ------");
            }
        }
    }
    // String[ValueType] means that the string is a type which
    // description comes from a Value expression
    // stringConstToTypeExpr : String[ValueType] -> TypeExpr
    static stringConstToTypeExpr(s) {
        let string_const = s.slice(1);
        string_const = string_const.substr(0, string_const.indexOf("="));
        switch (string_const) {
            case "none": {
                return TranslatorBosqueFStar.none_type;
            }
            case "int": {
                return TranslatorBosqueFStar.int_type;
            }
            case "true": {
                return TranslatorBosqueFStar.bool_type;
            }
            case "false": {
                return TranslatorBosqueFStar.bool_type;
            }
            case "string": {
                return TranslatorBosqueFStar.string_type;
            }
            default: {
                console.log("The case " + string_const + " is not implemented yet");
                throw new Error("The case " + string_const + " is not implemented yet");
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
    MIRArgumentToTermExpr(arg, fkey, ty) {
        // This branch handles string names
        // These encode fresh names
        if (typeof arg === "string") {
            if (ty instanceof type_expr_1.TypeExpr) {
                const m_ty = ty;
                this.types_seen.set(util_1.sanitizeName(fkey + arg), m_ty);
                return new term_expr_1.VarTerm(util_1.sanitizeName(arg), m_ty, fkey);
            }
            else {
                return new term_expr_1.VarTerm(util_1.sanitizeName(arg), this.types_seen.get(util_1.sanitizeName(fkey + arg)), fkey);
            }
        }
        // This branch handles variables
        if (arg instanceof mir_ops_1.MIRRegisterArgument) {
            if (ty instanceof type_expr_1.TypeExpr) {
                this.types_seen.set(util_1.sanitizeName(fkey + arg.nameID), ty);
                return new term_expr_1.VarTerm(util_1.sanitizeName(arg.nameID), ty, fkey);
            }
            else {
                return new term_expr_1.VarTerm(util_1.sanitizeName(arg.nameID), this.types_seen.get(util_1.sanitizeName(fkey + arg.nameID)), fkey);
            }
        }
        // This branch handles constants
        else {
            return new term_expr_1.ConstTerm(arg.stringify(), TranslatorBosqueFStar.stringConstToTypeExpr(arg.nameID), fkey);
        }
    }
    // MIRArgumentToTypeExpr : MIRArgument -> TypeExpr
    MIRArgumentToTypeExpr(arg, fkey) {
        if (typeof arg === "string") {
            return this.types_seen.get(fkey + arg);
        }
        // This branch handles variables
        if (arg instanceof mir_ops_1.MIRRegisterArgument) {
            return this.types_seen.get(util_1.sanitizeName(fkey + arg.nameID));
        }
        // This branch handles constants
        else {
            return TranslatorBosqueFStar.stringConstToTypeExpr(arg.nameID);
        }
    }
    opToAssignment(op, comingFrom, fkey) {
        switch (op.tag) {
            case mir_ops_1.MIROpTag.MIRLoadConst: {
                const opLoadConst = op;
                console.log(opLoadConst);
                const second_equal_sign_position = opLoadConst.src.nameID.indexOf("=", 1);
                const name_length = opLoadConst.src.nameID.length;
                const value_type = opLoadConst.src.nameID.slice(1, second_equal_sign_position - name_length);
                let value;
                if (value_type == "int" || value_type == "string") {
                    value = opLoadConst.src.nameID.slice(second_equal_sign_position + 1);
                }
                else {
                    value = value_type;
                }
                return [this.MIRArgumentToTermExpr(opLoadConst.trgt, fkey, TranslatorBosqueFStar.stringConstToTypeExpr(opLoadConst.src.nameID)),
                    new term_expr_1.ConstTerm(value, TranslatorBosqueFStar.stringConstToTypeExpr(opLoadConst.src.nameID), fkey)];
            }
            case mir_ops_1.MIROpTag.MIRLoadConstTypedString: {
                const opMIRLoadConstTypedString = op;
                const current_tkey = opMIRLoadConstTypedString.tkey;
                const partial_decl = TranslatorBosqueFStar.entity_declarations.get(current_tkey);
                let current_type;
                if (partial_decl == undefined) {
                    const actual_decl = TranslatorBosqueFStar.concept_declarations.get(current_tkey);
                    current_type = new type_expr_1.ConstructorType(actual_decl.tkey, actual_decl.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]));
                }
                else {
                    current_type = new type_expr_1.ConstructorType(partial_decl.tkey, partial_decl.fields.map(x => [x.name, TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]));
                }
                return [
                    this.MIRArgumentToTermExpr(opMIRLoadConstTypedString.trgt, fkey, new type_expr_1.TypedStringType(current_type)),
                    new term_expr_1.ConstTerm("\"" + opMIRLoadConstTypedString.ivalue.slice(1, -1) + "\"", new type_expr_1.TypedStringType(current_type), fkey)
                ];
            }
            // case MIROpTag.AccessConstField:
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRLoadFieldDefaultValue: { // IMPLEMENT:
                const opLoadFieldDefaultValue = op;
                console.log(opLoadFieldDefaultValue);
                // KEEP: working here
                // return [this.MIRArgumentToTermExpr(opMIRLoadFieldDefaultValue.trgt, fkey, 
                //     this.MIRArgumentToTypeExpr(opReturnAssign.src, fkey)),
                // this.MIRArgumentToTermExpr(opReturnAssign.src, fkey, undefined)];
                //return [this.MIRArgumentToTermExpr(opLoadFieldDefaultValue.trgt,fkey, this.MIRArgumentToTypeExpr(sanitizeName(opLoadFieldDefaultValue.fkey), "")), 
                //this.MIRArgumentToTermExpr(opLoadFieldDefaultValue.fkey, "", undefined)]
                return [new term_expr_1.VarTerm("_LoadFieldDefaultValue", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            // ---------------------------------------------------------------------------------------------------
            // case MIROpTag.AccessCapturedVariable: { 
            //     TranslatorBosqueFStar.debugging("AcessCapturedVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_AccessCapturedVariable", TranslatorBosqueFStar.int_type), new ConstTerm("0", TranslatorBosqueFStar.int_type)];
            // }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRAccessArgVariable: { // IMPLEMENT:
                const opAccessArgVariable = op;
                console.log(opAccessArgVariable);
                TranslatorBosqueFStar.debugging("AccessArgVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_AccessArgVariable", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRAccessLocalVariable: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("AcessLocalVariable Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_AcessLocalVariable", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRConstructorPrimary: {
                const opConstructorPrimary = op;
                const current_tkey = opConstructorPrimary.tkey;
                const current_entity_decl = TranslatorBosqueFStar.entity_declarations.get(current_tkey);
                const field_types = current_entity_decl.fields.map(x => [x.name,
                    TranslatorBosqueFStar.stringVarToTypeExpr(x.declaredType)]);
                const assignments = opConstructorPrimary.args.map((x, index) => [this.MIRArgumentToTermExpr(new mir_ops_1.MIRVariable(opConstructorPrimary.trgt.nameID + "_arg_" + index), fkey, this.MIRArgumentToTypeExpr(x, fkey)),
                    this.MIRArgumentToTermExpr(x, fkey, undefined)]);
                assignments.unshift([
                    this.MIRArgumentToTermExpr(opConstructorPrimary.trgt, fkey, new type_expr_1.ConstructorType(current_tkey, field_types)),
                    new term_expr_1.FuncTerm("B" + util_1.sanitizeName(current_tkey), assignments.map(x => x[0]), new type_expr_1.ConstructorType(current_tkey, field_types), fkey)
                ]);
                return assignments;
            }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionEmpty: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionEmpty Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_ConstructorPrimaryCollectionEmpty", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                const opConstructorPrimaryCollectionsSingletons = op;
                const current_tkey = opConstructorPrimaryCollectionsSingletons.tkey.slice(opConstructorPrimaryCollectionsSingletons.tkey.indexOf("=") + 1, -1);
                const content_type = TranslatorBosqueFStar.stringVarToTypeExpr(current_tkey);
                const assignments = opConstructorPrimaryCollectionsSingletons.args.map((x, index) => [this.MIRArgumentToTermExpr(new mir_ops_1.MIRVariable(opConstructorPrimaryCollectionsSingletons.trgt.nameID + "_arg_" + index), fkey, this.MIRArgumentToTypeExpr(x, fkey)),
                    this.MIRArgumentToTermExpr(x, fkey, undefined)]);
                assignments.unshift([this.MIRArgumentToTermExpr(opConstructorPrimaryCollectionsSingletons.trgt, fkey, new type_expr_1.ListType(content_type)),
                    new term_expr_1.ListTerm(assignments.map(x => x[0]), content_type, fkey)
                ]);
                return assignments;
            }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionCopies: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionCopies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_ConstructorPrimaryCollectionCopies", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionMixed: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("ConstructorPrimaryCollectionMixed Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_ConstructorPrimaryCollectionMixed", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRConstructorTuple: {
                const opConstructorTuple = op;
                const types = opConstructorTuple.args.map(x => this.MIRArgumentToTypeExpr(x, fkey));
                const elements = opConstructorTuple.args.map(x => this.MIRArgumentToTermExpr(x, fkey, undefined));
                return [this.MIRArgumentToTermExpr(opConstructorTuple.trgt, fkey, new type_expr_1.TupleType(false, types)),
                    new term_expr_1.TupleTerm(elements, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRConstructorRecord: {
                const opConstructorRecord = op;
                const field_names = opConstructorRecord.args.map(x => x[0]);
                const types_of_elements = opConstructorRecord.args.map(x => this.MIRArgumentToTypeExpr(x[1], fkey));
                const elements = opConstructorRecord.args.map(x => this.MIRArgumentToTermExpr(x[1], fkey, undefined));
                return [this.MIRArgumentToTermExpr(opConstructorRecord.trgt, fkey, new type_expr_1.RecordType(false, field_names, types_of_elements)),
                    new term_expr_1.RecordTerm(field_names, elements, fkey)];
            }
            // case MIROpTag.ConstructorLambda: { // IMPLEMENT:
            //     // TranslatorBosqueFStar.debugging("ConstructorLambda Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     // const opConstructorLambda = op as MIRConstructorLambda;
            //     // console.log(opConstructorLambda);
            //     return [new VarTerm("_ConstructorLambda", TranslatorBosqueFStar.int_type), new ConstTerm("0", TranslatorBosqueFStar.int_type)];
            // }
            case mir_ops_1.MIROpTag.MIRInvokeFixedFunction: {
                const opCallNamespaceFunction = op;
                const currentFunctionKey = opCallNamespaceFunction.mkey;
                // The following line will keep pushing to 
                // the stack_expressions stack
                this.collectExpr(currentFunctionKey);
                const resultType = TranslatorBosqueFStar.stringVarToTypeExpr(this.func_declarations.get(currentFunctionKey).resultType);
                return [this.MIRArgumentToTermExpr(opCallNamespaceFunction.trgt, fkey, resultType),
                    new term_expr_1.FuncTerm(util_1.sanitizeName(currentFunctionKey), opCallNamespaceFunction.args.map(x => this.MIRArgumentToTermExpr(x, fkey, undefined)), resultType, fkey)];
            }
            // case MIROpTag.CallStaticFunction: { // IMPLEMENT:
            //     TranslatorBosqueFStar.debugging("CallStaticFunction Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_CallStaticFunction", TranslatorBosqueFStar.int_type), new ConstTerm("0", TranslatorBosqueFStar.int_type)];
            // }
            case mir_ops_1.MIROpTag.MIRAccessFromIndex: {
                const opAccessFromIndex = op;
                const dimension = this.MIRArgumentToTypeExpr(opAccessFromIndex.arg, fkey).elements.length;
                return [
                    this.MIRArgumentToTermExpr(opAccessFromIndex.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromIndex.resultAccessType)),
                    new term_expr_1.TupleProjExpr(opAccessFromIndex.idx, dimension, this.MIRArgumentToTermExpr(opAccessFromIndex.arg, fkey, undefined), TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromIndex.resultAccessType), fkey)
                ];
            }
            case mir_ops_1.MIROpTag.MIRProjectFromIndecies: {
                const opProjectFromIndecies = op;
                const arg_dimension = this.MIRArgumentToTypeExpr(opProjectFromIndecies.arg, fkey).elements.length;
                const actual_type_array = opProjectFromIndecies.resultProjectType.slice(1, -1).split(", ");
                const projected_args = opProjectFromIndecies.indecies.map((value, index) => [
                    this.MIRArgumentToTermExpr("__fresh_name" + (TranslatorBosqueFStar.fresh_count + index), fkey, TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index])),
                    new term_expr_1.TupleProjExpr(value, arg_dimension, this.MIRArgumentToTermExpr(opProjectFromIndecies.arg, fkey, undefined), TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index]), fkey)
                ]);
                TranslatorBosqueFStar.fresh_count += projected_args.length;
                const lhs_term = this.MIRArgumentToTermExpr(opProjectFromIndecies.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opProjectFromIndecies.resultProjectType));
                const rhs_term = new term_expr_1.TupleTerm(projected_args.map(x => x[0]), fkey);
                projected_args.unshift([lhs_term, rhs_term]);
                return projected_args;
            }
            case mir_ops_1.MIROpTag.MIRAccessFromProperty: {
                const opAccessFromProperty = op;
                const dimension = this.MIRArgumentToTypeExpr(opAccessFromProperty.arg, fkey).elements.length;
                return [
                    this.MIRArgumentToTermExpr(opAccessFromProperty.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromProperty.resultAccessType)),
                    new term_expr_1.RecordProjExpr(opAccessFromProperty.property, dimension, this.MIRArgumentToTermExpr(opAccessFromProperty.arg, fkey, undefined), TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromProperty.resultAccessType), fkey)
                ];
            }
            case mir_ops_1.MIROpTag.MIRProjectFromProperties: {
                const opProjectFromIndecies = op;
                const arg_dimension = this.MIRArgumentToTypeExpr(opProjectFromIndecies.arg, fkey).elements.length;
                const actual_type_array = opProjectFromIndecies.resultProjectType.slice(1, -1).split(", ").map(x => {
                    const index = x.indexOf(":") + 1;
                    return x.substring(index);
                });
                const projected_args = opProjectFromIndecies.properties.map((value, index) => [
                    this.MIRArgumentToTermExpr("__fresh_name" + (TranslatorBosqueFStar.fresh_count + index), fkey, TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index])),
                    new term_expr_1.RecordProjExpr(value, arg_dimension, this.MIRArgumentToTermExpr(opProjectFromIndecies.arg, fkey, undefined), TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index]), fkey)
                ]);
                const lhs_term = this.MIRArgumentToTermExpr(opProjectFromIndecies.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opProjectFromIndecies.resultProjectType));
                const rhs_term = new term_expr_1.RecordTerm(opProjectFromIndecies.properties, projected_args.map(x => x[0]), fkey);
                projected_args.unshift([lhs_term, rhs_term]);
                return projected_args;
            }
            case mir_ops_1.MIROpTag.MIRAccessFromField: {
                const opAccessFromField = op;
                const last_index_point = opAccessFromField.field.lastIndexOf(".");
                const field_name = opAccessFromField.field.substr(last_index_point + 1);
                const type_src = this.types_seen.get(util_1.sanitizeName(fkey + opAccessFromField.arg.nameID));
                const scope_name = util_1.sanitizeName(type_src.original_name);
                return [this.MIRArgumentToTermExpr(opAccessFromField.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromField.resultAccessType)),
                    new term_expr_1.FuncTerm(`projectB${scope_name}_${field_name}`, [this.MIRArgumentToTermExpr(opAccessFromField.arg, fkey, undefined)], TranslatorBosqueFStar.stringVarToTypeExpr(opAccessFromField.resultAccessType), fkey)
                ];
            }
            case mir_ops_1.MIROpTag.MIRProjectFromFields: {
                const opProjectFromFields = op;
                const actual_type_array = opProjectFromFields.resultProjectType.slice(1, -1).split(", ").map(x => {
                    const index = x.indexOf(":") + 1;
                    return x.substring(index);
                });
                const type_src = this.types_seen.get(util_1.sanitizeName(fkey + opProjectFromFields.arg.nameID));
                const scope_name = util_1.sanitizeName(type_src.original_name);
                const properties = opProjectFromFields.fields.map((value, _) => {
                    const last_index_point = value.lastIndexOf(".");
                    return value.substr(last_index_point + 1);
                });
                const projected_args = opProjectFromFields.fields.map((_, index) => {
                    return [
                        this.MIRArgumentToTermExpr("__fresh_name" + (TranslatorBosqueFStar.fresh_count + index), fkey, TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index])),
                        new term_expr_1.FuncTerm(`projectB${scope_name}_${properties[index]}`, [this.MIRArgumentToTermExpr(opProjectFromFields.arg, fkey, undefined)], TranslatorBosqueFStar.stringVarToTypeExpr(actual_type_array[index]), fkey)
                    ];
                });
                TranslatorBosqueFStar.fresh_count += projected_args.length;
                const lhs_term = this.MIRArgumentToTermExpr(opProjectFromFields.trgt, fkey, TranslatorBosqueFStar.stringVarToTypeExpr(opProjectFromFields.resultProjectType));
                const rhs_term = new term_expr_1.RecordTerm(properties, projected_args.map(x => x[0]), fkey);
                projected_args.unshift([lhs_term, rhs_term]);
                return projected_args;
            }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRProjectFromTypeTuple: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeTuple Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRProjectFromTypeTuple", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRProjectFromTypeRecord: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRProjectFromTypeRecord Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRProjectFromTypeRecord", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRProjectFromTypeConcept: { // IMPLEMET:
                const opProjectFromTypeConcept = op;
                console.log(opProjectFromTypeConcept);
                //console.log(this.types_seen.get(sanitizeName(fkey + opProjectFromTypeConcept.arg.nameID)));
                return [new term_expr_1.VarTerm("_MIRProjectFromTypeConcept", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
                // return [this.MIRArgumentToTermExpr(opProjectFromTypeConcept.trgt, fkey, ), 
                //     TranslatorBosqueFStar.int_type, fkey), new ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            // ---------------------------------------------------------------------------------------------------
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRModifyWithIndecies: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRModifyWithIndecies Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRModifyWithIndecies", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRModifyWithProperties: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRModifyWithProperties Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRModifyWithProperties", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRModifyWithFields: { // IMPLEMENT:
                const opModifyWithFields = op;
                console.log(opModifyWithFields);
                return [new term_expr_1.VarTerm("_MIRModifyWithFields", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            // ---------------------------------------------------------------------------------------------------
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRStructuredExtendTuple: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRStructuredExtendedTuple Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRStructuredExtendTuple", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRStructuredExtendRecord: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRStructuredExtendRecord Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRStructuredExtendRecord", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRStructuredExtendObject: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRStructuredExtendObject Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRStructuredExtendObject", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            // ---------------------------------------------------------------------------------------------------
            // case MIROpTag.MIRInvokeKnownTarget: { // IMPLEMENT:
            //     TranslatorBosqueFStar.debugging("MIRInvokeKnownTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_MIRInvokeKnownTarget", TranslatorBosqueFStar.int_type), new ConstTerm("0", TranslatorBosqueFStar.int_type)];
            // }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRInvokeVirtualTarget: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRInvokeVirtualTarget Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRInvokeVirtualTarget", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            // ---------------------------------------------------------------------------------------------------
            // case MIROpTag.MIRCallLambda: { // IMPLEMENT:
            //     TranslatorBosqueFStar.debugging("MIRCallLambda Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
            //     return [new VarTerm("_MIRCallLambda", TranslatorBosqueFStar.int_type), new ConstTerm("0", TranslatorBosqueFStar.int_type)];
            // }
            case mir_ops_1.MIROpTag.MIRPrefixOp: {
                const opPrefixOp = op;
                return [this.MIRArgumentToTermExpr(opPrefixOp.trgt, fkey, this.MIRArgumentToTypeExpr(opPrefixOp.arg, fkey)),
                    new term_expr_1.FuncTerm(term_expr_1.TermExpr.unary_op_to_fstar.get(opPrefixOp.op), [this.MIRArgumentToTermExpr(opPrefixOp.arg, fkey, undefined)], this.MIRArgumentToTypeExpr(opPrefixOp.arg, fkey), fkey)];
            }
            case mir_ops_1.MIROpTag.MIRBinOp: {
                const opBinOp = op;
                const lhs = this.MIRArgumentToTermExpr(opBinOp.lhs, fkey, undefined);
                const rhs = this.MIRArgumentToTermExpr(opBinOp.rhs, fkey, undefined);
                return [this.MIRArgumentToTermExpr(opBinOp.trgt, fkey, TranslatorBosqueFStar.int_type),
                    new term_expr_1.FuncTerm(term_expr_1.TermExpr.bin_op_to_fstar.get(opBinOp.op), [lhs, rhs], TranslatorBosqueFStar.int_type, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRBinEq: {
                const opBinEq = op;
                const lhs = this.MIRArgumentToTermExpr(opBinEq.lhs, fkey, undefined);
                const rhs = this.MIRArgumentToTermExpr(opBinEq.rhs, fkey, undefined);
                return [
                    this.MIRArgumentToTermExpr(opBinEq.trgt, fkey, TranslatorBosqueFStar.bool_type),
                    new term_expr_1.FuncTerm("op_eqTerm", [lhs, rhs], TranslatorBosqueFStar.bool_type, fkey)
                ];
            }
            case mir_ops_1.MIROpTag.MIRBinCmp: { // DOUBLE CHECK regarding strings
                // The predicate returned is of type Bool
                // because the operations to arrive at this
                // point are <, <=, >, >= only
                const opBinCmp = op;
                const lhs = this.MIRArgumentToTermExpr(opBinCmp.lhs, fkey, undefined);
                const rhs = this.MIRArgumentToTermExpr(opBinCmp.rhs, fkey, undefined);
                // Q: Is still necessary to check if the type is either
                // an int or a string?
                // A: Yes, because that will tell which `operation code` should be used
                // TODO: Implement the above
                return [this.MIRArgumentToTermExpr(opBinCmp.trgt, fkey, TranslatorBosqueFStar.bool_type),
                    new term_expr_1.FuncTerm(term_expr_1.TermExpr.bin_op_to_fstar.get(opBinCmp.op), [lhs, rhs], TranslatorBosqueFStar.bool_type, fkey)];
                // return [this.MIRArgumentToTermExpr(opBinCmp.trgt, fkey, TranslatorBosqueFStar.bool_type),
                //     new FuncTerm("extractBool",
                //         [new FuncTerm((TermExpr.binOpToFStar.get(opBinCmp.op) as string), [lhs, rhs], TranslatorBosqueFStar.bool_type, fkey)],
                //         TranslatorBosqueFStar.bool_type, fkey)];
            }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRRegAssign: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRRegAssign Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRRegAssign", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRTruthyConvert: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRTruthyConvert Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRTruthyConvert", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRVarStore: {
                const opVarStore = op;
                return [this.MIRArgumentToTermExpr(opVarStore.name, fkey, this.MIRArgumentToTypeExpr(opVarStore.src, fkey)),
                    this.MIRArgumentToTermExpr(opVarStore.src, fkey, undefined)];
            }
            case mir_ops_1.MIROpTag.MIRReturnAssign: {
                const opReturnAssign = op;
                return [this.MIRArgumentToTermExpr(opReturnAssign.name, fkey, this.MIRArgumentToTypeExpr(opReturnAssign.src, fkey)),
                    this.MIRArgumentToTermExpr(opReturnAssign.src, fkey, undefined)];
            }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRAbort: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRAbort Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRAbort", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
                // Returns error
            }
            case mir_ops_1.MIROpTag.MIRDebug: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRDDebug Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRDebug", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
                // Print ignore
            }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRJump: {
                return [TranslatorBosqueFStar.skip_command, TranslatorBosqueFStar.skip_command];
            }
            case mir_ops_1.MIROpTag.MIRJumpCond: {
                return [TranslatorBosqueFStar.skip_command, TranslatorBosqueFStar.skip_command];
            }
            case mir_ops_1.MIROpTag.MIRJumpNone: {
                return [TranslatorBosqueFStar.skip_command, TranslatorBosqueFStar.skip_command];
            }
            case mir_ops_1.MIROpTag.MIRVarLifetimeStart: {
                return [TranslatorBosqueFStar.skip_command, TranslatorBosqueFStar.skip_command];
            }
            case mir_ops_1.MIROpTag.MIRVarLifetimeEnd: {
                return [TranslatorBosqueFStar.skip_command, TranslatorBosqueFStar.skip_command];
            }
            case mir_ops_1.MIROpTag.MIRPhi: { // DOUBLE CHECK
                const opPhi = op;
                const currentType = this.types_seen.get(util_1.sanitizeName(fkey + opPhi.trgt.nameID));
                const typeFromSrc = this.MIRArgumentToTypeExpr(opPhi.src.get(comingFrom), fkey);
                if (currentType == undefined) {
                    this.types_seen.set(util_1.sanitizeName(fkey + opPhi.trgt.nameID), typeFromSrc);
                }
                else {
                    if (!currentType.equalTo(typeFromSrc)) {
                        if (currentType instanceof type_expr_1.UnionType) {
                            if (typeFromSrc instanceof type_expr_1.UnionType) {
                                const previousElementsSet = new Set(Array.from(typeFromSrc.elements));
                                currentType.elements.forEach(x => previousElementsSet.add(x));
                                this.types_seen.set(util_1.sanitizeName(fkey + opPhi.trgt.nameID), new type_expr_1.UnionType(previousElementsSet));
                            }
                            else {
                                currentType.elements.add(typeFromSrc);
                                this.types_seen.set(util_1.sanitizeName(fkey + opPhi.trgt.nameID), new type_expr_1.UnionType(currentType.elements));
                            }
                        }
                        else {
                            if (typeFromSrc instanceof type_expr_1.UnionType) {
                                const previousElementsSet = new Set(Array.from(typeFromSrc.elements));
                                previousElementsSet.add(currentType);
                                this.types_seen.set(util_1.sanitizeName(fkey + opPhi.trgt.nameID), new type_expr_1.UnionType(previousElementsSet));
                            }
                            else {
                                this.types_seen.set(util_1.sanitizeName(fkey + opPhi.trgt.nameID), new type_expr_1.UnionType(new Set([typeFromSrc, currentType])));
                            }
                        }
                    }
                }
                return [this.MIRArgumentToTermExpr(opPhi.trgt, fkey, undefined),
                    this.MIRArgumentToTermExpr(opPhi.src.get(comingFrom), fkey, undefined)];
            }
            case mir_ops_1.MIROpTag.MIRIsTypeOfNone: {
                const opIsTypeOfNone = op;
                return [this.MIRArgumentToTermExpr(opIsTypeOfNone.trgt, fkey, TranslatorBosqueFStar.bool_type),
                    new term_expr_1.FuncTerm("isNoneBosque", [this.MIRArgumentToTermExpr(opIsTypeOfNone.arg, fkey, undefined)], TranslatorBosqueFStar.bool_type, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRIsTypeOfSome: {
                const opIsTypeOfSome = op;
                return [this.MIRArgumentToTermExpr(opIsTypeOfSome.trgt, fkey, TranslatorBosqueFStar.bool_type),
                    new term_expr_1.FuncTerm("isSomeBosque", [this.MIRArgumentToTermExpr(opIsTypeOfSome.arg, fkey, undefined)], TranslatorBosqueFStar.bool_type, fkey)];
            }
            // ---------------------------------------------------------------------------------------------------
            case mir_ops_1.MIROpTag.MIRIsTypeOf: { // IMPLEMENT:
                TranslatorBosqueFStar.debugging("MIRIsTypeOf Not implemented yet", TranslatorBosqueFStar.DEBUGGING);
                return [new term_expr_1.VarTerm("_MIRIsTypeOf", TranslatorBosqueFStar.int_type, fkey), new term_expr_1.ConstTerm("0", TranslatorBosqueFStar.int_type, fkey)];
            }
            case mir_ops_1.MIROpTag.MIRAccessConstantValue: {
                const opAccessConstantValue = op;
                return [this.MIRArgumentToTermExpr(opAccessConstantValue.trgt, fkey, this.MIRArgumentToTypeExpr(util_1.sanitizeName(opAccessConstantValue.ckey), "")),
                    this.MIRArgumentToTermExpr(opAccessConstantValue.ckey, "", undefined)
                ];
            }
            // ---------------------------------------------------------------------------------------------------
            default:
                console.log(op);
                throw new Error("Operation " + op + " not defined");
        }
    }
    opsToExpr(ops, comingFrom, fkey, program) {
        if (ops.length == 0) {
            return program();
        }
        else {
            const result = this.opToAssignment(ops[0], comingFrom, fkey);
            if (result[0] instanceof term_expr_1.VarTerm) {
                const [lval, rval] = result;
                if (lval.symbol_name == "_skip") {
                    return this.opsToExpr(ops.slice(1), comingFrom, fkey, program);
                }
                else {
                    return new expression_expr_1.AssignmentExpr(lval, rval, this.opsToExpr(ops.slice(1), comingFrom, fkey, program));
                }
            }
            else {
                return result
                    .reduce((rest_expression, current_assignment) => new expression_expr_1.AssignmentExpr(current_assignment[0], current_assignment[1], rest_expression), this.opsToExpr(ops.slice(1), comingFrom, fkey, program));
            }
        }
    }
    collectExpr(fkey) {
        const declarations = this.func_declarations.get(fkey);
        const map_blocks = declarations.body.body;
        // ---------------------------------------------------------
        // Checking vtypes -----------------------------------------
        // const valueTypes = (declarations.body as MIRBody).vtypes;
        // console.log(`Inside ${fkey}`);
        // console.log(valueTypes);
        // console.log("\n");
        // ---------------------------------------------------------
        if (typeof (map_blocks) === "string") {
            throw new Error("The program with fkey " + fkey + " is just a string");
        }
        else {
            declarations.params.map(x => this.types_seen.set(util_1.sanitizeName(fkey + x.name), TranslatorBosqueFStar.stringVarToTypeExpr(x.type)));
            const return_type = TranslatorBosqueFStar.stringVarToTypeExpr(declarations.resultType);
            const flow = mir_info_1.computeBlockLinks(map_blocks);
            // console.log("More detailed Blocks:---------------------------------------------------------");
            // map_blocks.forEach(x => console.log(x));
            // console.log("More detailed++ Blocks:-------------------------------------------------------");
            // map_blocks.forEach(x => console.log(x.jsonify()));
            const traverse = (block, comingFrom) => {
                const current_flow = flow.get(block.label);
                console.assert(block.ops.length > 0);
                switch (current_flow.succs.size) {
                    case 0: {
                        const last_op = block.ops[block.ops.length - 1];
                        console.assert(last_op != undefined);
                        const reg_name = util_1.sanitizeName(last_op.name.nameID);
                        const continuation = () => new expression_expr_1.ReturnExpr(new term_expr_1.VarTerm(reg_name, return_type, fkey));
                        return this.opsToExpr(block.ops, comingFrom, fkey, continuation);
                    }
                    case 1: {
                        const successor_label = current_flow.succs.values().next().value;
                        const continuation = () => traverse(map_blocks.get(successor_label), block.label);
                        return this.opsToExpr(block.ops.slice(0, -1), comingFrom, fkey, continuation);
                    }
                    case 2: {
                        const jump_cond_op = block.ops[block.ops.length - 1];
                        const reg_name = util_1.sanitizeName(jump_cond_op.arg.nameID);
                        const condition = new term_expr_1.VarTerm(reg_name, TranslatorBosqueFStar.bool_type, fkey);
                        const branch_true = traverse(map_blocks.get(jump_cond_op.trueblock), block.label);
                        const branch_false = traverse(map_blocks.get(jump_cond_op.falseblock), block.label);
                        const continuation = () => new expression_expr_1.ConditionalExpr(condition, branch_true, branch_false);
                        return this.opsToExpr(block.ops.slice(0, -1), comingFrom, fkey, continuation);
                    }
                    default: {
                        throw new Error("Wrong Control-Flow graph. The out-degree of any node cannot be more than 2 in block: " + block);
                    }
                }
            };
            if (!this.is_fkey_declared.has(fkey)) {
                this.is_fkey_declared.add(fkey);
                this.function_declarations.push(new FunctionDeclaration(declarations, traverse(map_blocks.get("entry"), "entry")));
            }
        }
    }
    generateFStarCode(fkey) {
        const user_defined_types_map = new Map([...TranslatorBosqueFStar.concept_declarations, ...TranslatorBosqueFStar.entity_declarations]);
        const user_defined_types = this.extractProvidesRelation(user_defined_types_map);
        // --------------------------------------------------------------------------------------------------------------
        // BosqueTypes files
        bosqueTypesFST_1.printBosqueTypesFST(this.fstar_files_directory, user_defined_types);
        // --------------------------------------------------------------------------------------------------------------
        // ---------------------------------------------------------------------
        // BosqueTerms files
        bosqueTermsFST_1.printBosqueTermsFST(this.fstar_files_directory, user_defined_types_map);
        // ---------------------------------------------------------------------
        // The following stores the types of constant declarations
        // in types_seen
        this.constant_declarations.forEach(const_decl => {
            if (const_decl.value.vtypes instanceof Map) {
                const local_vtypes = const_decl.value.vtypes;
                this.types_seen.set(util_1.sanitizeName(const_decl.cname), TranslatorBosqueFStar.stringVarToTypeExpr(local_vtypes.get("_return_")));
            }
        });
        const fd = FS.openSync(this.fstar_files_directory + "/" + this.file_name, 'w');
        this.collectExpr(fkey);
        // --------------------------------------------------------------------------------------------------
        // Main file
        // --------------------------------------------------------
        // Prelude
        FS.writeSync(fd, `module ${this.file_name.slice(0, -4)}\n\n`);
        FS.writeSync(fd, `open Sequence\n`);
        FS.writeSync(fd, `open List\n`);
        FS.writeSync(fd, `open BosqueTypes\n`);
        FS.writeSync(fd, `open BosqueTerms\n`);
        FS.writeSync(fd, `open BosqueCollections\n`);
        FS.writeSync(fd, `open Util\n`);
        FS.writeSync(fd, "\n");
        // --------------------------------------------------------
        // ------------------------------------
        FS.writeSync(fd, "(* Type names *)\n");
        type_expr_1.TypeExpr.declareTypeNames(fd);
        FS.writeSync(fd, "\n");
        // ------------------------------------
        // --------------------------------------------------------------------------------------------------
        // The following emits declaration of constant
        // in FStar
        FS.writeSync(fd, "(* Constant Declarations *)\n");
        this.constant_declarations.forEach(constant_decl => {
            // Constant declaration generally have only two blocks: entry and exit
            // We just `declare` the entry block
            constant_decl.value.body.forEach(basicBlock => {
                if (basicBlock.label == "entry") {
                    const return_type = TranslatorBosqueFStar.stringVarToTypeExpr(constant_decl.declaredType);
                    const continuation = () => new expression_expr_1.ReturnExpr(new term_expr_1.VarTerm("__ir_ret__", return_type, fkey));
                    this.types_seen.set(util_1.sanitizeName(constant_decl.cname), return_type);
                    FS.writeSync(fd, `let ${util_1.sanitizeName(constant_decl.cname)} =\
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
    runFStarCode(z3rlimit, max_fuel, max_ifuel) {
        const fstar_command = `fstar.exe ${this.file_name} --z3refresh --z3rlimit ${z3rlimit}\
    --max_fuel ${max_fuel} --max_ifuel ${max_ifuel} --include ${this.fstar_files_directory} --log_queries`;
        console.log(`Using the following command: ${fstar_command}`);
        ChildProcess.execSync(fstar_command);
        ChildProcess.execSync(`mv queries-${this.file_name.replace("fst", "smt2")} ${this.fstar_files_directory}`);
    }
}
exports.TranslatorBosqueFStar = TranslatorBosqueFStar;
TranslatorBosqueFStar.any_type = new type_expr_1.AnyType();
TranslatorBosqueFStar.some_type = new type_expr_1.SomeType();
TranslatorBosqueFStar.truthy_type = new type_expr_1.TruthyType();
TranslatorBosqueFStar.none_type = new type_expr_1.NoneType();
TranslatorBosqueFStar.parsable_type = new type_expr_1.ParsableType();
TranslatorBosqueFStar.bool_type = new type_expr_1.BoolType();
TranslatorBosqueFStar.int_type = new type_expr_1.IntType();
TranslatorBosqueFStar.guid_type = new type_expr_1.GUIDType();
TranslatorBosqueFStar.object_type = new type_expr_1.ObjectType();
TranslatorBosqueFStar.string_type = new type_expr_1.TypedStringType(TranslatorBosqueFStar.any_type);
TranslatorBosqueFStar.skip_command = new term_expr_1.VarTerm("_skip", TranslatorBosqueFStar.bool_type, "_global");
TranslatorBosqueFStar.DEBUGGING = true;
TranslatorBosqueFStar.fresh_count = 0;
class FunctionDeclaration {
    constructor(declarations, program) {
        this.declarations = declarations;
        this.program = program;
    }
    print(fd) {
        const fkey = this.declarations.key;
        const args = this.declarations.params.map(x => x.name);
        const _type = new type_expr_1.FuncType(this.declarations.params.map(x => TranslatorBosqueFStar.stringVarToTypeExpr(x.type)), TranslatorBosqueFStar.stringVarToTypeExpr(this.declarations.resultType));
        // TODO: Figure out how to include the following fields:
        // 1) recursive, 2) preconditions, 3) postconditions
        FS.writeSync(fd, `val ${util_1.sanitizeName(fkey)} : ${_type.valDeclare()}\n`);
        FS.writeSync(fd, `let ${util_1.sanitizeName(fkey)} ${args.join(" ")} = \n${this.program.toML(1, 1)}\n\n`);
    }
}
//# sourceMappingURL=translator_bosque_fstar.js.map