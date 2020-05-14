"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const mir_assembly_1 = require("../../compiler/mir_assembly");
const smt_exp_1 = require("./smt_exp");
const assert = require("assert");
class SMTTypeEmitter {
    constructor(assembly) {
        this.tempconvctr = 0;
        this.mangledNameMap = new Map();
        this.conceptSubtypeRelation = new Map();
        this.assembly = assembly;
        this.anyType = assembly.typeMap.get("NSCore::Any");
        this.noneType = assembly.typeMap.get("NSCore::None");
        this.boolType = assembly.typeMap.get("NSCore::Bool");
        this.intType = assembly.typeMap.get("NSCore::Int");
        this.stringType = assembly.typeMap.get("NSCore::String");
        this.keyType = assembly.typeMap.get("NSCore::KeyType");
    }
    mangleStringForSMT(name) {
        if (!this.mangledNameMap.has(name)) {
            const cleanname = name.replace(/\W/g, "_").toLowerCase() + "I" + this.mangledNameMap.size + "I";
            this.mangledNameMap.set(name, cleanname);
        }
        return this.mangledNameMap.get(name);
    }
    getMIRType(tkey) {
        return this.assembly.typeMap.get(tkey);
    }
    isSimpleNoneType(tt) {
        return (tt.options.length === 1) && tt.options[0].trkey === "NSCore::None";
    }
    isSimpleBoolType(tt) {
        return (tt.options.length === 1) && tt.options[0].trkey === "NSCore::Bool";
    }
    isSimpleIntType(tt) {
        return (tt.options.length === 1) && tt.options[0].trkey === "NSCore::Int";
    }
    isSimpleStringType(tt) {
        return (tt.options.length === 1) && tt.options[0].trkey === "NSCore::String";
    }
    isKeyType(tt) {
        return tt.options.every((topt) => {
            if (topt.trkey === "NSCore::KeyType") {
                return true;
            }
            if (!(topt instanceof mir_assembly_1.MIREntityType)) {
                return false;
            }
            const eopt = topt;
            if (eopt.ekey === "NSCore::None" || eopt.ekey === "NSCore::Bool" || eopt.ekey === "NSCore::Int" || eopt.ekey === "NSCore::String" || eopt.ekey === "NSCore::GUID") {
                return true;
            }
            if (eopt.ekey.startsWith("NSCore::StringOf<")) {
                return true;
            }
            const edecl = this.assembly.entityDecls.get(eopt.ekey);
            if (edecl.provides.includes("NSCore::Enum") || edecl.provides.includes("NSCore::IdKey")) {
                return true;
            }
            return false;
        });
    }
    isTupleType(tt) {
        return tt.options.every((opt) => opt instanceof mir_assembly_1.MIRTupleType);
    }
    isKnownLayoutTupleType(tt) {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof mir_assembly_1.MIRTupleType)) {
            return false;
        }
        const tup = tt.options[0];
        return !tup.entries.some((entry) => entry.isOptional);
    }
    isRecordType(tt) {
        return tt.options.every((opt) => opt instanceof mir_assembly_1.MIRRecordType);
    }
    isKnownLayoutRecordType(tt) {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof mir_assembly_1.MIRRecordType)) {
            return false;
        }
        const tup = tt.options[0];
        return !tup.entries.some((entry) => entry.isOptional);
    }
    isUEntityType(tt) {
        const ropts = tt.options.filter((opt) => opt.trkey !== "NSCore::None");
        if (ropts.length !== 1 || !(ropts[0] instanceof mir_assembly_1.MIREntityType)) {
            return false;
        }
        const et = ropts[0];
        const tdecl = this.assembly.entityDecls.get(et.ekey);
        return !this.isSpecialRepType(tdecl);
    }
    isUCollectionType(tt) {
        const ropts = tt.options.filter((opt) => opt.trkey !== "NSCore::None");
        if (ropts.length !== 1 || !(ropts[0] instanceof mir_assembly_1.MIREntityType)) {
            return false;
        }
        const et = ropts[0];
        return (et.ekey.startsWith("NSCore::List<") || et.ekey.startsWith("NSCore::Set<") || et.ekey.startsWith("NSCore::Map<"));
    }
    isUKeyListType(tt) {
        const ropts = tt.options.filter((opt) => opt.trkey !== "NSCore::None");
        if (ropts.length !== 1 || !(ropts[0] instanceof mir_assembly_1.MIREntityType)) {
            return false;
        }
        const et = ropts[0];
        return et.ekey === "NSCore::KeyList";
    }
    isSpecialKeyListRepType(et) {
        return et.tkey === "NSCore::KeyList";
    }
    isSpecialCollectionRepType(et) {
        return (et.tkey.startsWith("NSCore::List<") || et.tkey.startsWith("NSCore::Set<") || et.tkey.startsWith("NSCore::Map<"));
    }
    isListType(tt) {
        return tt.trkey.startsWith("NSCore::List<");
    }
    isSetType(tt) {
        return tt.trkey.startsWith("NSCore::Set<");
    }
    isMapType(tt) {
        return tt.trkey.startsWith("NSCore::Map<");
    }
    isSpecialRepType(et) {
        if (et.tkey === "NSCore::None" || et.tkey === "NSCore::Bool" || et.tkey === "NSCore::Int" || et.tkey === "NSCore::String" || et.tkey === "NSCore::GUID" || et.tkey === "NSCore::Regex") {
            return true;
        }
        if (et.tkey.startsWith("NSCore::StringOf<") || et.tkey.startsWith("NSCore::PODBuffer<")) {
            return true;
        }
        if (et.provides.includes("NSCore::Enum") || et.provides.includes("NSCore::IdKey")) {
            return true;
        }
        return false;
    }
    static getTupleTypeMaxLength(tt) {
        return Math.max(...tt.options.filter((opt) => opt instanceof mir_assembly_1.MIRTupleType).map((opt) => opt.entries.length));
    }
    static getKnownLayoutTupleType(tt) {
        return tt.options[0];
    }
    static getRecordTypeMaxPropertySet(tt) {
        let popts = new Set();
        tt.options.filter((opt) => opt instanceof mir_assembly_1.MIRRecordType).forEach((opt) => opt.entries.forEach((entry) => popts.add(entry.name)));
        return [...popts].sort();
    }
    static getKnownLayoutRecordType(tt) {
        return tt.options[0];
    }
    static getUEntityType(tt) {
        return tt.options.filter((opt) => opt.trkey !== "NSCore::None")[0];
    }
    initializeConceptSubtypeRelation() {
        this.assembly.typeMap.forEach((tt) => {
            if (tt instanceof mir_assembly_1.MIRConceptType) {
                const est = [...this.assembly.entityDecls].map((edecl) => this.getMIRType(edecl[0])).filter((et) => this.assembly.subtypeOf(et, tt));
                const keyarray = est.map((et) => et.trkey).sort();
                this.conceptSubtypeRelation.set(tt.trkey, keyarray);
            }
        });
    }
    getSubtypesArrayCount(tt) {
        return this.conceptSubtypeRelation.get(tt.trkey).length;
    }
    generateRecordTypePropertyName(tt) {
        const pnames = SMTTypeEmitter.getRecordTypeMaxPropertySet(tt);
        if (pnames.length === 0) {
            return "empty";
        }
        else {
            return this.mangleStringForSMT(`{${pnames.join(", ")}}`);
        }
    }
    typeToSMTCategory(ttype) {
        if (this.isSimpleBoolType(ttype)) {
            return "Bool";
        }
        else if (this.isSimpleIntType(ttype)) {
            return "Int";
        }
        else if (this.isSimpleStringType(ttype)) {
            return "String";
        }
        else if (this.isTupleType(ttype)) {
            return "bsqtuple_" + SMTTypeEmitter.getTupleTypeMaxLength(ttype);
        }
        else if (this.isRecordType(ttype)) {
            return "bsqrecord_" + this.generateRecordTypePropertyName(ttype);
        }
        else if (this.isKeyType(ttype)) {
            return "BKeyValue";
        }
        else if (this.isUEntityType(ttype)) {
            if (this.isUCollectionType(ttype)) {
                if (this.isListType(ttype)) {
                    return "bsqlist";
                }
                else {
                    return "bsqkvcontainer";
                }
            }
            else if (this.isUKeyListType(ttype)) {
                return "bsqkeylist";
            }
            else {
                return this.mangleStringForSMT(SMTTypeEmitter.getUEntityType(ttype).ekey);
            }
        }
        else {
            return "BTerm";
        }
    }
    coerce(exp, from, into) {
        if (this.typeToSMTCategory(from) === this.typeToSMTCategory(into)) {
            return exp;
        }
        if (from.trkey === "NSCore::None") {
            if (this.isKeyType(into)) {
                return new smt_exp_1.SMTValue(`bsqkey_none`);
            }
            else if (this.isUEntityType(into)) {
                return new smt_exp_1.SMTValue(this.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(into).ekey));
            }
            else {
                return new smt_exp_1.SMTValue("(bsqterm_key bsqkey_none)");
            }
        }
        else if (this.isSimpleBoolType(from)) {
            if (this.isKeyType(into)) {
                return new smt_exp_1.SMTValue(`(bsqkey_bool ${exp.emit()})`);
            }
            else {
                return new smt_exp_1.SMTValue(`(bsqterm_key (bsqkey_bool ${exp.emit()}))`);
            }
        }
        else if (this.isSimpleIntType(from)) {
            if (this.isKeyType(into)) {
                return new smt_exp_1.SMTValue(`(bsqkey_int ${exp.emit()})`);
            }
            else {
                return new smt_exp_1.SMTValue(`(bsqterm_key (bsqkey_int ${exp.emit()}))`);
            }
        }
        else if (this.isSimpleStringType(from)) {
            if (this.isKeyType(into)) {
                return new smt_exp_1.SMTValue(`(bsqkey_string ${exp.emit()})`);
            }
            else {
                return new smt_exp_1.SMTValue(`(bsqterm_key (bsqkey_string ${exp.emit()}))`);
            }
        }
        else if (this.isKeyType(from)) {
            if (this.isSimpleBoolType(into)) {
                return new smt_exp_1.SMTValue(`(bsqkey_bool_value ${exp.emit()})`);
            }
            else if (this.isSimpleIntType(into)) {
                return new smt_exp_1.SMTValue(`(bsqkey_int_value ${exp.emit()})`);
            }
            else if (this.isSimpleStringType(into)) {
                return new smt_exp_1.SMTValue(`(bsqkey_string_value ${exp.emit()})`);
            }
            else if (this.isUEntityType(into)) {
                //the only possible overlap is in the none type so just provide that
                return new smt_exp_1.SMTValue(`bsqkey_none`);
            }
            else {
                return new smt_exp_1.SMTValue(`(bsqterm_key ${exp.emit()})`);
            }
        }
        else if (this.isTupleType(from)) {
            const fromsize = SMTTypeEmitter.getTupleTypeMaxLength(from);
            if (this.isTupleType(into)) {
                const intosize = SMTTypeEmitter.getTupleTypeMaxLength(into);
                const intocons = this.generateTupleConstructor(into);
                if (intosize === 0) {
                    return new smt_exp_1.SMTValue(intocons);
                }
                else {
                    let temp = `@tmpconv_${this.tempconvctr++}`;
                    let args = [];
                    for (let i = 0; i < Math.min(intosize, fromsize); ++i) {
                        args.push(`(${this.generateTupleAccessor(from, i)} ${temp})`);
                    }
                    for (let i = Math.min(intosize, fromsize); i < intosize; ++i) {
                        args.push("bsqterm@clear");
                    }
                    return new smt_exp_1.SMTLet(temp, exp, new smt_exp_1.SMTValue(`(${intocons} ${args.join(" ")})`));
                }
            }
            else {
                if (fromsize === 0) {
                    return new smt_exp_1.SMTValue(`(bsqterm_tuple bsqtuple_array_empty)`);
                }
                else {
                    let temp = `@tmpconv_${this.tempconvctr++}`;
                    let tuparray = "bsqtuple_array_empty";
                    for (let i = 0; i < fromsize; ++i) {
                        tuparray = `(store ${tuparray} ${i} (${this.generateTupleAccessor(from, i)} ${temp}))`;
                    }
                    return new smt_exp_1.SMTLet(temp, exp, new smt_exp_1.SMTValue(`(bsqterm_tuple ${tuparray})`));
                }
            }
        }
        else if (this.isRecordType(from)) {
            const fromset = SMTTypeEmitter.getRecordTypeMaxPropertySet(from);
            if (this.isRecordType(into)) {
                const intoset = SMTTypeEmitter.getRecordTypeMaxPropertySet(into);
                const intocons = this.generateRecordConstructor(into);
                if (intoset.length === 0) {
                    return new smt_exp_1.SMTValue(intocons);
                }
                else {
                    let temp = `@tmpconv_${this.tempconvctr++}`;
                    let args = [];
                    for (let i = 0; i < intoset.length; ++i) {
                        const p = intoset[i];
                        if (fromset.includes(p)) {
                            args.push(`(${this.generateRecordAccessor(from, p)} ${temp})`);
                        }
                        else {
                            args.push("bsqterm@clear");
                        }
                    }
                    return new smt_exp_1.SMTLet(temp, exp, new smt_exp_1.SMTValue(`(${intocons} ${args.join(" ")})`));
                }
            }
            else {
                if (fromset.length === 0) {
                    return new smt_exp_1.SMTValue(`(bsqterm_record bsqrecord_array_empty)`);
                }
                else {
                    let temp = `@tmpconv_${this.tempconvctr++}`;
                    let tuparray = "bsqrecord_array_empty";
                    for (let i = 0; i < fromset.length; ++i) {
                        tuparray = `(store ${tuparray} "${fromset[i]}" (${this.generateRecordAccessor(from, fromset[i])} ${temp}))`;
                    }
                    return new smt_exp_1.SMTLet(temp, exp, new smt_exp_1.SMTValue(`(bsqterm_record ${tuparray})`));
                }
            }
        }
        else if (this.isUEntityType(from)) {
            const fromtype = this.assembly.entityDecls.get(SMTTypeEmitter.getUEntityType(from).ekey);
            if (this.isUCollectionType(from)) {
                let nonnone = undefined;
                if (this.isListType(from)) {
                    nonnone = new smt_exp_1.SMTValue(`(bsqterm_list "${fromtype.tkey}" ${exp.emit()})`);
                }
                else {
                    nonnone = new smt_exp_1.SMTValue(`(bsqterm_kvcontainer "${fromtype.tkey}" ${exp.emit()})`);
                }
                if (this.isKeyType(into)) {
                    //the only possible overlap is in the none type so just provide that
                    return new smt_exp_1.SMTValue(`bsqkey_none`);
                }
                else {
                    if (!this.assembly.subtypeOf(this.noneType, from)) {
                        return nonnone;
                    }
                    else {
                        const isnonetest = new smt_exp_1.SMTValue(`(is-${this.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(from).ekey)} ${exp.emit()})`);
                        return new smt_exp_1.SMTCond(isnonetest, new smt_exp_1.SMTValue("(bsqterm_key bsqkey_none)"), nonnone);
                    }
                }
            }
            else {
                let temp = `@tmpconv_${this.tempconvctr++}`;
                let entarray = "bsqentity_array_empty";
                for (let i = 0; i < fromtype.fields.length; ++i) {
                    const fd = fromtype.fields[i];
                    const access = `(${this.generateEntityAccessor(fromtype.tkey, fd.fkey)} ${temp})`;
                    entarray = `(store ${entarray} "${fd.fkey}" ${this.coerce(new smt_exp_1.SMTValue(access), this.getMIRType(fd.declaredType), this.anyType).emit()})`;
                }
                const nonnone = new smt_exp_1.SMTLet(temp, exp, new smt_exp_1.SMTValue(`(bsqterm_object "${fromtype.tkey}" ${entarray})`));
                if (this.isKeyType(into)) {
                    //the only possible overlap is in the none type so just provide that
                    return new smt_exp_1.SMTValue(`bsqkey_none`);
                }
                else {
                    if (!this.assembly.subtypeOf(this.noneType, from)) {
                        return nonnone;
                    }
                    else {
                        const isnonetest = new smt_exp_1.SMTValue(`(is-${this.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(from).ekey)} ${exp.emit()})`);
                        return new smt_exp_1.SMTCond(isnonetest, new smt_exp_1.SMTValue("(bsqterm_key bsqkey_none)"), nonnone);
                    }
                }
            }
        }
        else {
            assert(this.typeToSMTCategory(from) === "BTerm", "must be a BTerm mapped type");
            if (this.isSimpleBoolType(into)) {
                return new smt_exp_1.SMTValue(`(bsqkey_bool_value (bsqterm_key_value ${exp.emit()}))`);
            }
            else if (this.isSimpleIntType(into)) {
                return new smt_exp_1.SMTValue(`(bsqkey_int_value (bsqterm_key_value ${exp.emit()}))`);
            }
            else if (this.isSimpleStringType(into)) {
                return new smt_exp_1.SMTValue(`(bsqkey_string_value (bsqterm_key_value ${exp.emit()}))`);
            }
            else if (this.isKeyType(into)) {
                return new smt_exp_1.SMTValue(`(bsqterm_key_value ${exp.emit()})`);
            }
            else if (this.isTupleType(into)) {
                const intosize = SMTTypeEmitter.getTupleTypeMaxLength(into);
                let temp = `@tmpconv_${this.tempconvctr++}`;
                let args = [];
                for (let i = 0; i < intosize; ++i) {
                    args.push(`(select ${temp} ${i})`);
                }
                return new smt_exp_1.SMTLet(temp, new smt_exp_1.SMTValue(`(bsqterm_tuple_entries ${exp.emit()})`), new smt_exp_1.SMTValue(`(${this.generateTupleConstructor(into)} ${args.join(" ")})`));
            }
            else if (this.isRecordType(into)) {
                const intoset = SMTTypeEmitter.getRecordTypeMaxPropertySet(into);
                let temp = `@tmpconv_${this.tempconvctr++}`;
                let args = [];
                for (let i = 0; i < intoset.length; ++i) {
                    args.push(`(select ${temp} "${intoset[i]}")`);
                }
                return new smt_exp_1.SMTLet(temp, new smt_exp_1.SMTValue(`(bsqterm_record_entries ${exp.emit()})`), new smt_exp_1.SMTValue(`(${this.generateRecordConstructor(into)} ${args.join(" ")})`));
            }
            else if (this.isUEntityType(into)) {
                const intotype = this.assembly.entityDecls.get(SMTTypeEmitter.getUEntityType(into).ekey);
                if (this.isUCollectionType(into)) {
                    let nonnone = undefined;
                    if (this.isListType(into)) {
                        nonnone = new smt_exp_1.SMTValue(`(bsqterm_list_entry ${exp.emit()})`);
                    }
                    else {
                        nonnone = new smt_exp_1.SMTValue(`(bsqterm_bsqkvcontainer_entry ${exp.emit()})`);
                    }
                    if (!this.assembly.subtypeOf(this.noneType, into)) {
                        return nonnone;
                    }
                    else {
                        const isnonetest = new smt_exp_1.SMTValue(`(= (bsqterm_key bsqkey_none) ${exp.emit()})`);
                        return new smt_exp_1.SMTCond(isnonetest, new smt_exp_1.SMTValue(this.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(into).ekey)), nonnone);
                    }
                }
                else {
                    let temp = `@tmpconv_${this.tempconvctr++}`;
                    let args = [];
                    for (let i = 0; i < intotype.fields.length; ++i) {
                        args.push(this.coerce(new smt_exp_1.SMTValue(`(select ${temp} "${intotype.fields[i].fkey}")`), this.anyType, this.getMIRType(intotype.fields[i].declaredType)).emit());
                    }
                    const nonnone = new smt_exp_1.SMTLet(temp, new smt_exp_1.SMTValue(`(bsqterm_object_entries ${exp.emit()})`), new smt_exp_1.SMTValue(`(${this.generateEntityConstructor(intotype.tkey)} ${args.join(" ")})`));
                    if (!this.assembly.subtypeOf(this.noneType, into)) {
                        return nonnone;
                    }
                    else {
                        const isnonetest = new smt_exp_1.SMTValue(`(= (bsqterm_key bsqkey_none) ${exp.emit()})`);
                        return new smt_exp_1.SMTCond(isnonetest, new smt_exp_1.SMTValue(this.generateEntityNoneConstructor(SMTTypeEmitter.getUEntityType(into).ekey)), nonnone);
                    }
                }
            }
            else {
                return exp;
            }
        }
    }
    generateTupleConstructor(ttype) {
        return `bsqtuple_${SMTTypeEmitter.getTupleTypeMaxLength(ttype)}@cons`;
    }
    generateTupleAccessor(ttype, idx) {
        return `bsqtuple_${SMTTypeEmitter.getTupleTypeMaxLength(ttype)}@${idx}`;
    }
    generateRecordConstructor(ttype) {
        return `bsqrecord_${this.generateRecordTypePropertyName(ttype)}@cons`;
    }
    generateRecordAccessor(ttype, p) {
        return `bsqrecord_${this.generateRecordTypePropertyName(ttype)}@${p}`;
    }
    generateSMTEntity(entity) {
        if (this.isSpecialRepType(entity) || this.isSpecialCollectionRepType(entity) || this.isSpecialKeyListRepType(entity)) {
            return undefined;
        }
        const ename = this.mangleStringForSMT(entity.tkey);
        const fargs = entity.fields.map((fd) => {
            return `(${ename}@${this.mangleStringForSMT(fd.fkey)} ${this.typeToSMTCategory(this.getMIRType(fd.declaredType))})`;
        });
        return {
            fwddecl: `(${ename} 0)`,
            fulldecl: `( (${this.generateEntityNoneConstructor(entity.tkey)}) (cons@${ename} ${fargs.join(" ")}) )`
        };
    }
    generateEntityNoneConstructor(ekey) {
        if (ekey.startsWith("NSCore::List<")) {
            return "cons@bsqlist$none";
        }
        else if (ekey.startsWith("NSCore::Set<")) {
            return "cons@bsqkvcontainer$none";
        }
        else if (ekey.startsWith("NSCore::Map<")) {
            return "cons@bsqkvcontainer$none";
        }
        else if (ekey === "NSCore::KeyList") {
            return "cons@bsqkeylist$none";
        }
        else {
            return `cons@${this.mangleStringForSMT(ekey)}$none`;
        }
    }
    generateEntityConstructor(ekey) {
        if (ekey.startsWith("NSCore::List<")) {
            return "cons@bsqlist";
        }
        else if (ekey.startsWith("NSCore::Set<")) {
            return "cons@bsqkvcontainer";
        }
        else if (ekey.startsWith("NSCore::Map<")) {
            return "cons@bsqkvcontainer";
        }
        else if (ekey === "NSCore::KeyList") {
            return "cons@bsqkeylist";
        }
        else {
            return `cons@${this.mangleStringForSMT(ekey)}`;
        }
    }
    generateEntityAccessor(ekey, f) {
        return `${this.mangleStringForSMT(ekey)}@${this.mangleStringForSMT(f)}`;
    }
}
exports.SMTTypeEmitter = SMTTypeEmitter;
//# sourceMappingURL=smttype_emitter.js.map