"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const mir_assembly_1 = require("../../compiler/mir_assembly");
const assert = require("assert");
class CPPTypeEmitter {
    constructor(assembly) {
        this.mangledNameMap = new Map();
        this.scopectr = 0;
        this.conceptSubtypeRelation = new Map();
        this.assembly = assembly;
        this.anyType = assembly.typeMap.get("NSCore::Any");
        this.noneType = assembly.typeMap.get("NSCore::None");
        this.boolType = assembly.typeMap.get("NSCore::Bool");
        this.intType = assembly.typeMap.get("NSCore::Int");
        this.stringType = assembly.typeMap.get("NSCore::String");
    }
    mangleStringForCpp(name) {
        if (!this.mangledNameMap.has(name)) {
            const cleanname = name.replace(/\W/g, "_").toLowerCase() + "I" + this.mangledNameMap.size + "I";
            this.mangledNameMap.set(name, cleanname);
        }
        return this.mangledNameMap.get(name);
    }
    getMIRType(tkey) {
        return this.assembly.typeMap.get(tkey);
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
    isKnownLayoutTupleType(tt) {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof mir_assembly_1.MIRTupleType)) {
            return false;
        }
        const tup = tt.options[0];
        return !tup.entries.some((entry) => entry.isOptional);
    }
    isTupleType(tt) {
        return tt.options.every((opt) => opt instanceof mir_assembly_1.MIRTupleType);
    }
    isKnownLayoutRecordType(tt) {
        if (tt.options.length !== 1 || !(tt.options[0] instanceof mir_assembly_1.MIRRecordType)) {
            return false;
        }
        const tup = tt.options[0];
        return !tup.entries.some((entry) => entry.isOptional);
    }
    isRecordType(tt) {
        return tt.options.every((opt) => opt instanceof mir_assembly_1.MIRRecordType);
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
    static getKnownLayoutTupleType(tt) {
        return tt.options[0];
    }
    static getTupleTypeMaxLength(tt) {
        return Math.max(...tt.options.filter((opt) => opt instanceof mir_assembly_1.MIRTupleType).map((opt) => opt.entries.length));
    }
    static getKnownLayoutRecordType(tt) {
        return tt.options[0];
    }
    static getRecordTypeMaxPropertySet(tt) {
        let popts = new Set();
        tt.options.filter((opt) => opt instanceof mir_assembly_1.MIRRecordType).forEach((opt) => opt.entries.forEach((entry) => popts.add(entry.name)));
        return [...popts].sort();
    }
    getKnownPropertyRecordArrayName(tt) {
        const name = `{ ${CPPTypeEmitter.getRecordTypeMaxPropertySet(tt).join(", ")} }`;
        return `KnownPropertySet_${this.mangleStringForCpp(name)}`;
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
    maybeRefableCountableType(tt) {
        if (tt.options.every((opt) => {
            const uname = opt.trkey;
            return (uname === "NSCore::None" || uname === "NSCore::Bool");
        })) {
            return false;
        }
        if (tt.options.length === 1 && tt.options[0] instanceof mir_assembly_1.MIREntityType && tt.options[0].trkey === "NSCore::Int") {
            return false;
        }
        if (tt.options.length === 1 && tt.options[0] instanceof mir_assembly_1.MIREntityType && this.assembly.entityDecls.get(tt.options[0].ekey).provides.includes("NSCore::Enum")) {
            return false;
        }
        if (this.isTupleType(tt) && CPPTypeEmitter.getTupleTypeMaxLength(tt) === 0) {
            return false;
        }
        if (this.isRecordType(tt) && CPPTypeEmitter.getRecordTypeMaxPropertySet(tt).length === 0) {
            return false;
        }
        return true;
    }
    typeToCPPType(ttype, declspec) {
        if (this.isSimpleBoolType(ttype)) {
            return "bool";
        }
        else if (this.isSimpleIntType(ttype)) {
            return "BSQInt";
        }
        else if (this.isSimpleStringType(ttype)) {
            return "BSQString" + (declspec !== "base" ? "*" : "");
        }
        else if (this.isTupleType(ttype)) {
            if (this.isKnownLayoutTupleType(ttype)) {
                return `BSQTupleKnown<${CPPTypeEmitter.getTupleTypeMaxLength(ttype)}>`;
            }
            else {
                return `BSQTupleFixed<${CPPTypeEmitter.getTupleTypeMaxLength(ttype)}>`;
            }
        }
        else if (this.isRecordType(ttype)) {
            if (this.isKnownLayoutRecordType(ttype)) {
                return `BSQRecordKnown<${CPPTypeEmitter.getRecordTypeMaxPropertySet(ttype).length}>`;
            }
            else {
                return `BSQRecordFixed<${CPPTypeEmitter.getRecordTypeMaxPropertySet(ttype).length}>`;
            }
        }
        else if (this.isUEntityType(ttype)) {
            if (this.isUCollectionType(ttype)) {
                if (this.isListType(ttype)) {
                    return "BSQList" + (declspec !== "base" ? "*" : "");
                }
                else if (this.isSetType(ttype)) {
                    return "BSQSet" + (declspec !== "base" ? "*" : "");
                }
                else {
                    return "BSQMap" + (declspec !== "base" ? "*" : "");
                }
            }
            else if (this.isUKeyListType(ttype)) {
                return "BSQKeyList" + (declspec !== "base" ? "*" : "");
            }
            else {
                return this.mangleStringForCpp(CPPTypeEmitter.getUEntityType(ttype).ekey) + (declspec !== "base" ? "*" : "");
            }
        }
        else {
            return "Value";
        }
    }
    typeToCPPDefaultValue(ttype) {
        if (this.isSimpleBoolType(ttype)) {
            return "false";
        }
        else if (this.isSimpleIntType(ttype)) {
            return "BSQ_VALUE_0";
        }
        else if (this.isSimpleStringType(ttype)) {
            return "nullptr";
        }
        else if (this.isTupleType(ttype)) {
            {
                if (this.isKnownLayoutTupleType(ttype)) {
                    return "{nullptr}";
                }
                else {
                    return "{nullptr}";
                }
            }
        }
        else if (this.isRecordType(ttype)) {
            if (this.isKnownLayoutRecordType(ttype)) {
                return "{std::make_pair<MIRPropertyEnum, Value>(MIRPropertyEnum::Invalid, nullptr)}";
            }
            else {
                return "{std::make_pair<MIRPropertyEnum, Value>(MIRPropertyEnum::Invalid, nullptr)}";
            }
        }
        else if (this.isUEntityType(ttype)) {
            return "nullptr";
        }
        else {
            return "nullptr";
        }
    }
    coerce(exp, from, into) {
        if (this.typeToCPPType(from, "base") === this.typeToCPPType(into, "base")) {
            return exp;
        }
        if (from.trkey === "NSCore::None") {
            return "BSQ_VALUE_NONE";
        }
        else if (this.isSimpleBoolType(from)) {
            return `BSQ_BOX_VALUE_BOOL(${exp})`;
        }
        else if (this.isSimpleIntType(from)) {
            return `BSQ_BOX_VALUE_BSQINT(${exp}, ${this.mangleStringForCpp("$scope$")}, ${this.scopectr++})`;
        }
        else if (this.isSimpleStringType(from)) {
            return exp;
        }
        else if (this.isTupleType(from)) {
            assert(!(this.isKnownLayoutTupleType(from) && this.isKnownLayoutTupleType(into)), "Shoud be a type error or handled by equality case");
            const fromsize = CPPTypeEmitter.getTupleTypeMaxLength(from);
            if (this.isKnownLayoutTupleType(from)) {
                if (this.isTupleType(into)) {
                    const intosize = CPPTypeEmitter.getTupleTypeMaxLength(into);
                    return `StructuralCoercionOps::convertTupleKnownToFixed<${intosize}, ${fromsize}>(${exp})`;
                }
                else {
                    return `${this.mangleStringForCpp("$scope$")}.addAllocRef<${this.scopectr++}, BSQTuple>(StructuralCoercionOps::boxTupleKnown<${fromsize}>(${exp}))`;
                }
            }
            else if (this.isKnownLayoutTupleType(into)) {
                const intosize = CPPTypeEmitter.getTupleTypeMaxLength(into);
                return `StructuralCoercionOps::convertTupleFixedToKnown<${intosize}, ${fromsize}>(${exp})`;
            }
            else {
                if (this.isTupleType(into)) {
                    const intosize = CPPTypeEmitter.getTupleTypeMaxLength(into);
                    if (intosize < fromsize) {
                        return `StructuralCoercionOps::projectTupleDownFixed<${intosize}, ${fromsize}>(${exp})`;
                    }
                    else {
                        return `StructuralCoercionOps::projectTupleUpFixed<${intosize}, ${fromsize}>(${exp})`;
                    }
                }
                else {
                    return `${this.mangleStringForCpp("$scope$")}.addAllocRef<${this.scopectr++}, BSQTuple>(StructuralCoercionOps::boxTupleFixed<${fromsize}>(${exp}))`;
                }
            }
        }
        else if (this.isRecordType(from)) {
            assert(!(this.isKnownLayoutRecordType(from) && this.isKnownLayoutRecordType(into)), "Shoud be a type error or handled by equality case");
            const fromset = CPPTypeEmitter.getRecordTypeMaxPropertySet(from);
            if (this.isKnownLayoutRecordType(from)) {
                if (this.isRecordType(into)) {
                    const intoset = CPPTypeEmitter.getRecordTypeMaxPropertySet(into);
                    if (intoset.length === 0) {
                        return "BSQRecordFixed_empty";
                    }
                    else {
                        if (fromset.length === 0) {
                            return `BSQRecordFixed<${intoset.length}>{0}`;
                        }
                        else {
                            return `StructuralCoercionOps::convertRecordKnownToFixed<${intoset.length}, ${fromset.length}>(${exp}, ${this.getKnownPropertyRecordArrayName(from)})`;
                        }
                    }
                }
                else {
                    if (fromset.length === 0) {
                        return "BSQRecord::_empty";
                    }
                    else {
                        return `${this.mangleStringForCpp("$scope$")}.addAllocRef<${this.scopectr++}, BSQRecord>(StructuralCoercionOps::boxRecordKnown<${fromset.length}>(${exp}, ${this.getKnownPropertyRecordArrayName(from)}))`;
                    }
                }
            }
            else if (this.isKnownLayoutRecordType(into)) {
                const intoset = CPPTypeEmitter.getRecordTypeMaxPropertySet(into);
                return `StructuralCoercionOps::convertRecordFixedToKnown<${intoset.length}, ${fromset.length}>(${exp})`;
            }
            else {
                if (this.isRecordType(into)) {
                    const intoset = CPPTypeEmitter.getRecordTypeMaxPropertySet(into);
                    if (intoset.length < fromset.length) {
                        return `StructuralCoercionOps::projectRecordDownFixed<${intoset.length}, ${fromset.length}>(${exp})`;
                    }
                    else {
                        return `StructuralCoercionOps::projectRecordUpFixed<${intoset.length}, ${fromset.length}>(${exp})`;
                    }
                }
                else {
                    return `${this.mangleStringForCpp("$scope$")}.addAllocRef<${this.scopectr++}, BSQRecord>(StructuralCoercionOps::boxRecordFixed<${fromset.length}>(${exp}))`;
                }
            }
        }
        else if (this.isUEntityType(from)) {
            return exp;
        }
        else {
            assert(this.typeToCPPType(from, "base") === "Value", "must be a Value mapped type");
            if (this.isSimpleBoolType(into)) {
                return `BSQ_GET_VALUE_BOOL(${exp})`;
            }
            else if (this.isSimpleIntType(into)) {
                return `BSQ_GET_VALUE_BSQINT(${exp})`;
            }
            else if (this.isSimpleStringType(into)) {
                return `BSQ_GET_VALUE_PTR(${exp}, BSQString)`;
            }
            else if (this.isTupleType(into)) {
                const intosize = CPPTypeEmitter.getTupleTypeMaxLength(into);
                if (this.isKnownLayoutTupleType(into)) {
                    return `StructuralCoercionOps::unboxTupleKnown<${intosize}>(BSQ_GET_VALUE_PTR(${exp}, BSQTuple))`;
                }
                else {
                    return `StructuralCoercionOps::unboxTupleFixed<${intosize}>(BSQ_GET_VALUE_PTR(${exp}, BSQTuple))`;
                }
            }
            else if (this.isRecordType(into)) {
                const intoset = CPPTypeEmitter.getRecordTypeMaxPropertySet(into);
                if (this.isKnownLayoutRecordType(into)) {
                    return `StructuralCoercionOps::unboxRecordKnown<${intoset.length}>(BSQ_GET_VALUE_PTR(${exp}, BSQRecord))`;
                }
                else {
                    return `StructuralCoercionOps::unboxRecordFixed<${intoset.length}>(BSQ_GET_VALUE_PTR(${exp}, BSQRecord))`;
                }
            }
            else if (this.isUEntityType(into)) {
                return `BSQ_GET_VALUE_PTR(${exp}, ${this.typeToCPPType(into, "base")})`;
            }
            else {
                return exp;
            }
        }
    }
    generateFixedTupleAccessor(idx) {
        return `.atFixed<${idx}>()`;
    }
    generateKnownRecordAccessor(ttype, p) {
        return `.atPropertyIndex<${CPPTypeEmitter.getKnownLayoutRecordType(ttype).entries.findIndex((entry) => entry.name === p)}>()`;
    }
    generateFixedRecordAccessor(p) {
        return `.atFixed<MIRPropertyEnum::${p}>()`;
    }
    generateConstructorArgInc(argtype, arg) {
        if (!this.maybeRefableCountableType(argtype)) {
            return arg;
        }
        if (this.isTupleType(argtype)) {
            if (this.isKnownLayoutTupleType(argtype)) {
                return `${arg}.copyWithRefInc()`;
            }
            else {
                return `${arg}.copyWithRefInc()`;
            }
        }
        else if (this.isRecordType(argtype)) {
            if (this.isKnownLayoutRecordType(argtype)) {
                return `${arg}.copyWithRefInc()`;
            }
            else {
                return `${arg}.copyWithRefInc()`;
            }
        }
        else if (this.isUEntityType(argtype)) {
            if (this.assembly.subtypeOf(this.noneType, argtype)) {
                return `BSQRef::checkedIncrementNoneable<${this.typeToCPPType(argtype, "base")}>(${arg})`;
            }
            else {
                return `BSQRef::checkedIncrementFast<${this.typeToCPPType(argtype, "base")}>(${arg})`;
            }
        }
        else {
            return `BSQRef::checkedIncrementOf<${this.typeToCPPType(argtype, "parameter")}>(${arg})`;
        }
    }
    generateCPPEntity(entity) {
        if (this.isSpecialRepType(entity) || this.isSpecialCollectionRepType(entity) || this.isSpecialKeyListRepType(entity)) {
            return undefined;
        }
        const constructor_args = entity.fields.map((fd) => {
            return `${this.typeToCPPType(this.getMIRType(fd.declaredType), "parameter")} ${fd.name}`;
        });
        const constructor_initializer = entity.fields.map((fd) => {
            return `${this.mangleStringForCpp(fd.fkey)}(${fd.name})`;
        });
        const destructor_list = entity.fields.map((fd) => {
            const ftype = this.getMIRType(fd.declaredType);
            if (!this.maybeRefableCountableType(ftype)) {
                return undefined;
            }
            if (this.isTupleType(ftype)) {
                if (this.isKnownLayoutTupleType(ftype)) {
                    return `this->${this.mangleStringForCpp(fd.fkey)}.allRefDec();`;
                }
                else {
                    return `this->${this.mangleStringForCpp(fd.fkey)}.allRefDec();`;
                }
            }
            else if (this.isRecordType(ftype)) {
                if (this.isKnownLayoutRecordType(ftype)) {
                    return `this->${this.mangleStringForCpp(fd.fkey)}.allRefDec();`;
                }
                else {
                    return `this->${this.mangleStringForCpp(fd.fkey)}.allRefDec();`;
                }
            }
            else if (this.isUEntityType(ftype)) {
                if (this.assembly.subtypeOf(this.noneType, ftype)) {
                    return `BSQRef::checkedDecrementNoneable(this->${this.mangleStringForCpp(fd.fkey)});`;
                }
                else {
                    return `BSQRef::checkedDecrementFast(this->${this.mangleStringForCpp(fd.fkey)});`;
                }
            }
            else {
                return `BSQRef::checkedDecrement(this->${this.mangleStringForCpp(fd.fkey)});`;
            }
        })
            .filter((fd) => fd !== undefined);
        const fields = entity.fields.map((fd) => {
            return `${this.typeToCPPType(this.getMIRType(fd.declaredType), "decl")} ${this.mangleStringForCpp(fd.fkey)};`;
        });
        const vfield_accessors = entity.fields.map((fd) => {
            if (fd.enclosingDecl === entity.tkey) {
                return "NA";
            }
            else {
                const fn = `this->${this.mangleStringForCpp(fd.fkey)}`;
                return `${this.typeToCPPType(this.getMIRType(fd.declaredType), "return")} get$${this.mangleStringForCpp(fd.fkey)}() { return ${fn}; };`;
            }
        });
        const vcalls = [...entity.vcallMap].map((callp) => {
            const rcall = (this.assembly.invokeDecls.get(callp[1]) || this.assembly.primitiveInvokeDecls.get(callp[1]));
            if (rcall.enclosingDecl === entity.tkey) {
                return "NA";
            }
            else {
                const resulttype = this.getMIRType(rcall.resultType);
                const rtype = this.typeToCPPType(resulttype, "return");
                const vargs = rcall.params.slice(1).map((fp) => `${this.typeToCPPType(this.getMIRType(fp.type), "parameter")} ${fp.name}`);
                const cargs = rcall.params.map((fp) => fp.name);
                if (this.maybeRefableCountableType(resulttype)) {
                    if (this.isTupleType(resulttype)) {
                        const maxlen = CPPTypeEmitter.getTupleTypeMaxLength(resulttype);
                        for (let i = 0; i < maxlen; ++i) {
                            vargs.push(`BSQRef** $callerslot$${i}`);
                            cargs.push(`$callerslot$${i}`);
                        }
                    }
                    else if (this.isRecordType(resulttype)) {
                        const allprops = CPPTypeEmitter.getRecordTypeMaxPropertySet(resulttype);
                        for (let i = 0; i < allprops.length; ++i) {
                            vargs.push(`BSQRef** $callerslot$${allprops[i]}`);
                            cargs.push(`$callerslot$${allprops[i]}`);
                        }
                    }
                    else {
                        vargs.push("BSQRef** $callerslot$");
                        cargs.push("$callerslot$");
                    }
                }
                return `${rtype} ${this.mangleStringForCpp(callp[0])}(${vargs.join(", ")})\n`
                    + "    {\n"
                    + `        return ${this.mangleStringForCpp(callp[1])}(${cargs.join(", ")});\n`
                    + "    }\n";
            }
        });
        this.scopectr = 0;
        const faccess = entity.fields.map((f) => this.coerce(`this->${this.mangleStringForCpp(f.fkey)}`, this.getMIRType(f.declaredType), this.anyType));
        const fjoins = faccess.length !== 0 ? faccess.map((fa) => `Runtime::diagnostic_format(${fa})`).join(" + std::u32string(U\", \") + ") : "U\" \"";
        const display = "std::u32string display() const\n"
            + "    {\n"
            + (this.scopectr !== 0 ? `        BSQRefScope<${this.scopectr}> ${this.mangleStringForCpp("$scope$")};\n` : "")
            + `        return std::u32string(U"${entity.tkey}{ ") + ${fjoins} + std::u32string(U" }");\n`
            + "    }";
        return {
            fwddecl: `class ${this.mangleStringForCpp(entity.tkey)};`,
            fulldecl: `class ${this.mangleStringForCpp(entity.tkey)} : public BSQObject\n`
                + "{\n"
                + "public:\n"
                + `    ${fields.join("\n    ")}\n\n`
                + `    ${this.mangleStringForCpp(entity.tkey)}(${constructor_args.join(", ")}) : BSQObject(MIRNominalTypeEnum::${this.mangleStringForCpp(entity.tkey)})${constructor_initializer.length !== 0 ? ", " : ""}${constructor_initializer.join(", ")} { ; }\n`
                + `    virtual ~${this.mangleStringForCpp(entity.tkey)}() { ${destructor_list.join(" ")} }\n\n`
                + `    ${display}\n\n`
                + `    ${vfield_accessors.filter((vacf) => vacf !== "NA").join("\n    ")}\n\n`
                + `    ${vcalls.filter((vc) => vc !== "NA").join("\n    ")}\n`
                + "};"
        };
    }
}
exports.CPPTypeEmitter = CPPTypeEmitter;
//# sourceMappingURL=cpptype_emitter.js.map