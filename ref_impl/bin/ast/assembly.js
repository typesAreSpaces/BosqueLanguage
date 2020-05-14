"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const resolved_type_1 = require("./resolved_type");
const type_signature_1 = require("./type_signature");
class TemplateTermDecl {
    constructor(name, ttype) {
        this.name = name;
        this.ttype = ttype;
    }
}
exports.TemplateTermDecl = TemplateTermDecl;
class TemplateTermRestriction {
    constructor(name, ttype) {
        this.name = name;
        this.ttype = ttype;
    }
}
exports.TemplateTermRestriction = TemplateTermRestriction;
class InvokeDecl {
    constructor(sinfo, srcFile, attributes, recursive, pragmas, terms, termRestrictions, params, optRestName, optRestType, resultType, preconds, postconds, isLambda, captureSet, body) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.recursive = recursive;
        this.pragmas = pragmas;
        this.terms = terms;
        this.termRestrictions = termRestrictions;
        this.params = params;
        this.optRestName = optRestName;
        this.optRestType = optRestType;
        this.resultType = resultType;
        this.preconditions = preconds;
        this.postconditions = postconds;
        this.isLambda = isLambda;
        this.captureSet = captureSet;
        this.body = body;
    }
    generateSig() {
        return new type_signature_1.FunctionTypeSignature(this.recursive, [...this.params], this.optRestName, this.optRestType, this.resultType);
    }
    static createPCodeInvokeDecl(sinfo, srcFile, attributes, recursive, params, optRestName, optRestType, resultType, captureSet, body) {
        return new InvokeDecl(sinfo, srcFile, attributes, recursive, [], [], [], params, optRestName, optRestType, resultType, [], [], true, captureSet, body);
    }
    static createStaticInvokeDecl(sinfo, srcFile, attributes, recursive, pragmas, terms, termRestrictions, params, optRestName, optRestType, resultType, preconds, postconds, body) {
        return new InvokeDecl(sinfo, srcFile, attributes, recursive, pragmas, terms, termRestrictions, params, optRestName, optRestType, resultType, preconds, postconds, false, new Set(), body);
    }
    static createMemberInvokeDecl(sinfo, srcFile, attributes, recursive, pragmas, terms, termRestrictions, params, optRestName, optRestType, resultType, preconds, postconds, body) {
        return new InvokeDecl(sinfo, srcFile, attributes, recursive, pragmas, terms, termRestrictions, params, optRestName, optRestType, resultType, preconds, postconds, false, new Set(), body);
    }
}
exports.InvokeDecl = InvokeDecl;
class StaticMemberDecl {
    constructor(srcInfo, srcFile, pragmas, attributes, ns, name, dtype, value) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.pragmas = pragmas;
        this.attributes = attributes;
        this.name = name;
        this.declaredType = dtype;
        this.value = value;
    }
    getName() {
        return this.name;
    }
}
exports.StaticMemberDecl = StaticMemberDecl;
class StaticFunctionDecl {
    constructor(sinfo, srcFile, attributes, name, invoke) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.invoke = invoke;
    }
    getName() {
        return this.name;
    }
}
exports.StaticFunctionDecl = StaticFunctionDecl;
class MemberFieldDecl {
    constructor(srcInfo, srcFile, pragmas, attributes, name, dtype, value) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.pragmas = pragmas;
        this.attributes = attributes;
        this.name = name;
        this.declaredType = dtype;
        this.value = value;
    }
    getName() {
        return this.name;
    }
}
exports.MemberFieldDecl = MemberFieldDecl;
class MemberMethodDecl {
    constructor(sinfo, srcFile, attributes, name, invoke) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.name = name;
        this.invoke = invoke;
    }
    getName() {
        return this.name;
    }
}
exports.MemberMethodDecl = MemberMethodDecl;
class OOPTypeDecl {
    constructor(sourceLocation, srcFile, pragmas, attributes, ns, name, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods) {
        this.sourceLocation = sourceLocation;
        this.srcFile = srcFile;
        this.pragmas = pragmas;
        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.provides = provides;
        this.invariants = invariants;
        this.staticMembers = staticMembers;
        this.staticFunctions = staticFunctions;
        this.memberFields = memberFields;
        this.memberMethods = memberMethods;
    }
    isTypeACollectionEntity() {
        if (this.ns !== "NSCore") {
            return false;
        }
        return this.name === "List" || this.name === "Set";
    }
    isTypeAMapEntity() {
        if (this.ns !== "NSCore") {
            return false;
        }
        return this.name === "Map";
    }
    static attributeSetContains(attr, attrSet) {
        return attrSet.indexOf(attr) !== -1;
    }
}
exports.OOPTypeDecl = OOPTypeDecl;
class ConceptTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation, srcFile, pragmas, attributes, ns, name, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods) {
        super(sourceLocation, srcFile, pragmas, attributes, ns, name, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods);
    }
}
exports.ConceptTypeDecl = ConceptTypeDecl;
class EntityTypeDecl extends OOPTypeDecl {
    constructor(sourceLocation, srcFile, pragmas, attributes, ns, name, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods, isEnum, isKey) {
        super(sourceLocation, srcFile, pragmas, attributes, ns, name, terms, provides, invariants, staticMembers, staticFunctions, memberFields, memberMethods);
        this.isEnum = isEnum;
        this.isKey = isKey;
    }
}
exports.EntityTypeDecl = EntityTypeDecl;
class NamespaceConstDecl {
    constructor(srcInfo, srcFile, pragmas, attributes, ns, name, dtype, value) {
        this.sourceLocation = srcInfo;
        this.srcFile = srcFile;
        this.pragmas = pragmas;
        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
        this.declaredType = dtype;
        this.value = value;
    }
}
exports.NamespaceConstDecl = NamespaceConstDecl;
class NamespaceFunctionDecl {
    constructor(sinfo, srcFile, attributes, ns, name, invoke) {
        this.sourceLocation = sinfo;
        this.srcFile = srcFile;
        this.attributes = attributes;
        this.ns = ns;
        this.name = name;
        this.invoke = invoke;
    }
}
exports.NamespaceFunctionDecl = NamespaceFunctionDecl;
class NamespaceTypedef {
    constructor(ns, name, terms, btype) {
        this.ns = ns;
        this.name = name;
        this.terms = terms;
        this.boundType = btype;
    }
}
exports.NamespaceTypedef = NamespaceTypedef;
class NamespaceUsing {
    constructor(from, names) {
        this.fromNamespace = from;
        this.names = names;
    }
}
exports.NamespaceUsing = NamespaceUsing;
class NamespaceDeclaration {
    constructor(ns) {
        this.ns = ns;
        this.usings = [];
        this.declaredNames = new Set();
        this.typeDefs = new Map();
        this.consts = new Map();
        this.functions = new Map();
        this.concepts = new Map();
        this.objects = new Map();
    }
    checkUsingNameClash(names) {
        return names.some((name) => this.usings.some((usedecl) => usedecl.names.indexOf(name) !== -1));
    }
    checkDeclNameClash(ns, name) {
        const rname = ns + "::" + name;
        return this.typeDefs.has(rname) || this.consts.has(rname) || this.functions.has(rname) || this.concepts.has(rname) || this.objects.has(rname) || this.usings.some((usedecl) => usedecl.names.indexOf(name) !== -1);
    }
}
exports.NamespaceDeclaration = NamespaceDeclaration;
class OOMemberLookupInfo {
    constructor(contiainingType, decl, binds) {
        this.contiainingType = contiainingType;
        this.decl = decl;
        this.binds = binds;
    }
}
exports.OOMemberLookupInfo = OOMemberLookupInfo;
class Assembly {
    constructor() {
        this.m_specialTypeMap = new Map();
        this.m_namespaceMap = new Map();
        this.m_conceptMap = new Map();
        this.m_objectMap = new Map();
        this.m_subtypeRelationMemo = new Map();
        this.m_atomSubtypeRelationMemo = new Map();
    }
    resolveTemplateBinds(declterms, giventerms, binds) {
        const fullbinds = new Map();
        for (let i = 0; i < declterms.length; ++i) {
            fullbinds.set(declterms[i].name, this.normalizeTypeOnly(giventerms[i], binds));
        }
        return fullbinds;
    }
    normalizeType_Template(t, binds) {
        return binds.has(t.name) ? binds.get(t.name) : resolved_type_1.ResolvedType.createEmpty();
    }
    normalizeType_Nominal(t, binds) {
        const [aliasResolvedType, aliasResolvedBinds] = this.lookupTypeDef(t, binds);
        if (aliasResolvedType === undefined) {
            return resolved_type_1.ResolvedType.createEmpty();
        }
        else if (!(aliasResolvedType instanceof type_signature_1.NominalTypeSignature)) {
            return this.normalizeTypeGeneral(aliasResolvedType, aliasResolvedBinds);
        }
        else {
            const fconcept = this.tryGetConceptTypeForFullyResolvedName(aliasResolvedType.nameSpace + "::" + aliasResolvedType.baseName, aliasResolvedType.terms.length);
            if (fconcept !== undefined) {
                if (fconcept.terms.length !== aliasResolvedType.terms.length) {
                    return resolved_type_1.ResolvedType.createEmpty();
                }
                return resolved_type_1.ResolvedType.createSingle(this.createConceptTypeAtom(fconcept, aliasResolvedType, aliasResolvedBinds));
            }
            const fobject = this.tryGetObjectTypeForFullyResolvedName(aliasResolvedType.nameSpace + "::" + aliasResolvedType.baseName, aliasResolvedType.terms.length);
            if (fobject !== undefined) {
                if (fobject.terms.length !== aliasResolvedType.terms.length) {
                    return resolved_type_1.ResolvedType.createEmpty();
                }
                return resolved_type_1.ResolvedType.createSingle(this.createObjectTypeAtom(fobject, aliasResolvedType, aliasResolvedBinds));
            }
            return resolved_type_1.ResolvedType.createEmpty();
        }
    }
    normalizeType_Tuple(t, binds) {
        const entries = t.entries.map((entry) => new resolved_type_1.ResolvedTupleAtomTypeEntry(this.normalizeTypeOnly(entry[0], binds), entry[1]));
        if (entries.some((e) => e.type.isEmptyType())) {
            return resolved_type_1.ResolvedType.createEmpty();
        }
        let seenreq = false;
        for (let i = entries.length - 1; i >= 0; --i) {
            seenreq = seenreq || !entries[i].isOptional;
            if (entries[i].isOptional && seenreq) {
                return resolved_type_1.ResolvedType.createEmpty();
            }
        }
        return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedTupleAtomType.create(entries));
    }
    normalizeType_Record(t, binds) {
        let seenNames = new Set();
        let entries = [];
        for (let i = 0; i < t.entries.length; ++i) {
            if (seenNames.has(t.entries[i][0])) {
                return resolved_type_1.ResolvedType.createEmpty();
            }
            entries.push(new resolved_type_1.ResolvedRecordAtomTypeEntry(t.entries[i][0], this.normalizeTypeOnly(t.entries[i][1], binds), t.entries[i][2]));
        }
        if (entries.some((e) => e.type.isEmptyType())) {
            return resolved_type_1.ResolvedType.createEmpty();
        }
        return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedRecordAtomType.create(entries));
    }
    normalizeType_Intersection(t, binds) {
        if (t.types.some((opt) => this.normalizeTypeOnly(opt, binds).isEmptyType())) {
            return resolved_type_1.ResolvedType.createEmpty();
        }
        const ntypes = t.types.map((opt) => this.normalizeTypeOnly(opt, binds).options);
        const flattened = [].concat(...ntypes);
        if (flattened.some((ttype) => !(ttype instanceof resolved_type_1.ResolvedConceptAtomType))) {
            return resolved_type_1.ResolvedType.createEmpty();
        }
        const ctypes = flattened.map((arg) => arg.conceptTypes);
        const itypes = ([].concat(...ctypes)).sort((cte1, cte2) => cte1.idStr.localeCompare(cte2.idStr));
        //do a simplification based on A & B when A \Subtypeeq B is A
        let simplifiedTypes = [];
        for (let i = 0; i < itypes.length; ++i) {
            let docopy = true;
            for (let j = 0; j < itypes.length; ++j) {
                if (i === j) {
                    continue; //ignore check on same element
                }
                //if \exists a Tj s.t. Ti \Subtypeeq Tj then we discard Tj
                if (this.atomSubtypeOf(resolved_type_1.ResolvedConceptAtomType.create([itypes[j]]), resolved_type_1.ResolvedConceptAtomType.create([itypes[i]]))) {
                    docopy = (itypes[i].idStr === itypes[j].idStr) && i < j; //if same type only keep one copy
                    break;
                }
            }
            if (docopy) {
                simplifiedTypes.push(itypes[i]);
            }
        }
        if (simplifiedTypes.length === 0) {
            return resolved_type_1.ResolvedType.createEmpty();
        }
        return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedConceptAtomType.create(simplifiedTypes));
    }
    normalizeType_Union(t, binds) {
        if (t.types.some((opt) => this.normalizeTypeOnly(opt, binds).isEmptyType())) {
            return resolved_type_1.ResolvedType.createEmpty();
        }
        const utypes = t.types.map((opt) => this.normalizeTypeOnly(opt, binds));
        return this.normalizeUnionList(utypes);
    }
    normalizeUnionList(types) {
        //flatten any union types
        const ntypes = types.map((opt) => opt.options);
        const flattened = [].concat(...ntypes);
        //check for Some | None and add Any if needed
        if (flattened.some((atom) => atom.idStr === "NSCore::None") && flattened.some((atom) => atom.idStr === "NSCore::Some")) {
            flattened.push(this.getSpecialAnyType().options[0]);
        }
        const utypes = flattened.sort((cte1, cte2) => cte1.idStr.localeCompare(cte2.idStr));
        //do a simplification based on A | B when A \Subtypeeq B is B
        let simplifiedTypes = [];
        for (let i = 0; i < utypes.length; ++i) {
            let docopy = true;
            for (let j = 0; j < utypes.length; ++j) {
                if (i === j) {
                    continue; //ignore check on same element
                }
                //if \exists a Tj s.t. Ti \Subtypeeq Tj then we discard Ti
                if (this.atomSubtypeOf(utypes[i], utypes[j])) {
                    docopy = (utypes[i].idStr === utypes[j].idStr) && i < j; //if same type only keep one copy
                    break;
                }
            }
            if (docopy) {
                simplifiedTypes.push(utypes[i]);
            }
        }
        return resolved_type_1.ResolvedType.create(simplifiedTypes);
    }
    normalizeType_Function(t, binds) {
        const params = t.params.map((param) => new resolved_type_1.ResolvedFunctionTypeParam(param.name, param.isOptional, param.isRef, this.normalizeTypeGeneral(param.type, binds)));
        const optRestParamType = (t.optRestParamType !== undefined) ? this.normalizeTypeOnly(t.optRestParamType, binds) : undefined;
        const resType = this.normalizeTypeOnly(t.resultType, binds);
        if (params.some((p) => p.type instanceof resolved_type_1.ResolvedType && p.type.isEmptyType()) || params.some((p) => p.isOptional && p.isRef) || (optRestParamType !== undefined && optRestParamType.isEmptyType()) || resType.isEmptyType()) {
            return undefined;
        }
        return resolved_type_1.ResolvedFunctionType.create(t.recursive, params, t.optRestParamName, optRestParamType, resType);
    }
    atomSubtypeOf_EntityEntity(t1, t2) {
        if (t1.object.ns !== t2.object.ns || t1.object.name !== t2.object.name) {
            return false;
        }
        let allBindsOk = true;
        t1.binds.forEach((v, k) => { allBindsOk = allBindsOk && v.idStr === t2.binds.get(k).idStr; });
        return allBindsOk;
    }
    atomSubtypeOf_EntityConcept(t1, t2) {
        const t2type = resolved_type_1.ResolvedType.createSingle(t2);
        return t1.object.provides.some((provide) => {
            const tt = this.normalizeTypeOnly(provide, t1.binds);
            return !tt.isEmptyType() && this.subtypeOf(tt, t2type);
        });
    }
    atomSubtypeOf_ConceptConcept(t1, t2) {
        return t1.conceptTypes.every((c1t) => {
            return t2.conceptTypes.some((c2t) => {
                if (c1t.concept.ns === c2t.concept.ns && c1t.concept.name === c2t.concept.name) {
                    let allBindsOk = true;
                    c1t.binds.forEach((v, k) => { allBindsOk = allBindsOk && v.idStr === c2t.binds.get(k).idStr; });
                    return allBindsOk;
                }
                const t2type = resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedConceptAtomType.create([c2t]));
                return c1t.concept.provides.some((provide) => {
                    const tt = this.normalizeTypeOnly(provide, c1t.binds);
                    return !tt.isEmptyType() && this.subtypeOf(tt, t2type);
                });
            });
        });
    }
    atomSubtypeOf_TupleTuple(t1, t2) {
        for (let i = 0; i < t1.types.length; ++i) {
            const t1e = t1.types[i];
            if (i >= t2.types.length) {
                return false;
            }
            else {
                const t2e = t2.types[i];
                if ((t1e.isOptional && !t2e.isOptional) || !this.subtypeOf(t1e.type, t2e.type)) {
                    return false;
                }
            }
        }
        //t2 has a required entry that is not required in t1
        if (t2.types.length > t1.types.length && t2.types.slice(t1.types.length).some((entry) => !entry.isOptional)) {
            return false;
        }
        return true;
    }
    atomSubtypeOf_RecordRecord(t1, t2) {
        let badEntry = false;
        t1.entries.forEach((entry) => {
            const t2e = t2.entries.find((e) => e.name === entry.name);
            if (t2e === undefined) {
                badEntry = badEntry || true;
            }
            else {
                if ((entry.isOptional && !t2e.isOptional) || !this.subtypeOf(entry.type, t2e.type)) {
                    badEntry = badEntry || true;
                }
            }
        });
        t2.entries.forEach((entry) => {
            badEntry = badEntry || (t1.entries.find((e) => e.name === entry.name) === undefined && !entry.isOptional);
        });
        if (badEntry) {
            return false;
        }
        return true;
    }
    internSpecialConceptType(name, terms, binds) {
        if (this.m_specialTypeMap.has("NSCore::" + name)) {
            return this.m_specialTypeMap.get("NSCore::" + name);
        }
        const rsig = new type_signature_1.NominalTypeSignature("NSCore", name, terms || []);
        const tconcept = this.createConceptTypeAtom(this.tryGetConceptTypeForFullyResolvedName("NSCore::" + name, terms ? terms.length : 0), rsig, binds || new Map());
        const rtype = resolved_type_1.ResolvedType.createSingle(tconcept);
        this.m_specialTypeMap.set("NSCore::" + name, rtype);
        return rtype;
    }
    internSpecialObjectType(name, terms, binds) {
        if (this.m_specialTypeMap.has("NSCore::" + name)) {
            return this.m_specialTypeMap.get("NSCore::" + name);
        }
        const rsig = new type_signature_1.NominalTypeSignature("NSCore", name, terms || []);
        const tobject = this.createObjectTypeAtom(this.tryGetObjectTypeForFullyResolvedName("NSCore::" + name, terms ? terms.length : 0), rsig, binds || new Map());
        const rtype = resolved_type_1.ResolvedType.createSingle(tobject);
        this.m_specialTypeMap.set("NSCore::" + name, rtype);
        return rtype;
    }
    getSpecialAnyType() { return this.internSpecialConceptType("Any"); }
    getSpecialNoneType() { return this.internSpecialObjectType("None"); }
    getSpecialSomeType() { return this.internSpecialConceptType("Some"); }
    getSpecialBoolType() { return this.internSpecialObjectType("Bool"); }
    getSpecialIntType() { return this.internSpecialObjectType("Int"); }
    getSpecialRegexType() { return this.internSpecialObjectType("Regex"); }
    getSpecialStringType() { return this.internSpecialObjectType("String"); }
    getSpecialGUIDType() { return this.internSpecialObjectType("GUID"); }
    getSpecialTupleConceptType() { return this.internSpecialConceptType("Tuple"); }
    getSpecialRecordConceptType() { return this.internSpecialConceptType("Record"); }
    getSpecialObjectConceptType() { return this.internSpecialConceptType("Object"); }
    getSpecialEnumType() { return this.internSpecialConceptType("Enum"); }
    getSpecialCustomKeyType() { return this.internSpecialConceptType("IdKey"); }
    getSpecialParsableConcept() { return this.internSpecialConceptType("Parsable"); }
    getSpecialKeyTypeConcept() { return this.internSpecialConceptType("KeyType"); }
    ensureNominalRepresentation(t) {
        const opts = t.options.map((opt) => {
            if (opt instanceof resolved_type_1.ResolvedTupleAtomType) {
                return this.getSpecialTupleConceptType();
            }
            else if (opt instanceof resolved_type_1.ResolvedRecordAtomType) {
                return this.getSpecialRecordConceptType();
            }
            else {
                return resolved_type_1.ResolvedType.createSingle(opt);
            }
        });
        return this.typeUnion(opts);
    }
    tryGetConceptTypeForFullyResolvedName(name, templatecount) {
        return this.m_conceptMap.get(name + templatecount);
    }
    tryGetObjectTypeForFullyResolvedName(name, templatecount) {
        return this.m_objectMap.get(name + templatecount);
    }
    hasNamespace(ns) {
        return this.m_namespaceMap.has(ns);
    }
    getNamespace(ns) {
        return this.m_namespaceMap.get(ns);
    }
    ensureNamespace(ns) {
        if (!this.hasNamespace(ns)) {
            this.m_namespaceMap.set(ns, new NamespaceDeclaration(ns));
        }
        return this.getNamespace(ns);
    }
    getNamespaces() {
        let decls = [];
        this.m_namespaceMap.forEach((v, k) => {
            decls.push(v);
        });
        return decls;
    }
    addConceptDecl(resolvedName, templatecount, concept) {
        this.m_conceptMap.set(resolvedName + templatecount, concept);
    }
    addObjectDecl(resolvedName, templatecount, object) {
        this.m_objectMap.set(resolvedName + templatecount, object);
    }
    ////
    //Type representation, normalization, and operations
    lookupTypeDef(t, binds) {
        if (!this.hasNamespace(t.nameSpace)) {
            return [undefined, new Map()];
        }
        const lname = t.nameSpace + "::" + t.baseName;
        const nsd = this.getNamespace(t.nameSpace);
        if (!nsd.typeDefs.has(lname)) {
            return [t, new Map(binds)];
        }
        //compute the bindings to use when resolving the RHS of the typedef alias
        const typealias = nsd.typeDefs.get(lname);
        const updatedbinds = this.resolveTemplateBinds(typealias.terms, t.terms, binds);
        if (typealias.boundType instanceof type_signature_1.NominalTypeSignature) {
            return this.lookupTypeDef(typealias.boundType, updatedbinds);
        }
        else {
            return [typealias.boundType, updatedbinds];
        }
    }
    createConceptTypeAtom(concept, t, binds) {
        const fullbinds = this.resolveTemplateBinds(concept.terms, t.terms, binds);
        return resolved_type_1.ResolvedConceptAtomType.create([resolved_type_1.ResolvedConceptAtomTypeEntry.create(concept, fullbinds)]);
    }
    createObjectTypeAtom(object, t, binds) {
        const fullbinds = this.resolveTemplateBinds(object.terms, t.terms, binds);
        return resolved_type_1.ResolvedEntityAtomType.create(object, fullbinds);
    }
    getAllOOFields(ooptype, binds, fmap) {
        let declfields = fmap || new Map();
        ooptype.memberFields.forEach((mf, name) => {
            if (!OOPTypeDecl.attributeSetContains("abstract", mf.attributes) && !declfields.has(name)) {
                declfields.set(name, [ooptype, mf, binds]);
            }
        });
        ooptype.provides.forEach((provide) => {
            const tt = this.normalizeTypeOnly(provide, binds);
            tt.options[0].conceptTypes.forEach((concept) => {
                declfields = this.getAllOOFields(concept.concept, concept.binds, declfields);
            });
        });
        return declfields;
    }
    getAllOOInvariants(ooptype, binds, invs) {
        let declinvs = invs || [];
        ooptype.invariants.forEach((inv) => {
            declinvs.push([inv, binds]);
        });
        ooptype.provides.forEach((provide) => {
            const tt = this.normalizeTypeOnly(provide, binds);
            tt.options[0].conceptTypes.forEach((concept) => {
                declinvs = this.getAllOOInvariants(concept.concept, concept.binds, declinvs);
            });
        });
        return declinvs;
    }
    tryGetOOMemberDeclThis(ooptype, binds, kind, search) {
        let decl = undefined;
        if (kind === "const") {
            decl = ooptype.staticMembers.get(search);
        }
        else if (kind === "static") {
            decl = ooptype.staticFunctions.get(search);
        }
        else if (kind === "field") {
            decl = ooptype.memberFields.get(search);
        }
        else {
            decl = ooptype.memberMethods.get(search);
        }
        if (decl === undefined) {
            return undefined;
        }
        else {
            return new OOMemberLookupInfo(ooptype, decl, binds);
        }
    }
    tryGetOOMemberDeclParent(ooptype, binds, kind, search) {
        for (let i = 0; i < ooptype.provides.length; ++i) {
            const tt = this.normalizeTypeOnly(ooptype.provides[i], binds).options[0].conceptTypes[0];
            const res = this.tryGetOOMemberDeclThis(tt.concept, tt.binds, kind, search) || this.tryGetOOMemberDeclParent(tt.concept, tt.binds, kind, search);
            if (res !== undefined) {
                return res;
            }
        }
        return undefined;
    }
    tryGetOOMemberRootDeclarationOptions(ooptype, binds, kind, search) {
        const tdecl = this.tryGetOOMemberDeclThis(ooptype, binds, kind, search);
        const pdecl = this.tryGetOOMemberDeclParent(ooptype, binds, kind, search);
        if (tdecl === undefined && pdecl === undefined) {
            return undefined;
        }
        else if (tdecl !== undefined && pdecl === undefined) {
            return [tdecl];
        }
        else {
            let dopts = [];
            for (let i = 0; i < ooptype.provides.length; ++i) {
                const tt = this.normalizeTypeOnly(ooptype.provides[i], binds).options[0].conceptTypes[0];
                const copts = this.tryGetOOMemberRootDeclarationOptions(tt.concept, tt.binds, kind, search);
                if (copts !== undefined) {
                    dopts = dopts.concat(copts);
                }
            }
            return dopts;
        }
    }
    ensureSingleDecl(opts) {
        if (opts.length === 0) {
            return undefined;
        }
        else if (opts.length === 1) {
            return opts[0];
        }
        else {
            const opt1 = opts[0];
            const allSame = opts.every((opt) => {
                if (opt1.contiainingType.ns !== opt.contiainingType.ns || opt1.contiainingType.name !== opt.contiainingType.name) {
                    return false;
                }
                if (opt1.binds.size !== opt.binds.size) {
                    return false;
                }
                let bindsok = true;
                opt1.binds.forEach((v, k) => {
                    bindsok = bindsok && opt.binds.has(k) && v.idStr === opt.binds.get(k).idStr;
                });
                return bindsok;
            });
            return allSame ? opt1 : undefined;
        }
    }
    tryGetOOMemberDeclUnique(tt, kind, search) {
        const atom = resolved_type_1.ResolvedType.tryGetOOTypeInfo(this.ensureNominalRepresentation(tt));
        if (atom === undefined) {
            return undefined;
        }
        if (atom instanceof resolved_type_1.ResolvedEntityAtomType) {
            return this.tryGetOOMemberDeclThis(atom.object, atom.binds, kind, search) || this.tryGetOOMemberDeclParent(atom.object, atom.binds, kind, search);
        }
        else {
            const opts = atom.conceptTypes.map((opt) => this.tryGetOOMemberDeclThis(opt.concept, opt.binds, kind, search) || this.tryGetOOMemberDeclParent(opt.concept, opt.binds, kind, search));
            return this.ensureSingleDecl(opts.filter((opt) => opt !== undefined));
        }
    }
    tryGetOOMemberDeclOptions(tt, kind, search) {
        const decls = this.ensureNominalRepresentation(tt).options.map((atom) => this.tryGetOOMemberDeclUnique(resolved_type_1.ResolvedType.createSingle(atom), kind, search));
        if (decls.some((opt) => opt === undefined)) {
            return { decls: undefined, root: undefined };
        }
        const ropts = decls.map((info) => this.tryGetOOMemberRootDeclarationOptions(info.contiainingType, info.binds, kind, search));
        const roots = [].concat(...ropts);
        return { decls: decls, root: this.ensureSingleDecl(roots) };
    }
    resolveBindsForCall(declterms, giventerms, implicitBinds, callBinds) {
        let fullbinds = new Map();
        implicitBinds.forEach((v, k) => {
            fullbinds.set(k, v);
        });
        //compute the bindings to use when resolving the RHS of the typedef alias
        for (let i = 0; i < declterms.length; ++i) {
            fullbinds.set(declterms[i].name, this.normalizeTypeOnly(giventerms[i], callBinds));
        }
        return fullbinds;
    }
    normalizeTypeOnly(t, binds) {
        const res = this.normalizeTypeGeneral(t, binds);
        if (res instanceof resolved_type_1.ResolvedFunctionType) {
            return resolved_type_1.ResolvedType.createEmpty();
        }
        else {
            return res;
        }
    }
    normalizeTypeFunction(t, binds) {
        if (t instanceof type_signature_1.ParseErrorTypeSignature || t instanceof type_signature_1.AutoTypeSignature) {
            return undefined;
        }
        else {
            return this.normalizeType_Function(t, binds);
        }
    }
    normalizeTypeGeneral(t, binds) {
        if (t instanceof type_signature_1.ParseErrorTypeSignature || t instanceof type_signature_1.AutoTypeSignature) {
            return resolved_type_1.ResolvedType.createEmpty();
        }
        else if (t instanceof type_signature_1.FunctionTypeSignature) {
            return this.normalizeTypeFunction(t, binds) || resolved_type_1.ResolvedType.createEmpty();
        }
        else if (t instanceof type_signature_1.TemplateTypeSignature) {
            return this.normalizeType_Template(t, binds);
        }
        else if (t instanceof type_signature_1.NominalTypeSignature) {
            return this.normalizeType_Nominal(t, binds);
        }
        else if (t instanceof type_signature_1.TupleTypeSignature) {
            return this.normalizeType_Tuple(t, binds);
        }
        else if (t instanceof type_signature_1.RecordTypeSignature) {
            return this.normalizeType_Record(t, binds);
        }
        else if (t instanceof type_signature_1.IntersectionTypeSignature) {
            return this.normalizeType_Intersection(t, binds);
        }
        else {
            return this.normalizeType_Union(t, binds);
        }
    }
    normalizeToNominalRepresentation(t) {
        if (t instanceof resolved_type_1.ResolvedTupleAtomType) {
            return this.getSpecialTupleConceptType();
        }
        else if (t instanceof resolved_type_1.ResolvedRecordAtomType) {
            return this.getSpecialRecordConceptType();
        }
        else {
            return t;
        }
    }
    computeUnifiedFunctionType(funcs, rootSig) {
        if (funcs.length === 0) {
            return undefined;
        }
        if (funcs.length === 1) {
            return funcs[0];
        }
        else {
            if (funcs.some((ft) => !this.functionSubtypeOf(ft, rootSig))) {
                return undefined;
            }
            return rootSig;
        }
    }
    restrictNone(from) {
        return (this.subtypeOf(this.getSpecialNoneType(), from)) ? this.getSpecialNoneType() : resolved_type_1.ResolvedType.createEmpty();
    }
    restrictSome(from) {
        const hasany = from.options.some((atom) => resolved_type_1.ResolvedType.createSingle(atom).isAnyType());
        const sometypes = from.options.filter((atom) => this.subtypeOf(resolved_type_1.ResolvedType.createSingle(atom), this.getSpecialSomeType()));
        if (hasany) {
            return this.getSpecialSomeType();
        }
        else if (sometypes.length !== 0) {
            return resolved_type_1.ResolvedType.create(sometypes);
        }
        else {
            return resolved_type_1.ResolvedType.createEmpty();
        }
    }
    restrictT(from, t) {
        if (t.isNoneType()) {
            return this.restrictNone(from);
        }
        else if (t.isSomeType()) {
            return this.restrictSome(from);
        }
        else {
            return t;
        }
    }
    restrictNotT(from, t) {
        if (t.isNoneType()) {
            return this.restrictSome(from);
        }
        else if (t.isSomeType()) {
            return this.restrictNone(from);
        }
        else {
            const notttypes = from.options.filter((atom) => !this.subtypeOf(resolved_type_1.ResolvedType.createSingle(atom), t));
            return notttypes.length !== 0 ? resolved_type_1.ResolvedType.create(notttypes) : resolved_type_1.ResolvedType.createEmpty();
        }
    }
    typeUnion(types) {
        return this.normalizeUnionList(types);
    }
    atomSubtypeOf(t1, t2) {
        let memores = this.m_atomSubtypeRelationMemo.get(t1.idStr);
        if (memores === undefined) {
            this.m_atomSubtypeRelationMemo.set(t1.idStr, new Map());
            memores = this.m_atomSubtypeRelationMemo.get(t1.idStr);
        }
        let memoval = memores.get(t2.idStr);
        if (memoval !== undefined) {
            return memoval;
        }
        let res = false;
        if (t1.idStr === t2.idStr) {
            res = true;
        }
        else if (t1 instanceof resolved_type_1.ResolvedConceptAtomType && t2 instanceof resolved_type_1.ResolvedConceptAtomType) {
            res = this.atomSubtypeOf_ConceptConcept(t1, t2);
        }
        else if (t1 instanceof resolved_type_1.ResolvedConceptAtomType) {
            //res stays false
        }
        else if (t2 instanceof resolved_type_1.ResolvedConceptAtomType) {
            if (t1 instanceof resolved_type_1.ResolvedEntityAtomType) {
                res = this.atomSubtypeOf_EntityConcept(t1, t2);
            }
            else if (t1 instanceof resolved_type_1.ResolvedTupleAtomType) {
                res = this.atomSubtypeOf_ConceptConcept(this.getSpecialTupleConceptType().options[0], t2);
            }
            else {
                res = this.atomSubtypeOf_ConceptConcept(this.getSpecialRecordConceptType().options[0], t2);
            }
        }
        else {
            if (t1 instanceof resolved_type_1.ResolvedEntityAtomType && t2 instanceof resolved_type_1.ResolvedEntityAtomType) {
                res = this.atomSubtypeOf_EntityEntity(t1, t2);
            }
            else if (t1 instanceof resolved_type_1.ResolvedTupleAtomType && t2 instanceof resolved_type_1.ResolvedTupleAtomType) {
                res = this.atomSubtypeOf_TupleTuple(t1, t2);
            }
            else if (t1 instanceof resolved_type_1.ResolvedRecordAtomType && t2 instanceof resolved_type_1.ResolvedRecordAtomType) {
                res = this.atomSubtypeOf_RecordRecord(t1, t2);
            }
            else {
                //fall-through
            }
        }
        memores.set(t2.idStr, res);
        return res;
    }
    subtypeOf(t1, t2) {
        let memores = this.m_subtypeRelationMemo.get(t1.idStr);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.idStr, new Map());
            memores = this.m_subtypeRelationMemo.get(t1.idStr);
        }
        let memoval = memores.get(t2.idStr);
        if (memoval !== undefined) {
            return memoval;
        }
        const res = t1.options.every((t1opt) => t2.options.some((t2opt) => this.atomSubtypeOf(t1opt, t2opt)));
        memores.set(t2.idStr, res);
        return res;
    }
    functionSubtypeOf_helper(t1, t2) {
        if (t2.params.length !== t1.params.length) {
            return false; //need to have the same number of parameters
        }
        if ((t2.optRestParamType !== undefined) !== (t1.optRestParamType !== undefined)) {
            return false; //should both have rest or not
        }
        if (t2.optRestParamType !== undefined && !this.subtypeOf(t2.optRestParamType, t1.optRestParamType)) {
            return false; //variance
        }
        for (let i = 0; i < t2.params.length; ++i) {
            const t2p = t2.params[i];
            const t1p = t1.params[i];
            if ((t2p.isOptional !== t1p.isOptional) || (t2p.isRef !== t1p.isRef)) {
                return false;
            }
            //We want the argument types to be the same for all cases -- no clear reason to overload to more general types
            if (t2p.type instanceof resolved_type_1.ResolvedFunctionType && t1p.type instanceof resolved_type_1.ResolvedFunctionType) {
                if (t2p.type.idStr !== t1p.type.idStr) {
                    return false;
                }
            }
            else if (t2p.type instanceof resolved_type_1.ResolvedType && t1p.type instanceof resolved_type_1.ResolvedType) {
                if (t2p.type.idStr !== t1p.type.idStr) {
                    return false;
                }
            }
            else {
                return false;
            }
            //check that if t2p is named then t1p has the same name
            if (t2.params[i].name !== "_") {
                if (t2.params[i].name !== t1.params[i].name) {
                    return false;
                }
            }
        }
        return t1.resultType.idStr === t2.resultType.idStr;
    }
    functionSubtypeOf(t1, t2) {
        let memores = this.m_subtypeRelationMemo.get(t1.idStr);
        if (memores === undefined) {
            this.m_subtypeRelationMemo.set(t1.idStr, new Map());
            memores = this.m_subtypeRelationMemo.get(t1.idStr);
        }
        let memoval = memores.get(t2.idStr);
        if (memoval !== undefined) {
            return memoval;
        }
        const res = this.functionSubtypeOf_helper(t1, t2);
        memores.set(t2.idStr, res);
        return res;
    }
}
exports.Assembly = Assembly;
//# sourceMappingURL=assembly.js.map