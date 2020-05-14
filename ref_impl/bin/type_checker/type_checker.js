"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const resolved_type_1 = require("../ast/resolved_type");
const assembly_1 = require("../ast/assembly");
const type_environment_1 = require("./type_environment");
const type_signature_1 = require("../ast/type_signature");
const body_1 = require("../ast/body");
const mir_emitter_1 = require("../compiler/mir_emitter");
const mir_ops_1 = require("../compiler/mir_ops");
const parser_1 = require("../ast/parser");
const mir_assembly_1 = require("../compiler/mir_assembly");
class TypeError extends Error {
    constructor(file, line, message) {
        super(`Type error on ${line} -- ${message}`);
        Object.setPrototypeOf(this, new.target.prototype);
        this.file = file;
        this.line = line;
    }
}
exports.TypeError = TypeError;
class TypeChecker {
    constructor(assembly, emitEnabled, emitter, doInvariantCheck, doPrePostCheck, doAssertCheck) {
        this.AnySplitMethods = ["is", "isSome", "isNone"];
        this.m_assembly = assembly;
        this.m_doInvariantCheck = doInvariantCheck;
        this.m_doPrePostCheck = doPrePostCheck;
        this.m_doAssertCheck = doAssertCheck;
        this.m_file = "[No File]";
        this.m_errors = [];
        this.m_emitEnabled = emitEnabled;
        this.m_emitter = emitter;
    }
    raiseError(sinfo, msg) {
        this.m_emitEnabled = false;
        this.m_errors.push([this.m_file, sinfo.line, msg || "Type error"]);
        throw new TypeError(this.m_file, sinfo.line, msg || "Type error");
    }
    raiseErrorIf(sinfo, cond, msg) {
        if (cond) {
            this.raiseError(sinfo, msg);
        }
    }
    getErrorList() {
        return this.m_errors;
    }
    resolveAndEnsureTypeOnly(sinfo, ttype, binds) {
        const rtype = this.m_assembly.normalizeTypeOnly(ttype, binds);
        this.raiseErrorIf(sinfo, rtype.isEmptyType(), "Bad type signature");
        return rtype;
    }
    checkTemplateTypes(sinfo, terms, binds, optTypeRestrict) {
        const boundsok = terms.every((t) => this.m_assembly.subtypeOf(binds.get(t.name), this.resolveAndEnsureTypeOnly(sinfo, t.ttype, new Map())));
        this.raiseErrorIf(sinfo, !boundsok, "Template instantiation does not satisfy specified bounds");
        if (optTypeRestrict !== undefined) {
            const restrictok = optTypeRestrict.every((r) => this.m_assembly.subtypeOf(binds.get(r[0]), r[1]));
            this.raiseErrorIf(sinfo, !restrictok, "Violates type restriction in instantiation");
        }
    }
    checkInvokeDecl(sinfo, invoke, invokeBinds, pcodes) {
        this.raiseErrorIf(sinfo, invoke.optRestType !== undefined && invoke.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");
        this.raiseErrorIf(sinfo, invoke.recursive === "no" && pcodes.some((pc) => pc.code.recursive === "yes"), "Recursive decl does not match use");
        const allNames = new Set();
        if (invoke.optRestName !== undefined && invoke.optRestName !== "_") {
            allNames.add(invoke.optRestName);
        }
        for (let i = 0; i < invoke.params.length; ++i) {
            if (invoke.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(invoke.params[i].name), `Duplicate name in invocation signature paramaters "${invoke.params[i].name}"`);
                allNames.add(invoke.params[i].name);
            }
            const rtype = this.m_assembly.normalizeTypeGeneral(invoke.params[i].type, invokeBinds);
            this.raiseErrorIf(sinfo, rtype instanceof resolved_type_1.ResolvedType && rtype.isEmptyType(), "Bad type signature");
        }
        const firstOptIndex = invoke.params.findIndex((param) => param.isOptional);
        if (firstOptIndex === -1) {
            return;
        }
        for (let i = firstOptIndex; i < invoke.params.length; ++i) {
            this.raiseErrorIf(sinfo, !invoke.params[i].isOptional, "Cannot have required paramaters following optional parameters");
        }
        if (invoke.optRestType !== undefined) {
            this.resolveAndEnsureTypeOnly(sinfo, invoke.optRestType, invokeBinds);
        }
        this.resolveAndEnsureTypeOnly(sinfo, invoke.resultType, invokeBinds);
    }
    checkPCodeDecl(sinfo, fsig, rec) {
        this.raiseErrorIf(sinfo, fsig.optRestParamType !== undefined && fsig.params.some((param) => param.isOptional), "Cannot have optional and rest parameters in an invocation signature");
        this.raiseErrorIf(sinfo, rec === "no" && fsig.recursive === "yes", "Recursive decl does not match use");
        const allNames = new Set();
        if (fsig.optRestParamName !== undefined && fsig.optRestParamName !== "_") {
            allNames.add(fsig.optRestParamName);
        }
        for (let i = 0; i < fsig.params.length; ++i) {
            if (fsig.params[i].name !== "_") {
                this.raiseErrorIf(sinfo, allNames.has(fsig.params[i].name), `Duplicate name in invocation signature paramaters "${fsig.params[i].name}"`);
                allNames.add(fsig.params[i].name);
            }
        }
        const firstOptIndex = fsig.params.findIndex((param) => param.isOptional);
        if (firstOptIndex === -1) {
            return;
        }
        for (let i = firstOptIndex; i < fsig.params.length; ++i) {
            this.raiseErrorIf(sinfo, !fsig.params[i].isOptional, "Cannot have required paramaters following optional parameters");
        }
    }
    checkRecursion(sinfo, fsig, pcodes, crec) {
        if ((fsig.recursive === "no" && crec === "no") || (fsig.recursive === "yes" && crec === "yes")) {
            return;
        }
        let sigr = fsig.recursive;
        if (sigr === "cond") {
            sigr = pcodes.some((pc) => pc.code.recursive === "yes") ? "yes" : "no";
        }
        let callr = crec;
        if (callr === "cond") {
            callr = pcodes.some((pc) => pc.code.recursive === "yes") ? "yes" : "no";
        }
        this.raiseErrorIf(sinfo, (sigr === "yes" && callr === "no") || (sigr === "no" && callr === "yes"), "Mismatched recursive annotations on call");
    }
    checkValueEq(lhs, rhs) {
        return lhs.options.some((lhsopt) => {
            const lhst = resolved_type_1.ResolvedType.createSingle(lhsopt);
            return rhs.options.some((rhsopt) => {
                const rhst = resolved_type_1.ResolvedType.createSingle(rhsopt);
                return this.checkValueEq_Single(lhst, rhst);
            });
        });
    }
    checkValueEq_Single(lhs, rhs) {
        if (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialNoneType()) || this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialNoneType())) {
            return true;
        }
        const bothBool = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialBoolType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialBoolType()));
        const bothInt = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialIntType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialIntType()));
        const bothString = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialStringType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialStringType()));
        const bothGUID = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialGUIDType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialGUIDType()));
        if (bothBool || bothInt || bothString || bothGUID) {
            return true;
        }
        const bothStringOf = (lhs.idStr.startsWith("NSCore::StringOf<") && rhs.idStr.startsWith("NSCore::StringOf<"));
        if (bothStringOf) {
            return this.m_assembly.subtypeOf(lhs, rhs) || this.m_assembly.subtypeOf(rhs, lhs); //types are compatible
        }
        const bothEnum = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialEnumType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialEnumType()));
        const bothCustomKey = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialCustomKeyType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialCustomKeyType()));
        if (bothEnum || bothCustomKey) {
            return this.m_assembly.subtypeOf(lhs, rhs) && this.m_assembly.subtypeOf(rhs, lhs); //types are equal
        }
        const lhskeytype = lhs.idStr === "NSCore::KeyType" && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialKeyTypeConcept());
        const rhskeytype = this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialKeyTypeConcept()) && rhs.idStr === "NSCore::KeyType";
        if (lhskeytype || rhskeytype) {
            return true;
        }
        return false;
    }
    checkValueLess(lhs, rhs) {
        const bothInt = (this.m_assembly.subtypeOf(lhs, this.m_assembly.getSpecialIntType()) && this.m_assembly.subtypeOf(rhs, this.m_assembly.getSpecialIntType()));
        if (bothInt) {
            return true;
        }
        return false;
    }
    getInfoForLoadFromIndex(rtype, idx) {
        const options = rtype.options.map((atom) => {
            if (atom instanceof resolved_type_1.ResolvedEntityAtomType) {
                return this.m_assembly.getSpecialAnyType();
            }
            const tatom = atom;
            if (idx < tatom.types.length) {
                if (!tatom.types[idx].isOptional) {
                    return tatom.types[idx].type;
                }
                else {
                    return this.m_assembly.typeUnion([tatom.types[idx].type, this.m_assembly.getSpecialNoneType()]);
                }
            }
            else {
                return this.m_assembly.getSpecialNoneType();
            }
        });
        return this.m_assembly.typeUnion(options);
    }
    getInfoForLoadFromPropertyName(rtype, pname) {
        const options = rtype.options.map((atom) => {
            if (atom instanceof resolved_type_1.ResolvedEntityAtomType) {
                return this.m_assembly.getSpecialAnyType();
            }
            const ratom = atom;
            const tidx = ratom.entries.findIndex((re) => re.name === pname);
            if (tidx !== -1) {
                if (!ratom.entries[tidx].isOptional) {
                    return ratom.entries[tidx].type;
                }
                else {
                    return this.m_assembly.typeUnion([ratom.entries[tidx].type, this.m_assembly.getSpecialNoneType()]);
                }
            }
            else {
                return this.m_assembly.getSpecialNoneType();
            }
        });
        return this.m_assembly.typeUnion(options);
    }
    projectTupleAtom(sinfo, opt, ptype) {
        this.raiseErrorIf(sinfo, !(opt instanceof resolved_type_1.ResolvedTupleAtomType), "Cannot project over 'Tuple' type");
        const tuple = opt;
        let tentries = [];
        for (let i = 0; i < ptype.types.length; ++i) {
            if (!ptype.types[i].isOptional) {
                this.raiseErrorIf(sinfo, i >= tuple.types.length || tuple.types[i].isOptional, "Type mismatch in projection");
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(tuple.types[i].type, ptype.types[i].type), "Type mismatch in projection");
                tentries.push(new resolved_type_1.ResolvedTupleAtomTypeEntry(tuple.types[i].type, false));
            }
            else {
                if (i < tuple.types.length) {
                    this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(tuple.types[i].type, ptype.types[i].type), "Type mismatch in projection");
                    tentries.push(new resolved_type_1.ResolvedTupleAtomTypeEntry(tuple.types[i].type, tuple.types[i].isOptional));
                }
            }
        }
        return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedTupleAtomType.create(tentries));
    }
    projectRecordAtom(sinfo, opt, ptype) {
        this.raiseErrorIf(sinfo, !(opt instanceof resolved_type_1.ResolvedRecordAtomType), "Cannot project over 'Record' type");
        const record = opt;
        let rentries = [];
        for (let i = 0; i < ptype.entries.length; ++i) {
            const riter = record.entries.find((v) => v.name === ptype.entries[i].name);
            if (!ptype.entries[i].isOptional) {
                this.raiseErrorIf(sinfo, riter === undefined || riter.isOptional, "Type mismatch in projection");
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(riter.type, ptype.entries[i].type), "Type mismatch in projection");
                rentries.push(new resolved_type_1.ResolvedRecordAtomTypeEntry(ptype.entries[i].name, riter.type, false));
            }
            else {
                if (riter !== undefined) {
                    this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(riter.type, ptype.entries[i].type), "Type mismatch in projection");
                    rentries.push(new resolved_type_1.ResolvedRecordAtomTypeEntry(ptype.entries[i].name, riter.type, riter.isOptional));
                }
            }
        }
        return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedRecordAtomType.create(rentries));
    }
    projectOOTypeAtom(sinfo, opt, ptype) {
        let fields = new Set();
        ptype.conceptTypes.forEach((concept) => {
            const fmap = this.m_assembly.getAllOOFields(concept.concept, concept.binds);
            fmap.forEach((v, k) => fields.add(k));
        });
        let farray = [];
        fields.forEach((f) => farray.push(f));
        farray.sort();
        farray.forEach((f) => {
            const finfo = this.m_assembly.tryGetOOMemberDeclOptions(opt, "field", f);
            this.raiseErrorIf(sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");
        });
        const rentries = opt.options.map((atom) => {
            const oentries = farray.map((f) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclUnique(resolved_type_1.ResolvedType.createSingle(atom), "field", f);
                const ftype = this.resolveAndEnsureTypeOnly(sinfo, finfo.decl.declaredType, finfo.binds);
                return new resolved_type_1.ResolvedRecordAtomTypeEntry(f, ftype, false);
            });
            return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedRecordAtomType.create(oentries));
        });
        return rentries;
    }
    updateTupleIndeciesAtom(sinfo, t, updates) {
        this.raiseErrorIf(sinfo, !(t instanceof resolved_type_1.ResolvedTupleAtomType), "Cannot update on 'Tuple' type");
        const tuple = t;
        let tentries = [];
        for (let i = 0; i < updates.length; ++i) {
            const update = updates[i];
            this.raiseErrorIf(sinfo, update[0] < 0, "Update index is out of tuple bounds");
            if (update[0] > tentries.length) {
                const extendCount = (update[0] - tentries.length) + 1;
                for (let j = 0; j < extendCount; ++j) {
                    if (tentries.length + j < tuple.types.length) {
                        if (!tuple.types[i].isOptional) {
                            tentries.push(new resolved_type_1.ResolvedTupleAtomTypeEntry(tuple.types[j].type, false));
                        }
                        else {
                            tentries.push(new resolved_type_1.ResolvedTupleAtomTypeEntry(this.m_assembly.typeUnion([tuple.types[j].type, this.m_assembly.getSpecialNoneType()]), false));
                        }
                    }
                    else {
                        tentries.push(new resolved_type_1.ResolvedTupleAtomTypeEntry(this.m_assembly.getSpecialNoneType(), false));
                    }
                }
            }
            tentries[update[0]] = new resolved_type_1.ResolvedTupleAtomTypeEntry(update[1], false);
        }
        return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedTupleAtomType.create(tentries));
    }
    updateNamedPropertiesAtom(sinfo, t, updates) {
        this.raiseErrorIf(sinfo, !(t instanceof resolved_type_1.ResolvedRecordAtomType), "Cannot update on 'Record' type");
        const record = t;
        let rentries = [...record.entries];
        for (let i = 0; i < updates.length; ++i) {
            const update = updates[i];
            const idx = rentries.findIndex((e) => e.name === update[0]);
            rentries[idx !== -1 ? idx : rentries.length] = new resolved_type_1.ResolvedRecordAtomTypeEntry(update[0], update[1], false);
        }
        return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedRecordAtomType.create(rentries));
    }
    appendIntoTupleAtom(sinfo, t, merge) {
        this.raiseErrorIf(sinfo, !(t instanceof resolved_type_1.ResolvedTupleAtomType), "Cannot append on 'Tuple' type");
        const tuple = merge;
        let tentries = [];
        if (t.types.some((entry) => entry.isOptional)) {
            this.raiseError(sinfo, "Appending to tuple with optional entries creates ambigious result tuple");
        }
        else {
            //just copy everything along
            tentries = [...t.types, ...tuple.types];
        }
        return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedTupleAtomType.create(tentries));
    }
    mergeIntoRecordAtom(sinfo, t, merge) {
        this.raiseErrorIf(sinfo, !(t instanceof resolved_type_1.ResolvedRecordAtomType), "Cannot merge with 'Record' type");
        const record = merge;
        let rentries = [...t.entries];
        for (let i = 0; i < record.entries.length; ++i) {
            const update = record.entries[i];
            const fidx = rentries.findIndex((e) => e.name === update.name);
            const idx = fidx !== -1 ? fidx : rentries.length;
            if (!update.isOptional) {
                rentries[idx] = new resolved_type_1.ResolvedRecordAtomTypeEntry(update.name, update.type, false);
            }
            else {
                if (idx === rentries.length) {
                    rentries[idx] = update;
                }
                else {
                    rentries[idx] = new resolved_type_1.ResolvedRecordAtomTypeEntry(update.name, this.m_assembly.typeUnion([update.type, rentries[idx].type]), true);
                }
            }
        }
        return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedRecordAtomType.create(rentries));
    }
    checkTypeOkForTupleExpando(sinfo, rtype) {
        const tslist = rtype.options.map((opt) => {
            this.raiseErrorIf(sinfo, !(opt instanceof resolved_type_1.ResolvedTupleAtomType), "Cannot expando on 'Tuple' type argument");
            return opt;
        });
        const reqlen = tslist.reduce((acc, v) => Math.min(acc, v.types.filter((te) => !te.isOptional).length), Number.MAX_SAFE_INTEGER);
        const tlen = tslist.reduce((acc, v) => Math.max(acc, v.types.length), 0);
        return [reqlen, tlen];
    }
    checkTypeOkForRecordExpando(sinfo, rtype) {
        const rslist = rtype.options.map((opt) => {
            this.raiseErrorIf(sinfo, !(opt instanceof resolved_type_1.ResolvedRecordAtomType), "Cannot expando on 'Record' type argument");
            return opt;
        });
        let allNames = new Set();
        rslist.forEach((opt) => {
            opt.entries.forEach((re) => {
                allNames.add(re.name);
            });
        });
        let reqNames = new Set(allNames);
        rslist.forEach((opt) => {
            opt.entries.forEach((re) => {
                if (re.isOptional) {
                    allNames.delete(re.name);
                }
            });
        });
        return [reqNames, allNames];
    }
    checkPCodeExpression(env, exp, expectedFunction) {
        this.raiseErrorIf(exp.sinfo, exp.isAuto && expectedFunction === undefined, "Could not infer auto function type");
        const ltypetry = exp.isAuto ? expectedFunction : this.m_assembly.normalizeTypeFunction(exp.invoke.generateSig(), env.terms);
        this.raiseErrorIf(exp.sinfo, ltypetry === undefined, "Invalid lambda type");
        let captured = new Map();
        let capturedMap = new Map();
        let captures = [];
        exp.invoke.captureSet.forEach((v) => captures.push(v));
        captures.sort();
        captures.forEach((v) => {
            const vinfo = env.lookupVar(v);
            this.raiseErrorIf(exp.sinfo, vinfo.declaredType instanceof resolved_type_1.ResolvedFunctionType, "Cannot capture function typed argument");
            captured.set(v, new mir_ops_1.MIRVariable(v));
            capturedMap.set(v, vinfo.flowType);
        });
        this.m_emitter.registerPCode(exp.invoke, ltypetry, env.terms, [...capturedMap].sort((a, b) => a[0].localeCompare(b[0])));
        return { code: exp.invoke, scope: env.scope, captured: capturedMap, ftype: ltypetry };
    }
    checkArgumentsEvaluationWSig(env, sig, args, optSelfValue, refallowed) {
        let eargs = [];
        if (optSelfValue !== undefined) {
            eargs.push({ name: "this", argtype: optSelfValue[0], ref: undefined, expando: false, pcode: undefined, treg: optSelfValue[1] });
        }
        const skipthisidx = optSelfValue !== undefined ? 1 : 0;
        const noExpando = args.argList.every((arg) => !(arg instanceof body_1.PositionalArgument) || !arg.isSpread);
        const firstNameIdx = sig.params.findIndex((p) => args.argList.some((arg) => arg instanceof body_1.NamedArgument && arg.name !== "_" && arg.name === p.name));
        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            const treg = this.m_emitter.bodyEmitter.generateTmpRegister();
            this.raiseErrorIf(arg.value.sinfo, arg.isRef && !refallowed, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, arg.isRef && arg instanceof body_1.PositionalArgument && arg.isSpread, "Cannot use ref on spread argument");
            if (arg.value instanceof body_1.ConstructorPCodeExpression) {
                const oftype = (noExpando && (firstNameIdx === -1 || i < firstNameIdx) && i < sig.params.length && !sig.params[i].isOptional) ? sig.params[i + skipthisidx].type : this.m_assembly.getSpecialAnyType();
                this.raiseErrorIf(arg.value.sinfo, !(oftype instanceof resolved_type_1.ResolvedFunctionType), "Must have function type for function arg");
                this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params on function argument");
                const pcode = this.checkPCodeExpression(env, arg.value, oftype);
                if (arg instanceof body_1.NamedArgument) {
                    eargs.push({ name: arg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
                else {
                    this.raiseErrorIf(arg.value.sinfo, arg.isSpread, "Cannot have spread on pcode argument");
                    eargs.push({ name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
            }
            else if (arg.value instanceof body_1.AccessVariableExpression && env.pcodes.has(arg.value.name)) {
                const oftype = (noExpando && (firstNameIdx === -1 || i < firstNameIdx) && i < sig.params.length && !sig.params[i].isOptional) ? sig.params[i + skipthisidx].type : this.m_assembly.getSpecialAnyType();
                this.raiseErrorIf(arg.value.sinfo, !(oftype instanceof resolved_type_1.ResolvedFunctionType), "Must have function type for function arg");
                this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params on function argument");
                const pcode = env.pcodes.get(arg.value.name).pcode;
                if (arg instanceof body_1.NamedArgument) {
                    eargs.push({ name: arg.name, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
                else {
                    this.raiseErrorIf(arg.value.sinfo, arg.isSpread, "Cannot have spread on pcode argument");
                    eargs.push({ name: undefined, argtype: pcode.ftype, ref: undefined, expando: false, pcode: pcode, treg: treg });
                }
            }
            else {
                if (arg.isRef) {
                    this.raiseErrorIf(arg.value.sinfo, !(arg.value instanceof body_1.AccessVariableExpression), "Can only ref on variable names");
                    const rvname = arg.value.name;
                    this.raiseErrorIf(arg.value.sinfo, env.lookupVar(rvname) === null, "Variable name is not defined");
                    this.checkExpression(env, arg.value, treg);
                    const earg = env.lookupVar(rvname).declaredType;
                    if (arg instanceof body_1.NamedArgument) {
                        eargs.push({ name: arg.name, argtype: earg, ref: rvname, expando: false, pcode: undefined, treg: treg });
                    }
                    else {
                        eargs.push({ name: undefined, argtype: earg, ref: rvname, expando: false, pcode: undefined, treg: treg });
                    }
                }
                else {
                    const earg = this.checkExpression(env, arg.value, treg).getExpressionResult().etype;
                    if (arg instanceof body_1.NamedArgument) {
                        eargs.push({ name: arg.name, argtype: earg, ref: undefined, expando: false, pcode: undefined, treg: treg });
                    }
                    else {
                        eargs.push({ name: undefined, argtype: earg, ref: undefined, expando: arg.isSpread, pcode: undefined, treg: treg });
                    }
                }
            }
        }
        return eargs;
    }
    checkArgumentsEvaluationNoSig(env, args) {
        let eargs = [];
        for (let i = 0; i < args.argList.length; ++i) {
            const arg = args.argList[i];
            this.raiseErrorIf(arg.value.sinfo, arg.isRef, "Cannot use ref params in this call position");
            this.raiseErrorIf(arg.value.sinfo, arg.value instanceof body_1.ConstructorPCodeExpression, "Cannot use function in this call position");
            const treg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const earg = this.checkExpression(env, arg.value, treg).getExpressionResult().etype;
            if (arg instanceof body_1.NamedArgument) {
                eargs.push({ name: arg.name, argtype: earg, ref: undefined, expando: false, treg: treg, pcode: undefined });
            }
            else {
                eargs.push({ name: undefined, argtype: earg, ref: undefined, expando: arg.isSpread, treg: treg, pcode: undefined });
            }
        }
        return eargs;
    }
    checkArgumentsTupleConstructor(sinfo, env, args, trgt) {
        let targs = [];
        for (let i = 0; i < args.length; ++i) {
            this.raiseErrorIf(sinfo, args[i].expando, "Expando parameters are not allowed in Tuple constructor");
            this.raiseErrorIf(sinfo, args[i].name !== undefined, "Named parameters are not allowed in Tuple constructor");
            this.raiseErrorIf(sinfo, args[i].ref !== undefined, "Cannot use ref params in this call position");
            targs.push(args[i].argtype);
        }
        const tupleatom = resolved_type_1.ResolvedTupleAtomType.create(targs.map((targ) => new resolved_type_1.ResolvedTupleAtomTypeEntry(targ, false)));
        const rtuple = resolved_type_1.ResolvedType.createSingle(tupleatom);
        if (this.m_emitEnabled) {
            const regs = args.map((e) => e.treg);
            const tupkey = this.m_emitter.registerResolvedTypeReference(rtuple);
            this.m_emitter.bodyEmitter.emitConstructorTuple(sinfo, tupkey.trkey, regs, trgt);
        }
        return rtuple;
    }
    checkArgumentsRecordConstructor(sinfo, env, args, trgt) {
        let rargs = [];
        const seenNames = new Set();
        for (let i = 0; i < args.length; ++i) {
            this.raiseErrorIf(sinfo, args[i].expando, "Expando parameters are not allowed in Record constructor");
            this.raiseErrorIf(sinfo, args[i].name === undefined, "Positional parameters are not allowed in Record constructor");
            this.raiseErrorIf(sinfo, args[i].ref !== undefined, "Cannot use ref params in this call position");
            this.raiseErrorIf(sinfo, seenNames.has(args[i].name), "Duplicate argument name in Record constructor");
            rargs.push([args[i].name, args[i].argtype]);
        }
        const rentries = rargs.map((targ) => new resolved_type_1.ResolvedRecordAtomTypeEntry(targ[0], targ[1], false));
        const recordatom = resolved_type_1.ResolvedRecordAtomType.create(rentries);
        const rrecord = resolved_type_1.ResolvedType.createSingle(recordatom);
        if (this.m_emitEnabled) {
            const regs = args.map((e) => [e.name, e.treg]).sort((a, b) => a[0].localeCompare(b[0]));
            const regkey = this.m_emitter.registerResolvedTypeReference(rrecord);
            this.m_emitter.bodyEmitter.emitConstructorRecord(sinfo, regkey.trkey, regs, trgt);
        }
        return rrecord;
    }
    checkArgumentsCollectionConstructor(sinfo, oftype, ctype, args, trgt) {
        for (let i = 0; i < args.length; ++i) {
            this.raiseErrorIf(sinfo, args[i].name !== undefined, "Named parameters are not allowed in Collection constructors");
            this.raiseErrorIf(sinfo, args[i].ref !== undefined, "Cannot use ref params in this call position");
            const arg = args[i];
            if (!arg.expando) {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(arg.argtype, ctype));
            }
            else {
                arg.argtype.options.forEach((opt) => {
                    this.raiseErrorIf(sinfo, !(opt instanceof resolved_type_1.ResolvedEntityAtomType) || !(opt.object.isTypeACollectionEntity() || opt.object.isTypeAMapEntity()), "Can only expand other container types in container constructor");
                    const oatom = opt;
                    if (oatom.object.isTypeACollectionEntity()) {
                        const ttype = oatom.binds.get("T");
                        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(ttype, ctype), "Container contents not of suitable subtype");
                    }
                    else {
                        const ktype = oatom.binds.get("K");
                        const vtype = oatom.binds.get("V");
                        const tupleType = resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedTupleAtomType.create([new resolved_type_1.ResolvedTupleAtomTypeEntry(ktype, false), new resolved_type_1.ResolvedTupleAtomTypeEntry(vtype, false)]));
                        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(tupleType, ctype), "Container contents not of suitable subtype");
                    }
                });
            }
        }
        if (this.m_emitEnabled) {
            this.m_emitter.registerResolvedTypeReference(resolved_type_1.ResolvedType.createSingle(oftype));
            this.m_emitter.registerTypeInstantiation(oftype.object, oftype.binds);
            const tkey = mir_emitter_1.MIRKeyGenerator.generateTypeKey(oftype.object, oftype.binds);
            if (args.length === 0) {
                this.m_emitter.bodyEmitter.emitConstructorPrimaryCollectionEmpty(sinfo, tkey, trgt);
            }
            else {
                if (oftype.object.name === "Set") {
                    const sdecl = oftype.object.staticFunctions.get("_cons_insert");
                    this.m_emitter.registerStaticCall(oftype.object, oftype.binds, sdecl, "_cons_insert", oftype.binds, [], []);
                }
                if (oftype.object.name === "Map") {
                    const sdecl = oftype.object.staticFunctions.get("_cons_insert");
                    this.m_emitter.registerStaticCall(oftype.object, oftype.binds, sdecl, "_cons_insert", oftype.binds, [], []);
                }
                if (args.every((v) => !v.expando)) {
                    this.m_emitter.bodyEmitter.emitConstructorPrimaryCollectionSingletons(sinfo, tkey, args.map((arg) => arg.treg), trgt);
                }
                else if (args.every((v) => v.expando)) {
                    this.m_emitter.bodyEmitter.emitConstructorPrimaryCollectionCopies(sinfo, tkey, args.map((arg) => arg.treg), trgt);
                }
                else {
                    this.m_emitter.bodyEmitter.emitConstructorPrimaryCollectionMixed(sinfo, tkey, args.map((arg) => [arg.expando, arg.treg]), trgt);
                }
            }
        }
        return resolved_type_1.ResolvedType.createSingle(oftype);
    }
    checkArgumentsConstructor(sinfo, oftype, args, trgt) {
        const fieldInfo = this.m_assembly.getAllOOFields(oftype.object, oftype.binds);
        let fields = [];
        fieldInfo.forEach((v, k) => {
            fields.push(k);
        });
        fields = fields.sort();
        let filledLocations = [];
        //figure out named parameter mapping first
        for (let i = 0; i < args.length; ++i) {
            const arg = args[i];
            this.raiseErrorIf(sinfo, args[i].ref !== undefined, "Cannot use ref params in this call position");
            if (arg.name !== undefined) {
                const fidx = fields.indexOf(arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.idStr} does not have field named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${arg.name}"`);
                filledLocations[fidx] = { vtype: arg.argtype, mustDef: true, trgt: arg.treg };
            }
            else if (arg.expando && this.m_assembly.subtypeOf(arg.argtype, this.m_assembly.getSpecialRecordConceptType())) {
                const expandInfo = this.checkTypeOkForRecordExpando(sinfo, arg.argtype);
                this.raiseErrorIf(sinfo, !expandInfo[0], `Type cannot be expanded as part of Entity constructor ${arg.argtype.idStr}`);
                expandInfo[1].forEach((pname) => {
                    const fidx = fields.indexOf(pname);
                    this.raiseErrorIf(sinfo, fidx === -1, `Entity ${oftype.idStr} does not have field named "${pname}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);
                    this.raiseErrorIf(sinfo, fieldInfo.get(pname)[1].value !== undefined && !expandInfo[1].has(pname), `Constructor requires "${pname}" but it is provided as an optional argument`);
                    const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromPropertyName(arg.argtype, pname);
                    if (this.m_emitEnabled) {
                        const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);
                        this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, ptype.trkey, arg.treg, pname, etreg);
                    }
                    filledLocations[fidx] = { vtype: lvtype, mustDef: expandInfo[1].has(pname), trgt: etreg };
                });
            }
            else {
                //nop
            }
        }
        //go through names and fill out info for any that should use the default value -- raise error if any are missing
        for (let i = 0; i < fields.length; ++i) {
            const field = fieldInfo.get(fields[i]);
            const fieldtype = this.resolveAndEnsureTypeOnly(sinfo, field[1].declaredType, field[2]);
            if (filledLocations[i] === undefined) {
                this.raiseErrorIf(sinfo, field[1].value === undefined, `Field "${fields[i]}" is required and must be assigned a value in constructor`);
                const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                if (this.m_emitEnabled) {
                    this.m_emitter.bodyEmitter.emitLoadMemberFieldDefaultValue(sinfo, mir_emitter_1.MIRKeyGenerator.generateFieldKey(field[0], field[2], field[1].name), etreg);
                }
                filledLocations[i] = { vtype: fieldtype, mustDef: true, trgt: etreg };
            }
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(filledLocations[i].vtype, fieldtype), `Field "${fields[i]}" expected argument of type ${fieldtype.idStr} but got ${filledLocations[i].vtype.idStr}`);
        }
        if (this.m_emitEnabled) {
            this.m_emitter.registerResolvedTypeReference(resolved_type_1.ResolvedType.createSingle(oftype));
            this.m_emitter.registerTypeInstantiation(oftype.object, oftype.binds);
            const tkey = mir_emitter_1.MIRKeyGenerator.generateTypeKey(oftype.object, oftype.binds);
            this.m_emitter.bodyEmitter.emitConstructorPrimary(sinfo, tkey, filledLocations.map((fl) => fl.trgt), trgt);
        }
        return resolved_type_1.ResolvedType.createSingle(oftype);
    }
    checkArgumentsSignature(sinfo, env, sig, args) {
        let filledLocations = [];
        //figure out named parameter mapping first
        for (let j = 0; j < args.length; ++j) {
            const arg = args[j];
            if (arg.name !== undefined) {
                const fidx = sig.params.findIndex((param) => param.name === arg.name);
                this.raiseErrorIf(sinfo, fidx === -1, `Call does not have parameter named "${arg.name}"`);
                this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name ${arg.name}`);
                filledLocations[fidx] = { vtype: arg.argtype, mustDef: true, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
            }
            else if (arg.expando && this.m_assembly.subtypeOf(arg.argtype, this.m_assembly.getSpecialRecordConceptType())) {
                const expandInfo = this.checkTypeOkForRecordExpando(sinfo, arg.argtype);
                this.raiseErrorIf(sinfo, !expandInfo[0], "Type cannot be expanded as part of call");
                expandInfo[1].forEach((pname) => {
                    const fidx = sig.params.findIndex((param) => param.name === pname);
                    this.raiseErrorIf(sinfo, fidx === -1, `Call does not have parameter named "${pname}"`);
                    this.raiseErrorIf(sinfo, filledLocations[fidx] !== undefined, `Duplicate definition of parameter name "${pname}"`);
                    this.raiseErrorIf(sinfo, !sig.params[fidx].isOptional && !expandInfo[1].has(pname), `Call requires "${pname}" but it is provided as an optional argument`);
                    const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromPropertyName(arg.argtype, pname);
                    if (this.m_emitEnabled) {
                        const ptype = this.m_emitter.registerResolvedTypeReference(lvtype);
                        this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, ptype.trkey, arg.treg, pname, etreg);
                    }
                    filledLocations[fidx] = { vtype: lvtype, mustDef: expandInfo[1].has(pname), ref: undefined, pcode: undefined, trgt: etreg };
                });
            }
            else {
                //nop
            }
        }
        //now fill in positional parameters
        let apos = args.findIndex((ae) => ae.name === undefined && !(ae.expando && this.m_assembly.subtypeOf(ae.argtype, this.m_assembly.getSpecialRecordConceptType())));
        if (apos === -1) {
            apos = args.length;
        }
        let ii = 0;
        while (ii < sig.params.length && apos < args.length) {
            if (filledLocations[ii] !== undefined) {
                this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
                ++ii;
                continue;
            }
            const arg = args[apos];
            if (!arg.expando) {
                filledLocations[ii] = { vtype: arg.argtype, mustDef: true, ref: arg.ref, pcode: arg.pcode, trgt: arg.treg };
                ++ii;
            }
            else {
                this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(arg.argtype, this.m_assembly.getSpecialTupleConceptType()), "Only Tuple types can be expanded as positional arguments");
                const expandInfo = this.checkTypeOkForTupleExpando(sinfo, arg.argtype);
                for (let ectr = 0; ectr < expandInfo[1]; ++ectr) {
                    this.raiseErrorIf(sinfo, ii >= sig.params.length, "Too many arguments as part of tuple expando and/or cannot split tuple expando (between arguments and rest)");
                    this.raiseErrorIf(sinfo, !sig.params[ii].isOptional && ectr >= expandInfo[1], `Call requires "${sig.params[ii].name}" but it is provided as an optional argument as part of tuple expando`);
                    const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                    const lvtype = this.getInfoForLoadFromIndex(arg.argtype, ectr);
                    if (this.m_emitEnabled) {
                        const itype = this.m_emitter.registerResolvedTypeReference(lvtype);
                        this.m_emitter.bodyEmitter.emitLoadTupleIndex(sinfo, itype.trkey, arg.treg, ectr, etreg);
                    }
                    filledLocations[ii] = { vtype: lvtype, mustDef: ectr < expandInfo[1], ref: undefined, pcode: undefined, trgt: etreg };
                    while (filledLocations[ii] !== undefined) {
                        this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
                        ii++;
                    }
                }
            }
            apos++;
            while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && this.m_assembly.subtypeOf(args[apos].argtype, this.m_assembly.getSpecialRecordConceptType())))) {
                apos++;
            }
        }
        while (filledLocations[ii] !== undefined) {
            this.raiseErrorIf(sinfo, !filledLocations[ii].mustDef, `We have an potentially ambigious binding of an optional parameter "${sig.params[ii].name}"`);
            ii++;
        }
        while (apos < args.length && (args[apos].name !== undefined || (args[apos].expando && this.m_assembly.subtypeOf(args[apos].argtype, this.m_assembly.getSpecialRecordConceptType())))) {
            apos++;
        }
        if (ii < sig.params.length) {
            this.raiseErrorIf(sinfo, !sig.params[ii].isOptional, `Insufficient number of parameters -- missing value for ${sig.params[ii].name}`);
        }
        else {
            this.raiseErrorIf(sinfo, apos !== args.length && sig.optRestParamType === undefined, "Too many arguments for call");
        }
        //go through names and fill out info for any that should use the default value -- raise error if any are missing
        //check ref, pcode, and regular arg types -- plus build up emit data
        let margs = [];
        let mtypes = [];
        let pcodes = [];
        let refs = [];
        for (let j = 0; j < sig.params.length; ++j) {
            const paramtype = sig.params[j].type;
            if (filledLocations[j] === undefined) {
                this.raiseErrorIf(sinfo, !sig.params[j].isOptional, `Parameter ${sig.params[j].name} is required and must be assigned a value in constructor`);
                filledLocations[j] = { vtype: paramtype, mustDef: true, ref: undefined, pcode: undefined, trgt: new mir_ops_1.MIRConstantNone() };
            }
            if (sig.params[j].type instanceof resolved_type_1.ResolvedFunctionType) {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode === undefined, `Parameter ${sig.params[j].name} expected a function`);
                this.raiseErrorIf(sinfo, !this.m_assembly.functionSubtypeOf(filledLocations[j].vtype, paramtype), `Parameter ${sig.params[j].name} expected function of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);
                pcodes.push(filledLocations[j].pcode);
            }
            else {
                this.raiseErrorIf(sinfo, filledLocations[j].pcode !== undefined, `Parameter ${sig.params[j].name} cannot take a function`);
                if (sig.params[j].isRef) {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref === undefined, `Parameter ${sig.params[j].name} expected reference parameter`);
                    this.raiseErrorIf(sinfo, filledLocations[j].vtype.idStr !== paramtype.idStr, `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);
                    refs.push(filledLocations[j].ref);
                    margs.push(filledLocations[j].trgt);
                    mtypes.push(filledLocations[j].vtype);
                }
                else {
                    this.raiseErrorIf(sinfo, filledLocations[j].ref !== undefined, `Parameter ${sig.params[j].name} reference parameter is not alloed in this position`);
                    this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(filledLocations[j].vtype, paramtype), `Parameter ${sig.params[j].name} expected argument of type ${paramtype.idStr} but got ${filledLocations[j].vtype.idStr}`);
                    margs.push(filledLocations[j].trgt);
                    mtypes.push(filledLocations[j].vtype);
                }
            }
        }
        //if this has a rest parameter check it
        if (sig.optRestParamType !== undefined) {
            const objtype = resolved_type_1.ResolvedType.tryGetOOTypeInfo(sig.optRestParamType);
            this.raiseErrorIf(sinfo, objtype === undefined || !(objtype instanceof resolved_type_1.ResolvedEntityAtomType), "Invalid rest type");
            const oodecl = objtype.object;
            const oobinds = objtype.binds;
            const oftype = resolved_type_1.ResolvedEntityAtomType.create(oodecl, oobinds);
            const rargs = args.slice(apos).filter((arg) => arg.name === undefined);
            const rtreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            if (oodecl.isTypeACollectionEntity()) {
                this.checkArgumentsCollectionConstructor(sinfo, oftype, oobinds.get("T"), rargs, rtreg);
            }
            else {
                const contentstype = resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedTupleAtomType.create([new resolved_type_1.ResolvedTupleAtomTypeEntry(oobinds.get("K"), false), new resolved_type_1.ResolvedTupleAtomTypeEntry(oobinds.get("V"), false)]));
                this.checkArgumentsCollectionConstructor(sinfo, oftype, contentstype, rargs, rtreg);
            }
            margs.push(rtreg);
            mtypes.push(resolved_type_1.ResolvedType.createSingle(oftype));
        }
        //take all the pcodes and pass the "captured" variables in as arguments in alpha order
        let cinfo = [];
        if (pcodes.length !== 0) {
            let allcaptured = new Set();
            pcodes.forEach((pc) => pc.captured.forEach((v, k) => allcaptured.add(k)));
            const cnames = [...allcaptured].sort();
            for (let i = 0; i < cnames.length; ++i) {
                const vinfo = env.lookupVar(cnames[i]);
                margs.push(new mir_ops_1.MIRVariable(vinfo.isCaptured ? this.m_emitter.bodyEmitter.generateCapturedVarName(cnames[i]) : cnames[i]));
                mtypes.push(vinfo.flowType);
                cinfo.push([cnames[i], vinfo.flowType]);
            }
        }
        return { args: margs, types: mtypes, refs: refs, pcodes: pcodes, cinfo: cinfo };
    }
    generateRefInfoForCallEmit(fsig, refs) {
        const rtype = this.m_emitter.registerResolvedTypeReference(fsig.resultType);
        const refinfo = refs.map((rn) => {
            const rp = fsig.params.find((p) => p.name === rn);
            const ptk = this.m_emitter.registerResolvedTypeReference(rp.type);
            return [rn, ptk];
        });
        return [rtype, refinfo];
    }
    generateRefInfoForReturnEmit(rtype, env) {
        if (env.refparams.length === 0) {
            return undefined;
        }
        else {
            const entries = [
                new resolved_type_1.ResolvedTupleAtomTypeEntry(rtype, false),
                ...env.refparams.map((rn) => new resolved_type_1.ResolvedTupleAtomTypeEntry(env.lookupVar(rn).declaredType, false))
            ];
            return this.m_emitter.registerResolvedTypeReference(resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedTupleAtomType.create(entries))).trkey;
        }
    }
    checkLiteralNoneExpression(env, exp, trgt) {
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitLoadConstNone(exp.sinfo, trgt);
        }
        return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialNoneType(), type_environment_1.FlowTypeTruthValue.False)];
    }
    checkLiteralBoolExpression(env, exp, trgt) {
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, exp.value, trgt);
        }
        return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), exp.value ? type_environment_1.FlowTypeTruthValue.True : type_environment_1.FlowTypeTruthValue.False)];
    }
    checkLiteralIntegerExpression(env, exp, trgt) {
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitLoadConstInt(exp.sinfo, exp.value, trgt);
        }
        return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialIntType())];
    }
    checkLiteralStringExpression(env, exp, trgt) {
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitLoadConstString(exp.sinfo, exp.value, trgt);
        }
        return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialStringType())];
    }
    checkTypedStringCommon(sinfo, env, ttype) {
        const oftype = this.resolveAndEnsureTypeOnly(sinfo, ttype, env.terms);
        //do dynamic check to see if string is valid of format
        this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(oftype, this.m_assembly.getSpecialParsableConcept()), "Type must provide 'Parsable' concept");
        const fdecltry = this.m_assembly.tryGetOOMemberDeclUnique(oftype, "static", "tryParse");
        this.raiseErrorIf(sinfo, fdecltry === undefined, `Constant value not defined for type '${oftype.idStr}'`);
        const aoftype = resolved_type_1.ResolvedType.tryGetOOTypeInfo(oftype);
        this.raiseErrorIf(sinfo, aoftype === undefined, "Can only make string type using concept or object types");
        const oodecl = (aoftype instanceof resolved_type_1.ResolvedEntityAtomType) ? aoftype.object : aoftype.conceptTypes[0].concept;
        const oobinds = (aoftype instanceof resolved_type_1.ResolvedEntityAtomType) ? aoftype.binds : aoftype.conceptTypes[0].binds;
        //ensure full string[T] type is registered
        const terms = [new type_signature_1.TemplateTypeSignature("T")];
        const binds = new Map().set("T", oftype);
        const stype = this.resolveAndEnsureTypeOnly(sinfo, new type_signature_1.NominalTypeSignature("NSCore", "StringOf", terms), binds);
        return { oftype: [oodecl, oobinds], ofresolved: oftype, stringtype: stype };
    }
    checkCreateTypedString(env, exp, trgt) {
        const aoftype = this.checkTypedStringCommon(exp.sinfo, env, exp.stype);
        if (this.m_emitEnabled) {
            this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);
            this.m_emitter.registerTypeInstantiation(...aoftype.oftype);
            const stype = this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);
            const sdecl = aoftype.oftype[0].staticFunctions.get("tryParse");
            this.raiseErrorIf(exp.sinfo, sdecl === undefined, "Missing static function 'tryParse'");
            const pfunckey = this.m_emitter.registerStaticCall(aoftype.oftype[0], aoftype.oftype[1], sdecl, "tryParse", aoftype.oftype[1], [], []);
            //
            //TODO -- should emit parse checking code here
            //
            this.m_emitter.bodyEmitter.emitLoadConstTypedString(exp.sinfo, exp.value, mir_emitter_1.MIRKeyGenerator.generateTypeKey(...aoftype.oftype), stype.trkey, pfunckey, trgt);
        }
        return [env.setExpressionResult(this.m_assembly, aoftype.stringtype)];
    }
    checkTypedStringConstructor(env, exp, trgt) {
        const aoftype = this.checkTypedStringCommon(exp.sinfo, env, exp.stype);
        const sdecl = aoftype.oftype[0].staticFunctions.get("tryParse");
        this.raiseErrorIf(exp.sinfo, sdecl === undefined, "Missing static function 'tryParse'");
        if (this.m_emitEnabled) {
            this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);
            this.m_emitter.registerTypeInstantiation(...aoftype.oftype);
            const stype = this.m_emitter.registerResolvedTypeReference(aoftype.stringtype);
            const skey = this.m_emitter.registerStaticCall(aoftype.oftype[0], aoftype.oftype[1], sdecl, "tryParse", aoftype.oftype[1], [], []);
            const tmpr = this.m_emitter.bodyEmitter.generateTmpRegister();
            this.m_emitter.bodyEmitter.emitLoadConstString(exp.sinfo, exp.value, tmpr);
            this.m_emitter.bodyEmitter.emitInvokeFixedFunction(this.m_emitter.masm, exp.sinfo, stype, skey, [tmpr], [], trgt);
            //
            //TODO -- should emit parse checking code here
            //
        }
        return [env.setExpressionResult(this.m_assembly, aoftype.ofresolved)];
    }
    checkAccessNamespaceConstant(env, exp, trgt) {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);
        this.raiseErrorIf(exp.sinfo, !nsdecl.consts.has(exp.name), `Constant named '${exp.name}' is not defined`);
        const cdecl = nsdecl.consts.get(exp.name);
        const rtype = this.resolveAndEnsureTypeOnly(exp.sinfo, cdecl.declaredType, new Map());
        if (this.m_emitEnabled) {
            const gkey = this.m_emitter.registerPendingGlobalProcessing(cdecl);
            this.m_emitter.bodyEmitter.emitAccessConstant(exp.sinfo, gkey, trgt);
        }
        return [env.setExpressionResult(this.m_assembly, rtype)];
    }
    checkAccessStaticField(env, exp, trgt) {
        const baseType = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.stype, env.terms);
        const cdecltry = this.m_assembly.tryGetOOMemberDeclUnique(baseType, "const", exp.name);
        this.raiseErrorIf(exp.sinfo, cdecltry === undefined, `Constant value not defined for type '${baseType.idStr}'`);
        const cdecl = cdecltry;
        const rtype = this.resolveAndEnsureTypeOnly(exp.sinfo, cdecl.decl.declaredType, cdecl.binds);
        if (this.m_emitEnabled) {
            this.m_emitter.registerResolvedTypeReference(baseType);
            this.m_emitter.registerTypeInstantiation(cdecl.contiainingType, cdecl.binds);
            const skey = this.m_emitter.registerPendingConstProcessing(cdecl.contiainingType, cdecl.decl, cdecl.binds);
            this.m_emitter.bodyEmitter.emitAccessConstant(exp.sinfo, skey, trgt);
        }
        return [env.setExpressionResult(this.m_assembly, rtype)];
    }
    checkAccessVariable(env, exp, trgt) {
        this.raiseErrorIf(exp.sinfo, !env.isVarNameDefined(exp.name), `Variable name '${exp.name}' is not defined`);
        if (this.m_emitEnabled) {
            if (env.getLocalVarInfo(exp.name) !== undefined) {
                this.m_emitter.bodyEmitter.emitAccessLocalVariable(exp.sinfo, exp.name, trgt);
            }
            else {
                if (env.lookupVar(exp.name).isCaptured) {
                    this.m_emitter.bodyEmitter.emitAccessArgVariable(exp.sinfo, this.m_emitter.bodyEmitter.generateCapturedVarName(exp.name), trgt);
                }
                else {
                    this.m_emitter.bodyEmitter.emitAccessArgVariable(exp.sinfo, exp.name, trgt);
                }
            }
        }
        const vinfo = env.lookupVar(exp.name);
        this.raiseErrorIf(exp.sinfo, !vinfo.mustDefined, "Var may not be defined at use");
        return [env.setExpressionResult(this.m_assembly, vinfo.flowType)];
    }
    checkConstructorPrimary(env, exp, trgt) {
        const ctype = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ctype, env.terms);
        const objtype = resolved_type_1.ResolvedType.tryGetOOTypeInfo(ctype);
        this.raiseErrorIf(exp.sinfo, objtype === undefined || !(objtype instanceof resolved_type_1.ResolvedEntityAtomType), "Invalid constructor type");
        const oodecl = objtype.object;
        const oobinds = objtype.binds;
        this.checkTemplateTypes(exp.sinfo, oodecl.terms, oobinds);
        const eargs = this.checkArgumentsEvaluationNoSig(env, exp.args);
        const oftype = resolved_type_1.ResolvedEntityAtomType.create(oodecl, oobinds);
        if (oodecl.isTypeACollectionEntity()) {
            return [env.setExpressionResult(this.m_assembly, this.checkArgumentsCollectionConstructor(exp.sinfo, oftype, oobinds.get("T"), eargs, trgt))];
        }
        else if (oodecl.isTypeAMapEntity()) {
            const contentstype = resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedTupleAtomType.create([new resolved_type_1.ResolvedTupleAtomTypeEntry(oobinds.get("K"), false), new resolved_type_1.ResolvedTupleAtomTypeEntry(oobinds.get("V"), false)]));
            return [env.setExpressionResult(this.m_assembly, this.checkArgumentsCollectionConstructor(exp.sinfo, oftype, contentstype, eargs, trgt))];
        }
        else {
            return [env.setExpressionResult(this.m_assembly, this.checkArgumentsConstructor(exp.sinfo, oftype, eargs, trgt))];
        }
    }
    checkConstructorPrimaryWithFactory(env, exp, trgt, refok) {
        const baseType = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ctype, env.terms);
        const objtype = resolved_type_1.ResolvedType.tryGetOOTypeInfo(baseType);
        this.raiseErrorIf(exp.sinfo, objtype === undefined || !(objtype instanceof resolved_type_1.ResolvedEntityAtomType), "Invalid constructor type");
        const oodecl = objtype.object;
        const oobinds = objtype.binds;
        this.raiseErrorIf(exp.sinfo, !(oodecl instanceof assembly_1.EntityTypeDecl), "Can only construct concrete entities");
        this.checkTemplateTypes(exp.sinfo, oodecl.terms, oobinds);
        const fdecl = oodecl.staticFunctions.get(exp.factoryName);
        this.raiseErrorIf(exp.sinfo, fdecl === undefined || !assembly_1.OOPTypeDecl.attributeSetContains("factory", fdecl.attributes), `Function is not a factory function for type '${baseType.idStr}'`);
        const binds = this.m_assembly.resolveBindsForCall(fdecl.invoke.terms, exp.terms.targs, oobinds, env.terms);
        this.raiseErrorIf(exp.sinfo, binds === undefined, "Call bindings could not be resolved");
        this.checkTemplateTypes(exp.sinfo, fdecl.invoke.terms, binds);
        const fsig = this.m_assembly.normalizeTypeFunction(fdecl.invoke.generateSig(), binds);
        this.raiseErrorIf(exp.sinfo, fsig === undefined, "Invalid function signature");
        const eargs = this.checkArgumentsEvaluationWSig(env, fsig, exp.args, undefined, refok);
        const rargs = this.checkArgumentsSignature(exp.sinfo, env, fsig, eargs);
        this.checkRecursion(exp.sinfo, fsig, rargs.pcodes, exp.pragmas.recursive);
        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        if (this.m_emitEnabled) {
            this.m_emitter.registerResolvedTypeReference(baseType);
            this.m_emitter.registerTypeInstantiation(oodecl, oobinds);
            const skey = this.m_emitter.registerStaticCall(oodecl, oobinds, fdecl, exp.factoryName, binds, rargs.pcodes, rargs.cinfo);
            const [frtype, refinfo] = this.generateRefInfoForCallEmit(fsig, rargs.refs);
            this.m_emitter.bodyEmitter.emitInvokeFixedFunction(this.m_emitter.masm, exp.sinfo, frtype, skey, rargs.args, refinfo, etreg);
        }
        const oftype = resolved_type_1.ResolvedEntityAtomType.create(oodecl, oobinds);
        const returntype = fsig.resultType;
        return [env.setExpressionResult(this.m_assembly, this.checkArgumentsConstructor(exp.sinfo, oftype, [{ name: undefined, argtype: returntype, expando: true, ref: undefined, pcode: undefined, treg: etreg }], trgt))];
    }
    checkTupleConstructor(env, exp, trgt) {
        const eargs = this.checkArgumentsEvaluationNoSig(env, exp.args);
        return [env.setExpressionResult(this.m_assembly, this.checkArgumentsTupleConstructor(exp.sinfo, env, eargs, trgt))];
    }
    checkRecordConstructor(env, exp, trgt) {
        const eargs = this.checkArgumentsEvaluationNoSig(env, exp.args);
        return [env.setExpressionResult(this.m_assembly, this.checkArgumentsRecordConstructor(exp.sinfo, env, eargs, trgt))];
    }
    checkCallNamespaceFunctionExpression(env, exp, trgt, refok) {
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.hasNamespace(exp.ns), `Namespace '${exp.ns}' is not defined`);
        const nsdecl = this.m_assembly.getNamespace(exp.ns);
        this.raiseErrorIf(exp.sinfo, !nsdecl.functions.has(exp.name), `Function named '${exp.name}' is not defined`);
        const fdecl = nsdecl.functions.get(exp.name);
        const binds = this.m_assembly.resolveBindsForCall(fdecl.invoke.terms, exp.terms.targs, new Map(), env.terms);
        this.raiseErrorIf(exp.sinfo, binds === undefined, "Call bindings could not be resolved");
        this.checkTemplateTypes(exp.sinfo, fdecl.invoke.terms, binds);
        const fsig = this.m_assembly.normalizeTypeFunction(fdecl.invoke.generateSig(), binds);
        this.raiseErrorIf(exp.sinfo, fsig === undefined, "Invalid function signature");
        const eargs = this.checkArgumentsEvaluationWSig(env, fsig, exp.args, undefined, refok);
        const margs = this.checkArgumentsSignature(exp.sinfo, env, fsig, eargs);
        this.checkRecursion(exp.sinfo, fsig, margs.pcodes, exp.pragmas.recursive);
        if (this.m_emitEnabled) {
            const ckey = this.m_emitter.registerFunctionCall(exp.ns, exp.name, fdecl, binds, margs.pcodes, margs.cinfo);
            const [frtype, refinfo] = this.generateRefInfoForCallEmit(fsig, margs.refs);
            this.m_emitter.bodyEmitter.emitInvokeFixedFunction(this.m_emitter.masm, exp.sinfo, frtype, ckey, margs.args, refinfo, trgt);
        }
        return [env.setExpressionResult(this.m_assembly, this.resolveAndEnsureTypeOnly(exp.sinfo, fdecl.invoke.resultType, binds))];
    }
    checkCallStaticFunctionExpression(env, exp, trgt, refok) {
        const baseType = this.resolveAndEnsureTypeOnly(exp.sinfo, exp.ttype, env.terms);
        const fdecltry = this.m_assembly.tryGetOOMemberDeclUnique(baseType, "static", exp.name);
        this.raiseErrorIf(exp.sinfo, fdecltry === undefined, `Constant value not defined for type '${baseType.idStr}'`);
        const fdecl = fdecltry;
        const binds = this.m_assembly.resolveBindsForCall(fdecl.decl.invoke.terms, exp.terms.targs, fdecl.binds, env.terms);
        this.raiseErrorIf(exp.sinfo, binds === undefined, "Call bindings could not be resolved");
        this.checkTemplateTypes(exp.sinfo, fdecl.decl.invoke.terms, binds);
        const fsig = this.m_assembly.normalizeTypeFunction(fdecl.decl.invoke.generateSig(), binds);
        this.raiseErrorIf(exp.sinfo, fsig === undefined, "Invalid function signature");
        const eargs = this.checkArgumentsEvaluationWSig(env, fsig, exp.args, undefined, refok);
        const margs = this.checkArgumentsSignature(exp.sinfo, env, fsig, eargs);
        this.checkRecursion(exp.sinfo, fsig, margs.pcodes, exp.pragmas.recursive);
        if (this.m_emitEnabled) {
            const isindexableop = fdecl.contiainingType.ns === "NSCore" && fdecl.contiainingType.name === "Indexable";
            const keytype = this.m_assembly.getSpecialKeyTypeConcept();
            const mirkeytype = this.m_emitter.registerResolvedTypeReference(keytype);
            if (isindexableop && exp.name === "getKey") {
                const mirargtypeinfer = this.m_emitter.registerResolvedTypeReference(margs.types[0]);
                if (this.m_assembly.subtypeOf(margs.types[0], keytype)) {
                    this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, margs.args[0], trgt);
                }
                else {
                    //
                    // TODO: we should infer the keytype from the Indexable info to do a better emit and type inference
                    //
                    this.m_emitter.bodyEmitter.emitGetKey(exp.sinfo, mirargtypeinfer.trkey, margs.args[0], mirkeytype.trkey, trgt);
                }
            }
            else if (isindexableop && exp.name === "equal") {
                let mirargtypeinferlhs = this.m_emitter.registerResolvedTypeReference(margs.types[0]);
                let mirargtypeinferrhs = this.m_emitter.registerResolvedTypeReference(margs.types[1]);
                let lhs = margs.args[0];
                if (!this.m_assembly.subtypeOf(margs.types[0], keytype)) {
                    lhs = this.m_emitter.bodyEmitter.generateTmpRegister();
                    this.m_emitter.bodyEmitter.emitGetKey(exp.sinfo, mirargtypeinferlhs.trkey, margs.args[0], mirkeytype.trkey, lhs);
                    mirargtypeinferlhs = mirkeytype;
                }
                let rhs = margs.args[0];
                if (!this.m_assembly.subtypeOf(margs.types[1], keytype)) {
                    rhs = this.m_emitter.bodyEmitter.generateTmpRegister();
                    this.m_emitter.bodyEmitter.emitGetKey(exp.sinfo, mirargtypeinferrhs.trkey, margs.args[1], mirkeytype.trkey, rhs);
                    mirargtypeinferrhs = mirkeytype;
                }
                //
                // TODO: we should infer the keytype from the Indexable info to do a better emit and type inference
                //
                this.m_emitter.bodyEmitter.emitBinEq(exp.sinfo, mirargtypeinferlhs.trkey, lhs, mirargtypeinferrhs.trkey, "==", rhs, trgt);
            }
            else if (isindexableop && exp.name === "less") {
                let mirargtypeinferlhs = this.m_emitter.registerResolvedTypeReference(margs.types[0]);
                let mirargtypeinferrhs = this.m_emitter.registerResolvedTypeReference(margs.types[1]);
                let lhs = margs.args[0];
                if (!this.m_assembly.subtypeOf(margs.types[0], keytype)) {
                    lhs = this.m_emitter.bodyEmitter.generateTmpRegister();
                    this.m_emitter.bodyEmitter.emitGetKey(exp.sinfo, mirargtypeinferlhs.trkey, margs.args[0], mirkeytype.trkey, lhs);
                    mirargtypeinferlhs = mirkeytype;
                }
                let rhs = margs.args[0];
                if (!this.m_assembly.subtypeOf(margs.types[1], keytype)) {
                    rhs = this.m_emitter.bodyEmitter.generateTmpRegister();
                    this.m_emitter.bodyEmitter.emitGetKey(exp.sinfo, mirargtypeinferrhs.trkey, margs.args[1], mirkeytype.trkey, rhs);
                    mirargtypeinferrhs = mirkeytype;
                }
                //
                // TODO: we should infer the keytype from the Indexable info to do a better emit and type inference
                //
                this.m_emitter.bodyEmitter.emitBinCmp(exp.sinfo, mirargtypeinferlhs.trkey, lhs, mirargtypeinferrhs.trkey, "<", rhs, trgt);
            }
            else {
                this.m_emitter.registerResolvedTypeReference(baseType);
                this.m_emitter.registerTypeInstantiation(fdecl.contiainingType, fdecl.binds);
                const skey = this.m_emitter.registerStaticCall(fdecl.contiainingType, fdecl.binds, fdecl.decl, fdecl.decl.name, binds, margs.pcodes, margs.cinfo);
                const [frtype, refinfo] = this.generateRefInfoForCallEmit(fsig, margs.refs);
                this.m_emitter.bodyEmitter.emitInvokeFixedFunction(this.m_emitter.masm, exp.sinfo, frtype, skey, margs.args, refinfo, trgt);
            }
        }
        return [env.setExpressionResult(this.m_assembly, this.resolveAndEnsureTypeOnly(exp.sinfo, fdecl.decl.invoke.resultType, binds))];
    }
    checkPCodeInvokeExpression(env, exp, trgt) {
        const pco = env.lookupPCode(exp.pcode);
        this.raiseErrorIf(exp.sinfo, pco === undefined, "Code name not defined");
        const pcode = pco.pcode;
        const captured = pco.captured;
        const cargs = [...exp.args.argList, ...captured.map((cv) => new body_1.PositionalArgument(false, false, new body_1.AccessVariableExpression(exp.sinfo, cv)))];
        const eargs = this.checkArgumentsEvaluationWSig(env, pcode.ftype, new body_1.Arguments(cargs), undefined, false);
        const margs = this.checkArgumentsSignature(exp.sinfo, env, pcode.ftype, eargs);
        this.checkRecursion(exp.sinfo, pcode.ftype, margs.pcodes, exp.pragmas.recursive);
        if (this.m_emitEnabled) {
            const ftype = this.m_emitter.registerResolvedTypeReference(pcode.ftype.resultType);
            this.m_emitter.bodyEmitter.emitInvokeFixedFunction(this.m_emitter.masm, exp.sinfo, ftype, mir_emitter_1.MIRKeyGenerator.generatePCodeKey(pcode.code), margs.args, [], trgt);
        }
        return [env.setExpressionResult(this.m_assembly, pcode.ftype.resultType)];
    }
    checkAccessFromIndex(env, op, arg, trgt) {
        const texp = env.getExpressionResult().etype;
        this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType()), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.index < 0, "Index cannot be negative");
        const idxtype = this.getInfoForLoadFromIndex(texp, op.index);
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitLoadTupleIndex(op.sinfo, this.m_emitter.registerResolvedTypeReference(idxtype).trkey, arg, op.index, trgt);
        }
        return [env.setExpressionResult(this.m_assembly, idxtype)];
    }
    checkProjectFromIndecies(env, op, arg, trgt) {
        const texp = env.getExpressionResult().etype;
        this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType()), "Base of index expression must be of Tuple type");
        this.raiseErrorIf(op.sinfo, op.indecies.some((idx) => idx < 0), "Index cannot be negative");
        const resultOptions = texp.options.map((opt) => {
            let ttypes = op.indecies.map((idx) => new resolved_type_1.ResolvedTupleAtomTypeEntry(this.getInfoForLoadFromIndex(resolved_type_1.ResolvedType.createSingle(opt), idx), false));
            return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedTupleAtomType.create(ttypes));
        });
        const restype = this.m_assembly.typeUnion(resultOptions);
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitProjectTupleIndecies(op.sinfo, this.m_emitter.registerResolvedTypeReference(restype).trkey, arg, op.indecies, trgt);
        }
        return [env.setExpressionResult(this.m_assembly, restype)];
    }
    checkAccessFromName(env, op, arg, trgt) {
        const texp = env.getExpressionResult().etype;
        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            const rtype = this.getInfoForLoadFromPropertyName(texp, op.name);
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitLoadProperty(op.sinfo, this.m_emitter.registerResolvedTypeReference(rtype).trkey, arg, op.name, trgt);
            }
            return [env.setExpressionResult(this.m_assembly, rtype)];
        }
        else {
            const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", op.name);
            this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");
            const topts = finfo.decls.map((info) => this.resolveAndEnsureTypeOnly(op.sinfo, info.decl.declaredType, info.binds));
            const rtype = this.m_assembly.typeUnion(topts);
            if (this.m_emitEnabled) {
                const fdeclinfo = finfo.root;
                const fkey = mir_emitter_1.MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, op.name);
                this.m_emitter.bodyEmitter.emitLoadField(op.sinfo, this.m_emitter.registerResolvedTypeReference(rtype).trkey, arg, fkey, trgt);
            }
            return [env.setExpressionResult(this.m_assembly, rtype)];
        }
    }
    checkProjectFromNames(env, op, arg, trgt) {
        const texp = env.getExpressionResult().etype;
        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            const resultOptions = texp.options.map((opt) => {
                let ttypes = op.names.map((name) => new resolved_type_1.ResolvedRecordAtomTypeEntry(name, this.getInfoForLoadFromPropertyName(resolved_type_1.ResolvedType.createSingle(opt), name), false));
                return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedRecordAtomType.create(ttypes));
            });
            const restype = this.m_assembly.typeUnion(resultOptions);
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitProjectProperties(op.sinfo, this.m_emitter.registerResolvedTypeReference(restype).trkey, arg, op.names, trgt);
            }
            return [env.setExpressionResult(this.m_assembly, restype)];
        }
        else {
            const fieldkeys = op.names.map((f) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", f);
                this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");
                const fdeclinfo = finfo.root;
                return mir_emitter_1.MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, f);
            });
            const resultOptions = texp.options.map((atom) => {
                const oentries = op.names.map((f) => {
                    const finfo = this.m_assembly.tryGetOOMemberDeclUnique(resolved_type_1.ResolvedType.createSingle(atom), "field", f);
                    const ftype = this.resolveAndEnsureTypeOnly(op.sinfo, finfo.decl.declaredType, finfo.binds);
                    return new resolved_type_1.ResolvedRecordAtomTypeEntry(f, ftype, false);
                });
                return resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedRecordAtomType.create(oentries));
            });
            const restype = this.m_assembly.typeUnion(resultOptions);
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitProjectFields(op.sinfo, this.m_emitter.registerResolvedTypeReference(restype).trkey, arg, fieldkeys, trgt);
            }
            return [env.setExpressionResult(this.m_assembly, restype)];
        }
    }
    checkProjectFromType(env, op, arg, trgt) {
        const texp = env.getExpressionResult().etype;
        let resultOptions = [];
        const opType = this.resolveAndEnsureTypeOnly(op.sinfo, op.ptype, env.terms);
        this.raiseErrorIf(op.sinfo, opType.options.length !== 1, "Invalid type");
        const ptype = opType.options[0];
        if (ptype instanceof resolved_type_1.ResolvedTupleAtomType) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType()));
            resultOptions = texp.options.map((opt) => this.projectTupleAtom(op.sinfo, opt, ptype));
            if (this.m_emitEnabled) {
                const ttype = this.m_emitter.registerResolvedTypeReference(opType);
                const resultType = this.m_emitter.registerResolvedTypeReference(this.m_assembly.typeUnion(resultOptions));
                this.m_emitter.bodyEmitter.emitProjectFromTypeTuple(op.sinfo, resultType.trkey, arg, ttype.trkey, trgt);
            }
        }
        else if (ptype instanceof resolved_type_1.ResolvedRecordAtomType) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType()));
            resultOptions = texp.options.map((opt) => this.projectRecordAtom(op.sinfo, opt, ptype));
            if (this.m_emitEnabled) {
                const ttype = this.m_emitter.registerResolvedTypeReference(opType);
                const resultType = this.m_emitter.registerResolvedTypeReference(this.m_assembly.typeUnion(resultOptions));
                this.m_emitter.bodyEmitter.emitProjectFromTypeRecord(op.sinfo, resultType.trkey, arg, ttype.trkey, trgt);
            }
        }
        else {
            this.raiseErrorIf(op.sinfo, !(ptype instanceof resolved_type_1.ResolvedConceptAtomType), "Can only project on Tuple, Record, Object, or Concept types");
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, opType), "Must be subtype for project operation to be valid");
            resultOptions = this.projectOOTypeAtom(op.sinfo, texp, ptype);
            if (this.m_emitEnabled) {
                this.m_emitter.registerResolvedTypeReference(opType);
                ptype.conceptTypes.map((ctype) => this.m_emitter.registerTypeInstantiation(ctype.concept, ctype.binds));
                const ckeys = ptype.conceptTypes.map((ctype) => mir_emitter_1.MIRKeyGenerator.generateTypeKey(ctype.concept, ctype.binds));
                const resultType = this.m_emitter.registerResolvedTypeReference(this.m_assembly.typeUnion(resultOptions));
                this.m_emitter.bodyEmitter.emitProjectFromTypeConcept(op.sinfo, resultType.trkey, arg, ckeys, trgt);
            }
        }
        return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(resultOptions))];
    }
    checkModifyWithIndecies(env, op, arg, trgt) {
        const texp = env.getExpressionResult().etype;
        this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType()));
        const updates = op.updates.map((update) => {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            return [update[0], this.checkExpression(env, update[1], etreg).getExpressionResult().etype, etreg];
        });
        const resultOptions = texp.options.map((opt) => this.updateTupleIndeciesAtom(op.sinfo, opt, updates.map((update) => [update[0], update[1]])));
        const rtuple = this.m_assembly.typeUnion(resultOptions);
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitModifyWithIndecies(op.sinfo, this.m_emitter.registerResolvedTypeReference(rtuple).trkey, arg, updates.map((update) => [update[0], update[2]]), trgt);
        }
        return [env.setExpressionResult(this.m_assembly, rtuple)];
    }
    checkModifyWithNames(env, op, arg, trgt) {
        const texp = env.getExpressionResult().etype;
        const updates = op.updates.map((update) => {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            return [update[0], this.checkExpression(env, update[1], etreg).getExpressionResult().etype, etreg];
        });
        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            const resultOptions = texp.options.map((opt) => this.updateNamedPropertiesAtom(op.sinfo, opt, updates.map((update) => [update[0], update[1]])));
            const rrecord = this.m_assembly.typeUnion(resultOptions);
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitModifyWithProperties(op.sinfo, this.m_emitter.registerResolvedTypeReference(rrecord).trkey, arg, updates.map((update) => [update[0], update[2]]), trgt);
            }
            return [env.setExpressionResult(this.m_assembly, rrecord)];
        }
        else {
            const fieldupdates = updates.map((update) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", update[0]);
                this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");
                const fdeclinfo = finfo.root;
                const decltype = this.m_assembly.normalizeTypeGeneral(fdeclinfo.decl.declaredType, fdeclinfo.binds);
                this.raiseErrorIf(op.sinfo, decltype.isEmptyType() || !this.m_assembly.subtypeOf(update[1], decltype));
                return [mir_emitter_1.MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, update[0]), update[2]];
            });
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitModifyWithFields(op.sinfo, this.m_emitter.registerResolvedTypeReference(texp).trkey, arg, fieldupdates, trgt);
            }
            return [env.setExpressionResult(this.m_assembly, texp)];
        }
    }
    checkStructuredExtend(env, op, arg, trgt) {
        const texp = env.getExpressionResult().etype;
        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        let mergeValue = this.checkExpression(env, op.extension, etreg).getExpressionResult().etype;
        let resultOptions = [];
        if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialTupleConceptType())) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(mergeValue, this.m_assembly.getSpecialTupleConceptType()), "Must be two Tuples to merge");
            resultOptions = resultOptions.concat(...texp.options.map((topt) => {
                return mergeValue.options.map((tmerge) => this.appendIntoTupleAtom(op.sinfo, topt, tmerge));
            }));
            const resulttype = this.m_assembly.typeUnion(resultOptions);
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitStructuredExtendTuple(op.sinfo, this.m_emitter.registerResolvedTypeReference(resulttype).trkey, arg, etreg, trgt);
            }
            return [env.setExpressionResult(this.m_assembly, resulttype)];
        }
        else if (this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialRecordConceptType())) {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(mergeValue, this.m_assembly.getSpecialRecordConceptType()), "Must be two Records to merge");
            resultOptions = resultOptions.concat(...texp.options.map((topt) => {
                return mergeValue.options.map((tmerge) => this.mergeIntoRecordAtom(op.sinfo, topt, tmerge));
            }));
            const resulttype = this.m_assembly.typeUnion(resultOptions);
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitStructuredExtendRecord(op.sinfo, this.m_emitter.registerResolvedTypeReference(resulttype).trkey, arg, etreg, trgt);
            }
            return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(resultOptions))];
        }
        else {
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, this.m_assembly.getSpecialObjectConceptType()), "Can only merge onto Tuples/Records/Objects");
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(mergeValue, this.m_assembly.getSpecialRecordConceptType()), "Must be Record to merge into Object");
            let allnames = new Map();
            mergeValue.options.forEach((opt) => {
                const record = opt;
                record.entries.forEach((entry) => {
                    allnames.set(entry.name, allnames.has(entry.name) ? entry.type : this.m_assembly.typeUnion([entry.type, allnames.get(entry.name)]));
                });
            });
            const namel = [...allnames].map((np) => np[0]).sort();
            const fieldResolves = namel.map((pname) => {
                const finfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "field", pname);
                this.raiseErrorIf(op.sinfo, finfo.root === undefined, "Field name is not defined (or is multiply) defined");
                const fdeclinfo = finfo.root;
                const decltype = this.m_assembly.normalizeTypeGeneral(fdeclinfo.decl.declaredType, fdeclinfo.binds);
                this.raiseErrorIf(op.sinfo, decltype.isEmptyType() || !this.m_assembly.subtypeOf(allnames.get(pname), decltype));
                return [pname, mir_emitter_1.MIRKeyGenerator.generateFieldKey(fdeclinfo.contiainingType, fdeclinfo.binds, pname)];
            });
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitStructuredExtendObject(op.sinfo, this.m_emitter.registerResolvedTypeReference(texp).trkey, arg, etreg, fieldResolves, trgt);
            }
            return [env.setExpressionResult(this.m_assembly, texp)];
        }
    }
    checkInvoke(env, op, arg, trgt, optArgVar, refok) {
        const texp = env.getExpressionResult().etype;
        const specialcall = (op.name === "isNone" || op.name === "isSome" || op.name === "is" || op.name === "as" || op.name === "tryAs" || op.name === "defaultAs");
        if (!specialcall && (op.specificResolve !== undefined || (texp.isUniqueCallTargetType() && this.m_assembly.tryGetOOMemberDeclUnique(texp, "method", op.name)))) {
            const resolveType = op.specificResolve !== undefined ? this.resolveAndEnsureTypeOnly(op.sinfo, op.specificResolve, env.terms) : texp;
            this.raiseErrorIf(op.sinfo, !this.m_assembly.subtypeOf(texp, resolveType), "This is not a subtype of specified resolve type");
            const mdecltry = this.m_assembly.tryGetOOMemberDeclUnique(resolveType, "method", op.name);
            this.raiseErrorIf(op.sinfo, mdecltry === undefined, `Method not defined for type '${resolveType.idStr}'`);
            const mdecl = mdecltry;
            const binds = this.m_assembly.resolveBindsForCall(mdecl.decl.invoke.terms, op.terms.targs, mdecl.binds, env.terms);
            this.raiseErrorIf(op.sinfo, binds === undefined, "Call bindings could not be resolved");
            const fsig = this.m_assembly.normalizeTypeFunction(mdecl.decl.invoke.generateSig(), binds);
            this.raiseErrorIf(op.sinfo, fsig === undefined, "Invalid function signature");
            const eargs = this.checkArgumentsEvaluationWSig(env, fsig, op.args, [resolveType, arg], refok);
            const margs = this.checkArgumentsSignature(op.sinfo, env, fsig, eargs);
            this.checkRecursion(op.sinfo, fsig, margs.pcodes, op.pragmas.recursive);
            if (this.m_emitEnabled) {
                this.m_emitter.registerResolvedTypeReference(resolveType);
                this.m_emitter.registerTypeInstantiation(mdecl.contiainingType, mdecl.binds);
                const mkey = this.m_emitter.registerMethodCall(mdecl.contiainingType, mdecl.decl, mdecl.binds, mdecl.decl.name, binds, margs.pcodes, margs.cinfo);
                const [frtype, refinfo] = this.generateRefInfoForCallEmit(fsig, margs.refs);
                this.m_emitter.bodyEmitter.emitInvokeFixedFunction(this.m_emitter.masm, op.sinfo, frtype, mkey, margs.args, refinfo, trgt);
            }
            return [env.setExpressionResult(this.m_assembly, fsig.resultType)];
        }
        else {
            const vinfo = this.m_assembly.tryGetOOMemberDeclOptions(texp, "method", op.name);
            this.raiseErrorIf(op.sinfo, vinfo.root === undefined, "Multiple possible declarations of this method");
            const vopts = vinfo.decls.map((opt) => {
                const mdecl = opt.decl;
                const binds = this.m_assembly.resolveBindsForCall(mdecl.invoke.terms, op.terms.targs, opt.binds, env.terms);
                return this.m_assembly.normalizeTypeFunction(mdecl.invoke.generateSig(), binds);
            });
            const rootdecl = vinfo.root.contiainingType.memberMethods.get(op.name);
            const rootbinds = this.m_assembly.resolveBindsForCall(rootdecl.invoke.terms, op.terms.targs, vinfo.root.binds, env.terms);
            const rootsig = this.m_assembly.normalizeTypeFunction(rootdecl.invoke.generateSig(), rootbinds);
            const lsigtry = this.m_assembly.computeUnifiedFunctionType(vopts, rootsig);
            this.raiseErrorIf(op.sinfo, lsigtry === undefined, "Ambigious signature for invoke");
            const lsig = lsigtry;
            const eargs = this.checkArgumentsEvaluationWSig(env, lsig, op.args, [texp, arg], refok);
            const margs = this.checkArgumentsSignature(op.sinfo, env, lsig, eargs);
            this.checkRecursion(op.sinfo, lsig, margs.pcodes, op.pragmas.recursive);
            if (this.m_emitEnabled) {
                let cbindsonly = this.m_assembly.resolveBindsForCall(rootdecl.invoke.terms, op.terms.targs, new Map(), env.terms);
                const specialm0type = this.m_emitter.registerResolvedTypeReference(margs.types.length === 1 ? margs.types[0] : this.m_assembly.getSpecialNoneType()).trkey;
                if (op.name === "isNone") {
                    this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialNoneType()).trkey, specialm0type, margs.args[0]);
                }
                else if (op.name === "isSome") {
                    this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, trgt, this.m_emitter.registerResolvedTypeReference(this.m_assembly.getSpecialSomeType()).trkey, specialm0type, margs.args[0]);
                }
                else if (op.name === "is" || op.name === "as" || op.name === "tryAs" || op.name === "defaultAs") {
                    const ttype = rootbinds.get("T");
                    const mt = this.m_emitter.registerResolvedTypeReference(ttype);
                    if (op.name === "is") {
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, trgt, mt.trkey, specialm0type, margs.args[0]);
                    }
                    else if (op.name === "as") {
                        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Las_done");
                        const failblck = this.m_emitter.bodyEmitter.createNewBlock("Las_fail");
                        const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, creg, mt.trkey, specialm0type, margs.args[0]);
                        this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, creg, doneblck, failblck);
                        this.m_emitter.bodyEmitter.setActiveBlock(failblck);
                        this.m_emitter.bodyEmitter.emitAbort(op.sinfo, true, "as<T> fail");
                        this.m_emitter.bodyEmitter.emitDirectJump(op.sinfo, "exit");
                        this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                        this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs.args[0], trgt);
                    }
                    else if (op.name === "tryAs") {
                        this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs.args[0], trgt);
                        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Ltryas_done");
                        const noneblck = this.m_emitter.bodyEmitter.createNewBlock("Ltryas_none");
                        const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, creg, mt.trkey, specialm0type, margs.args[0]);
                        this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, creg, doneblck, noneblck);
                        this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                        this.m_emitter.bodyEmitter.emitLoadConstNone(op.sinfo, trgt);
                        this.m_emitter.bodyEmitter.emitDirectJump(op.sinfo, doneblck);
                        this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                    }
                    else {
                        this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs.args[0], trgt);
                        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Ldefaultas_done");
                        const noneblck = this.m_emitter.bodyEmitter.createNewBlock("Ldefaultas_none");
                        const creg = this.m_emitter.bodyEmitter.generateTmpRegister();
                        this.m_emitter.bodyEmitter.emitTypeOf(op.sinfo, creg, mt.trkey, specialm0type, margs.args[0]);
                        this.m_emitter.bodyEmitter.emitBoolJump(op.sinfo, creg, doneblck, noneblck);
                        this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                        this.m_emitter.bodyEmitter.emitLoadConstNone(op.sinfo, trgt);
                        this.m_emitter.bodyEmitter.emitRegAssign(op.sinfo, margs.args[1], trgt);
                        this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                    }
                }
                else {
                    const vkey = this.m_emitter.registerVirtualMethodCall(vinfo.root.contiainingType, vinfo.root.binds, op.name, cbindsonly, margs.pcodes, margs.cinfo);
                    const [frtype, refinfo] = this.generateRefInfoForCallEmit(lsig, margs.refs);
                    this.m_emitter.bodyEmitter.emitInvokeVirtualTarget(this.m_emitter.masm, op.sinfo, frtype, vkey, margs.args, refinfo, trgt);
                }
            }
            if (optArgVar === undefined || !this.AnySplitMethods.some((m) => m === op.name)) {
                const returnOpts = vopts.map((ropt) => ropt.resultType);
                return [env.setExpressionResult(this.m_assembly, this.m_assembly.typeUnion(returnOpts))];
            }
            else {
                //
                //TODO: we may want to do some as/tryAs action here as well
                //
                let opname = op.name;
                if (op.name === "is") {
                    const ttype = rootbinds.get("T");
                    if (ttype.isNoneType()) {
                        opname = "isNone";
                    }
                    if (ttype.isSomeType()) {
                        opname = "isSome";
                    }
                }
                if (opname === "isNone" || opname === "isSome") {
                    const [enone, esome] = type_environment_1.TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, [env]);
                    this.raiseErrorIf(op.sinfo, enone.length === 0, "Value is never equal to none");
                    this.raiseErrorIf(op.sinfo, esome.length === 0, "Value is always equal to none");
                    if (optArgVar === undefined) {
                        const eqnone = enone.map((opt) => opt.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), opname === "isNone" ? type_environment_1.FlowTypeTruthValue.True : type_environment_1.FlowTypeTruthValue.False));
                        const neqnone = esome.map((opt) => opt.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), opname === "isNone" ? type_environment_1.FlowTypeTruthValue.False : type_environment_1.FlowTypeTruthValue.True));
                        return [...eqnone, ...neqnone];
                    }
                    else {
                        const eqnone = enone.map((opt) => opt
                            .assumeVar(optArgVar, opt.expressionResult.etype)
                            .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), opname === "isNone" ? type_environment_1.FlowTypeTruthValue.True : type_environment_1.FlowTypeTruthValue.False));
                        const neqnone = esome.map((opt) => opt
                            .assumeVar(optArgVar, opt.expressionResult.etype)
                            .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), opname === "isNone" ? type_environment_1.FlowTypeTruthValue.False : type_environment_1.FlowTypeTruthValue.True));
                        return [...eqnone, ...neqnone];
                    }
                }
                else {
                    const ttype = rootbinds.get("T");
                    const tvals = [env]
                        .filter((opt) => !this.m_assembly.restrictT(opt.getExpressionResult().etype, ttype).isEmptyType())
                        .map((opt) => opt
                        .assumeVar(optArgVar, this.m_assembly.restrictT(opt.getExpressionResult().etype, ttype))
                        .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), type_environment_1.FlowTypeTruthValue.True));
                    const ntvals = [env]
                        .filter((opt) => !this.m_assembly.restrictNotT(opt.getExpressionResult().etype, ttype).isEmptyType())
                        .map((opt) => opt
                        .assumeVar(optArgVar, this.m_assembly.restrictNotT(opt.getExpressionResult().etype, ttype))
                        .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), type_environment_1.FlowTypeTruthValue.False));
                    this.raiseErrorIf(op.sinfo, tvals.length === 0, "Value is never of type");
                    this.raiseErrorIf(op.sinfo, ntvals.length === 0, "Value is always of type");
                    return [...tvals, ...ntvals];
                }
            }
        }
    }
    checkElvisAction(sinfo, env, elvisEnabled, etrgt, noneblck) {
        const [enone, esome] = type_environment_1.TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, env);
        this.raiseErrorIf(sinfo, enone.length === 0 && elvisEnabled, "None value is not possible -- will never return none and elvis access is redundant");
        this.raiseErrorIf(sinfo, esome.length === 0 && elvisEnabled, "Some value is not possible -- will always return none and following expression is redundant");
        if (this.m_emitEnabled && elvisEnabled) {
            const nextblk = this.m_emitter.bodyEmitter.createNewBlock("Lelvis");
            this.m_emitter.bodyEmitter.emitNoneJump(sinfo, etrgt, noneblck, nextblk);
            this.m_emitter.bodyEmitter.setActiveBlock(nextblk);
        }
        return elvisEnabled ? [esome, enone] : [[...esome, ...enone], []];
    }
    checkPostfixExpression(env, exp, trgt, refok) {
        const hasNoneCheck = exp.ops.some((op) => op.isElvis);
        const noneblck = hasNoneCheck && this.m_emitEnabled ? this.m_emitter.bodyEmitter.createNewBlock("Lelvis_none") : "[DISABLED]";
        const doneblck = hasNoneCheck && this.m_emitEnabled ? this.m_emitter.bodyEmitter.createNewBlock("Lelvis_done") : "[DISABLED]";
        let etgrt = this.m_emitter.bodyEmitter.generateTmpRegister();
        let eenv = this.checkExpressionMultiFlow(env, exp.rootExp, etgrt);
        if (exp.rootExp instanceof body_1.AccessVariableExpression && exp.ops.length === 1 && exp.ops[0] instanceof body_1.PostfixInvoke) {
            const [fflow, scflow] = this.checkElvisAction(exp.sinfo, eenv, exp.ops[0].isElvis, etgrt, noneblck);
            const res = this.checkInvoke(type_environment_1.TypeEnvironment.join(this.m_assembly, ...fflow), exp.ops[0], etgrt, trgt, exp.rootExp.name, refok);
            if (hasNoneCheck && this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                this.m_emitter.bodyEmitter.emitLoadConstNone(exp.sinfo, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }
            return [...res, ...scflow];
        }
        else {
            let scflows = [];
            let cenv = eenv;
            for (let i = 0; i < exp.ops.length; ++i) {
                const [fflow, scflow] = this.checkElvisAction(exp.sinfo, cenv, exp.ops[i].isElvis, etgrt, noneblck);
                scflows = [...scflows, ...scflow];
                const nflow = type_environment_1.TypeEnvironment.join(this.m_assembly, ...fflow);
                const ntgrt = this.m_emitter.bodyEmitter.generateTmpRegister();
                switch (exp.ops[i].op) {
                    case body_1.PostfixOpTag.PostfixAccessFromIndex:
                        cenv = this.checkAccessFromIndex(nflow, exp.ops[i], etgrt, ntgrt);
                        break;
                    case body_1.PostfixOpTag.PostfixProjectFromIndecies:
                        cenv = this.checkProjectFromIndecies(nflow, exp.ops[i], etgrt, ntgrt);
                        break;
                    case body_1.PostfixOpTag.PostfixAccessFromName:
                        cenv = this.checkAccessFromName(nflow, exp.ops[i], etgrt, ntgrt);
                        break;
                    case body_1.PostfixOpTag.PostfixProjectFromNames:
                        cenv = this.checkProjectFromNames(nflow, exp.ops[i], etgrt, ntgrt);
                        break;
                    case body_1.PostfixOpTag.PostfixProjectFromType:
                        cenv = this.checkProjectFromType(nflow, exp.ops[i], etgrt, ntgrt);
                        break;
                    case body_1.PostfixOpTag.PostfixModifyWithIndecies:
                        cenv = this.checkModifyWithIndecies(nflow, exp.ops[i], etgrt, ntgrt);
                        break;
                    case body_1.PostfixOpTag.PostfixModifyWithNames:
                        cenv = this.checkModifyWithNames(nflow, exp.ops[i], etgrt, ntgrt);
                        break;
                    case body_1.PostfixOpTag.PostfixStructuredExtend:
                        cenv = this.checkStructuredExtend(nflow, exp.ops[i], etgrt, ntgrt);
                        break;
                    default:
                        this.raiseErrorIf(exp.sinfo, exp.ops[i].op !== body_1.PostfixOpTag.PostfixInvoke, "Unknown postfix op");
                        cenv = this.checkInvoke(nflow, exp.ops[i], etgrt, ntgrt, undefined, refok);
                        break;
                }
                etgrt = ntgrt;
            }
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, etgrt, trgt);
                if (hasNoneCheck) {
                    this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                    this.m_emitter.bodyEmitter.setActiveBlock(noneblck);
                    this.m_emitter.bodyEmitter.emitLoadConstNone(exp.sinfo, trgt);
                    this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                    this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
                }
            }
            return [...cenv, ...scflows];
        }
    }
    checkPrefixOp(env, exp, trgt) {
        if (exp.op === "+" || exp.op === "-") {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const eres = this.checkExpression(env, exp.exp, etreg);
            this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(eres.getExpressionResult().etype, this.m_assembly.getSpecialIntType()), "Operators + and - only applicable to numeric values");
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitPrefixOp(exp.sinfo, exp.op, etreg, trgt);
            }
            return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialIntType())];
        }
        else {
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const estates = this.checkExpressionMultiFlow(env, exp.exp, etreg);
            const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
            this.raiseErrorIf(exp.sinfo, estates.some((state) => !this.m_assembly.subtypeOf(state.getExpressionResult().etype, okType)), "Operator ! only applicable to None/Bool values");
            const [tstates, fstates] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, estates);
            const ntstates = tstates.map((state) => state.setExpressionResult(this.m_assembly, state.getExpressionResult().etype, type_environment_1.FlowTypeTruthValue.False));
            const nfstates = fstates.map((state) => state.setExpressionResult(this.m_assembly, state.getExpressionResult().etype, type_environment_1.FlowTypeTruthValue.True));
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitPrefixOp(exp.sinfo, "!", etreg, trgt);
            }
            return [...ntstates, ...nfstates];
        }
    }
    checkBinOp(env, exp, trgt) {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg);
        const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const rhs = this.checkExpression(env, exp.rhs, rhsreg);
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(lhs.getExpressionResult().etype, this.m_assembly.getSpecialIntType()) || !this.m_assembly.subtypeOf(rhs.getExpressionResult().etype, this.m_assembly.getSpecialIntType()));
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitBinOp(exp.sinfo, lhsreg, exp.op, rhsreg, trgt);
        }
        return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialIntType())];
    }
    checkBinEq(env, exp, trgt) {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg);
        const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const rhs = this.checkExpression(env, exp.rhs, rhsreg);
        const pairwiseok = this.checkValueEq(lhs.getExpressionResult().etype, rhs.getExpressionResult().etype);
        this.raiseErrorIf(exp.sinfo, !pairwiseok, "Types are incompatible for equality compare");
        if (this.m_emitEnabled) {
            if (exp.lhs instanceof body_1.LiteralNoneExpression && exp.rhs instanceof body_1.LiteralNoneExpression) {
                this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, exp.op === "==" ? true : false, trgt);
            }
            else if (exp.lhs instanceof body_1.LiteralNoneExpression) {
                const chktype = this.m_emitter.registerResolvedTypeReference(exp.op === "==" ? this.m_assembly.getSpecialNoneType() : this.m_assembly.getSpecialSomeType());
                this.m_emitter.bodyEmitter.emitTypeOf(exp.sinfo, trgt, chktype.trkey, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().etype).trkey, rhsreg);
            }
            else if (exp.rhs instanceof body_1.LiteralNoneExpression) {
                const chktype = this.m_emitter.registerResolvedTypeReference(exp.op === "==" ? this.m_assembly.getSpecialNoneType() : this.m_assembly.getSpecialSomeType());
                this.m_emitter.bodyEmitter.emitTypeOf(exp.sinfo, trgt, chktype.trkey, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().etype).trkey, lhsreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitBinEq(exp.sinfo, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().etype).trkey, lhsreg, exp.op, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().etype).trkey, rhsreg, trgt);
            }
        }
        if ((exp.lhs instanceof body_1.LiteralNoneExpression && exp.rhs instanceof body_1.AccessVariableExpression) ||
            (exp.lhs instanceof body_1.AccessVariableExpression && exp.rhs instanceof body_1.LiteralNoneExpression)) {
            const [enone, esome] = type_environment_1.TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, exp.rhs instanceof body_1.AccessVariableExpression ? [rhs] : [lhs]);
            this.raiseErrorIf(exp.sinfo, enone.length === 0, "Value is never equal to none");
            this.raiseErrorIf(exp.sinfo, esome.length === 0, "Value is always equal to none");
            const vname = exp.rhs instanceof body_1.AccessVariableExpression ? exp.rhs.name : exp.lhs.name;
            const eqnone = enone.map((opt) => opt
                .assumeVar(vname, opt.expressionResult.etype)
                .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), exp.op === "==" ? type_environment_1.FlowTypeTruthValue.True : type_environment_1.FlowTypeTruthValue.False));
            const neqnone = esome.map((opt) => opt
                .assumeVar(vname, opt.expressionResult.etype)
                .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), exp.op === "==" ? type_environment_1.FlowTypeTruthValue.False : type_environment_1.FlowTypeTruthValue.True));
            return [...eqnone, ...neqnone];
        }
        else {
            //
            //TODO: maybe later (since this is tricky) infer that variable is strengthened by type on other side in case of -- exp.rhs instanceof AccessVariableExpression || exp.lhs instanceof AccessVariableExpression
            //
            return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType())];
        }
    }
    checkBinCmp(env, exp, trgt) {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpression(env, exp.lhs, lhsreg);
        const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const rhs = this.checkExpression(env, exp.rhs, rhsreg);
        this.raiseErrorIf(exp.sinfo, !this.checkValueLess(lhs.getExpressionResult().etype, rhs.getExpressionResult().etype), "Types are incompatible for order compare");
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitBinCmp(exp.sinfo, this.m_emitter.registerResolvedTypeReference(lhs.getExpressionResult().etype).trkey, lhsreg, exp.op, this.m_emitter.registerResolvedTypeReference(rhs.getExpressionResult().etype).trkey, rhsreg, trgt);
        }
        return [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType())];
    }
    checkBinLogic(env, exp, trgt) {
        const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg);
        this.raiseErrorIf(exp.sinfo, lhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");
        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Llogic_done");
        const scblck = this.m_emitter.bodyEmitter.createNewBlock("Llogic_shortcircuit");
        const restblck = this.m_emitter.bodyEmitter.createNewBlock("Llogic_rest");
        if (this.m_emitEnabled) {
            if (exp.op === "||") {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, lhsreg, scblck, restblck);
                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
                this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, true, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            }
            else if (exp.op === "&&") {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, lhsreg, restblck, scblck);
                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
                this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, false, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            }
            else {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, lhsreg, restblck, scblck);
                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
                this.m_emitter.bodyEmitter.emitLoadConstBool(exp.sinfo, true, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            }
            this.m_emitter.bodyEmitter.setActiveBlock(restblck);
        }
        const [trueflow, falseflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, lhs);
        //THIS IS WRONG -- in "true && x" the true is redundant but the rest of the expressions needs to be evaluated 
        this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false rest of expression is infeasible");
        if (exp.op === "||") {
            const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const rhs = this.checkExpressionMultiFlow(type_environment_1.TypeEnvironment.join(this.m_assembly, ...falseflow), exp.rhs, rhsreg);
            this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitTruthyConversion(exp.sinfo, rhsreg, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }
            const [rtflow, rfflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, rhs);
            //THIS IS WRONG -- in "x || false" the true is redundant but the rest of the expressions needs to be evaluated 
            //this.raiseErrorIf(exp.sinfo, rtflow.length === 0 || rfflow.length === 0, "Expression is never true/false and not needed");
            return [...trueflow, ...rtflow, ...rfflow];
        }
        else if (exp.op === "&&") {
            const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const rhs = this.checkExpressionMultiFlow(type_environment_1.TypeEnvironment.join(this.m_assembly, ...trueflow), exp.rhs, rhsreg);
            this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitTruthyConversion(exp.sinfo, rhsreg, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }
            const [rtflow, rfflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, rhs);
            //THIS IS WRONG -- in "x && true" the true is redundant but the rest of the expressions needs to be evaluated 
            //this.raiseErrorIf(exp.sinfo, rtflow.length === 0 || rfflow.length === 0, "Expression is never true/false and not needed");
            return [...falseflow, ...rtflow, ...rfflow];
        }
        else {
            const rhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const rhs = this.checkExpressionMultiFlow(type_environment_1.TypeEnvironment.join(this.m_assembly, ...trueflow), exp.rhs, rhsreg);
            this.raiseErrorIf(exp.sinfo, rhs.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitTruthyConversion(exp.sinfo, rhsreg, trgt);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
            }
            const [rtflow, rfflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, rhs);
            //THIS IS WRONG -- in "x => true" the true is redundant but the rest of the expressions needs to be evaluated 
            //this.raiseErrorIf(exp.sinfo, rtflow.length === 0 || rfflow.length === 0, "Expression is never true/false and not needed");
            return [...falseflow.map((opt) => opt.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), type_environment_1.FlowTypeTruthValue.True)), ...rtflow, ...rfflow];
        }
    }
    checkNonecheck(env, exp, trgt) {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg);
        let [enone, esome] = type_environment_1.TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, lhs);
        this.raiseErrorIf(exp.sinfo, enone.length === 0, "Value is never equal to none");
        this.raiseErrorIf(exp.sinfo, esome.length === 0, "Value is always equal to none");
        if (exp.lhs instanceof body_1.AccessVariableExpression) {
            const vname = exp.lhs.name;
            enone = enone.map((opt) => opt.assumeVar(vname, opt.expressionResult.etype));
            esome = esome.map((opt) => opt.assumeVar(vname, opt.expressionResult.etype));
        }
        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lnonecheck_done");
        const scblck = this.m_emitter.bodyEmitter.createNewBlock("Lnonecheck_shortcircuit");
        const restblck = this.m_emitter.bodyEmitter.createNewBlock("Lnonecheck_rest");
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitNoneJump(exp.sinfo, lhsreg, scblck, restblck);
            this.m_emitter.bodyEmitter.setActiveBlock(scblck);
            this.m_emitter.bodyEmitter.emitLoadConstNone(exp.sinfo, trgt);
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            this.m_emitter.bodyEmitter.setActiveBlock(restblck);
        }
        const rhs = this.checkExpressionMultiFlow(type_environment_1.TypeEnvironment.join(this.m_assembly, ...esome), exp.rhs, trgt);
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }
        return [...enone, ...rhs];
    }
    checkCoalesce(env, exp, trgt) {
        const lhsreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const lhs = this.checkExpressionMultiFlow(env, exp.lhs, lhsreg);
        let [enone, esome] = type_environment_1.TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, lhs);
        this.raiseErrorIf(exp.sinfo, enone.length === 0, "Value is never equal to none");
        this.raiseErrorIf(exp.sinfo, esome.length === 0, "Value is always equal to none");
        if (exp.lhs instanceof body_1.AccessVariableExpression) {
            const vname = exp.lhs.name;
            enone = enone.map((opt) => opt.assumeVar(vname, opt.expressionResult.etype));
            esome = esome.map((opt) => opt.assumeVar(vname, opt.expressionResult.etype));
        }
        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lcoalesce_done");
        const scblck = this.m_emitter.bodyEmitter.createNewBlock("Lcoalesce_shortcircuit");
        const restblck = this.m_emitter.bodyEmitter.createNewBlock("Lcoalesce_rest");
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitNoneJump(exp.sinfo, lhsreg, restblck, scblck);
            this.m_emitter.bodyEmitter.setActiveBlock(scblck);
            this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, lhsreg, trgt);
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            this.m_emitter.bodyEmitter.setActiveBlock(restblck);
        }
        const rhs = this.checkExpressionMultiFlow(type_environment_1.TypeEnvironment.join(this.m_assembly, ...enone), exp.rhs, trgt);
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }
        return [...esome, ...rhs];
    }
    checkSelect(env, exp, trgt) {
        const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
        const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, exp.test, testreg);
        this.raiseErrorIf(exp.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");
        const [trueflow, falseflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
        this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false expression test is redundant");
        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lselect_done");
        const trueblck = this.m_emitter.bodyEmitter.createNewBlock("Lselect_true");
        const falseblck = this.m_emitter.bodyEmitter.createNewBlock("Lselect_false");
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, testreg, trueblck, falseblck);
        }
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(trueblck);
        }
        const truestate = this.checkExpression(type_environment_1.TypeEnvironment.join(this.m_assembly, ...trueflow), exp.option1, trgt);
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
        }
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(falseblck);
        }
        const falsestate = this.checkExpression(type_environment_1.TypeEnvironment.join(this.m_assembly, ...falseflow), exp.option2, trgt);
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }
        const rtype = this.m_assembly.typeUnion([truestate.getExpressionResult().etype, falsestate.getExpressionResult().etype]);
        return [env.setExpressionResult(this.m_assembly, rtype)];
    }
    checkOrExpression(env, exp, trgt, extraok) {
        this.raiseErrorIf(exp.sinfo, !extraok.orok, "Or expression is not valid in this position");
        const scblck = this.m_emitter.bodyEmitter.createNewBlock("Lorcheck_return");
        const regularblck = this.m_emitter.bodyEmitter.createNewBlock("Lorcheck_regular");
        let evalue = this.checkExpressionMultiFlow(env, exp.exp, trgt, { refok: extraok.refok, orok: false });
        let normaltype = this.m_assembly.typeUnion(evalue.map((ev) => ev.getExpressionResult().etype));
        let normalexps = [];
        let terminaltype = this.m_assembly.getSpecialNoneType();
        let terminalexps = [];
        if (exp.cond !== undefined || exp.result !== undefined) {
            evalue = evalue.map((ev) => ev.pushLocalScope().addVar("_value_", true, ev.getExpressionResult().etype, true, ev.getExpressionResult().etype));
            if (this.m_emitEnabled) {
                const vtype = type_environment_1.TypeEnvironment.join(this.m_assembly, ...evalue).getExpressionResult().etype;
                this.m_emitter.bodyEmitter.localLifetimeStart(exp.sinfo, "_value_", this.m_emitter.registerResolvedTypeReference(vtype).trkey);
                this.m_emitter.bodyEmitter.emitVarStore(exp.sinfo, trgt, "_value_");
            }
        }
        if (exp.cond === undefined) {
            let [enone, esome] = type_environment_1.TypeEnvironment.convertToNoneSomeFlowsOnExpressionResult(this.m_assembly, evalue);
            this.raiseErrorIf(exp.sinfo, enone.length === 0, "Value is never equal to none");
            this.raiseErrorIf(exp.sinfo, esome.length === 0, "Value is always equal to none");
            if (exp.exp instanceof body_1.AccessVariableExpression) {
                const vname = exp.exp.name;
                enone = enone.map((opt) => opt.assumeVar(vname, opt.expressionResult.etype));
                esome = esome.map((opt) => opt.assumeVar(vname, opt.expressionResult.etype));
            }
            normaltype = type_environment_1.TypeEnvironment.join(this.m_assembly, ...esome).getExpressionResult().etype;
            terminaltype = type_environment_1.TypeEnvironment.join(this.m_assembly, ...enone).getExpressionResult().etype;
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitNoneJump(exp.sinfo, trgt, scblck, regularblck);
                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
            }
            normalexps = esome;
            terminalexps = enone;
        }
        else {
            const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
            const treg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const tvalue = this.checkExpressionMultiFlow(type_environment_1.TypeEnvironment.join(this.m_assembly, ...evalue), exp.cond, treg);
            this.raiseErrorIf(exp.sinfo, tvalue.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");
            const [trueflow, falseflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, tvalue);
            this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false expression test is redundant");
            normaltype = type_environment_1.TypeEnvironment.join(this.m_assembly, ...evalue).getLocalVarInfo("_value_").flowType;
            terminaltype = type_environment_1.TypeEnvironment.join(this.m_assembly, ...evalue).getLocalVarInfo("_value_").flowType;
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, treg, scblck, regularblck);
                this.m_emitter.bodyEmitter.setActiveBlock(scblck);
            }
            normalexps = falseflow.map((ev) => ev.popLocalScope());
            terminalexps = trueflow.map((ev) => ev.popLocalScope());
        }
        let rreg = trgt;
        if (exp.result !== undefined) {
            const tenv = type_environment_1.TypeEnvironment.join(this.m_assembly, ...terminalexps);
            const rvalue = this.checkExpression(tenv, exp.result, rreg);
            terminaltype = rvalue.getExpressionResult().etype;
        }
        if (exp.cond !== undefined || exp.result !== undefined) {
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.localLifetimeEnd(exp.sinfo, "_value_");
            }
        }
        if (exp.action === "return") {
            this.raiseErrorIf(exp.sinfo, env.isInYieldBlock(), "Cannot use return statment inside an expression block");
            if (this.m_emitEnabled) {
                const rtuple = this.generateRefInfoForReturnEmit(terminaltype, env);
                this.m_emitter.bodyEmitter.emitReturnAssign(exp.sinfo, rtuple, env.refparams, rreg);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, "exit");
                this.m_emitter.bodyEmitter.setActiveBlock(regularblck);
            }
            return [...(normalexps.map((ev) => ev.setExpressionResult(this.m_assembly, normaltype))), env.setReturn(this.m_assembly, terminaltype)];
        }
        else {
            this.raiseErrorIf(exp.sinfo, !env.isInYieldBlock(), "Cannot use yield statment unless inside and expression block");
            if (this.m_emitEnabled) {
                const yinfo = env.getYieldTargetInfo();
                this.m_emitter.bodyEmitter.emitRegAssign(exp.sinfo, rreg, yinfo[0]);
                this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, yinfo[1]);
                this.m_emitter.bodyEmitter.setActiveBlock(regularblck);
            }
            return [...(normalexps.map((ev) => ev.setExpressionResult(this.m_assembly, normaltype))), env.setYield(this.m_assembly, terminaltype)];
        }
    }
    checkBlockExpression(env, exp, trgt) {
        const yblck = this.m_emitter.bodyEmitter.createNewBlock("Lyield");
        let cenv = env.freezeVars().pushLocalScope().pushYieldTarget(trgt, yblck);
        for (let i = 0; i < exp.ops.length; ++i) {
            if (!cenv.hasNormalFlow()) {
                break;
            }
            cenv = this.checkStatement(cenv, exp.ops[i]);
        }
        if (this.m_emitEnabled && cenv.hasNormalFlow()) {
            this.m_emitter.bodyEmitter.setActiveBlock(yblck);
            const deadvars = cenv.getCurrentFrameNames();
            for (let i = 0; i < deadvars.length; ++i) {
                this.m_emitter.bodyEmitter.localLifetimeEnd(exp.sinfo, deadvars[i]);
            }
        }
        this.raiseErrorIf(exp.sinfo, cenv.hasNormalFlow(), "Not all flow paths yield a value!");
        this.raiseErrorIf(exp.sinfo, cenv.yieldResult === undefined, "No valid flow through expresssion block");
        const ytype = cenv.yieldResult;
        return [env.setExpressionResult(this.m_assembly, ytype)];
    }
    checkIfExpression(env, exp, trgt) {
        const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lifexp_done");
        let cenv = env;
        let results = [];
        for (let i = 0; i < exp.flow.conds.length; ++i) {
            const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const test = this.checkExpressionMultiFlow(cenv, exp.flow.conds[i].cond, testreg);
            this.raiseErrorIf(exp.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");
            const [trueflow, falseflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
            this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false expression test is redundant");
            const trueblck = this.m_emitter.bodyEmitter.createNewBlock(`Lifexp_${i}true`);
            const falseblck = this.m_emitter.bodyEmitter.createNewBlock(`Lifexp_${i}false`);
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitBoolJump(exp.sinfo, testreg, trueblck, falseblck);
            }
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock(trueblck);
            }
            const truestate = this.checkExpression(type_environment_1.TypeEnvironment.join(this.m_assembly, ...trueflow), exp.flow.conds[i].action, trgt);
            if (this.m_emitEnabled) {
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                }
                this.m_emitter.bodyEmitter.setActiveBlock(falseblck);
            }
            results.push(truestate);
            cenv = type_environment_1.TypeEnvironment.join(this.m_assembly, ...falseflow);
        }
        const aenv = this.checkExpression(cenv, exp.flow.elseAction, trgt);
        results.push(aenv);
        if (this.m_emitEnabled && aenv.hasNormalFlow()) {
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
        }
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }
        return results;
    }
    checkMatchExpression(env, exp, trgt) {
        const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = this.checkExpression(env, exp.sval, vreg);
        const svname = exp.sval instanceof body_1.AccessVariableExpression ? exp.sval.name : undefined;
        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lswitchexp_done");
        let cenv = venv;
        let vtype = venv.getExpressionResult().etype;
        let results = [];
        for (let i = 0; i < exp.flow.length; ++i) {
            const nextlabel = this.m_emitter.bodyEmitter.createNewBlock(`Lswitchexp_${i}next`);
            const actionlabel = this.m_emitter.bodyEmitter.createNewBlock(`Lswitchexp_${i}action`);
            const test = this.checkMatchGuard(exp.sinfo, i, vreg, vtype, cenv, exp.flow[i].check, nextlabel, actionlabel, svname, i === exp.flow.length - 1);
            vtype = test.nexttype;
            const [trueflow, falseflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test.envinfo);
            this.raiseErrorIf(exp.sinfo, trueflow.length === 0 || (falseflow.length === 0 && i !== exp.flow.length - 1), "Expression is always true/false expression test is redundant");
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock(actionlabel);
            }
            const truestate = this.checkExpression(type_environment_1.TypeEnvironment.join(this.m_assembly, ...trueflow), exp.flow[i].action, trgt);
            if (this.m_emitEnabled) {
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, doneblck);
                }
                this.m_emitter.bodyEmitter.setActiveBlock(nextlabel);
            }
            results.push(truestate);
            cenv = falseflow.length !== 0 ? type_environment_1.TypeEnvironment.join(this.m_assembly, ...falseflow) : cenv;
        }
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitAbort(exp.sinfo, true, "exhaustive");
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, "exit");
        }
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }
        return results;
    }
    checkExpression(env, exp, trgt, extraok) {
        const res = this.checkExpressionMultiFlow(env, exp, trgt, extraok);
        this.raiseErrorIf(exp.sinfo, res.length === 0, "No feasible flow for expression");
        return type_environment_1.TypeEnvironment.join(this.m_assembly, ...res);
    }
    checkExpressionMultiFlow(env, exp, trgt, extraok) {
        switch (exp.tag) {
            case body_1.ExpressionTag.LiteralNoneExpression:
                return this.checkLiteralNoneExpression(env, exp, trgt);
            case body_1.ExpressionTag.LiteralBoolExpression:
                return this.checkLiteralBoolExpression(env, exp, trgt);
            case body_1.ExpressionTag.LiteralIntegerExpression:
                return this.checkLiteralIntegerExpression(env, exp, trgt);
            case body_1.ExpressionTag.LiteralStringExpression:
                return this.checkLiteralStringExpression(env, exp, trgt);
            case body_1.ExpressionTag.LiteralTypedStringExpression:
                return this.checkCreateTypedString(env, exp, trgt);
            case body_1.ExpressionTag.LiteralTypedStringConstructorExpression:
                return this.checkTypedStringConstructor(env, exp, trgt);
            case body_1.ExpressionTag.AccessNamespaceConstantExpression:
                return this.checkAccessNamespaceConstant(env, exp, trgt);
            case body_1.ExpressionTag.AccessStaticFieldExpression:
                return this.checkAccessStaticField(env, exp, trgt);
            case body_1.ExpressionTag.AccessVariableExpression:
                return this.checkAccessVariable(env, exp, trgt);
            case body_1.ExpressionTag.ConstructorPrimaryExpression:
                return this.checkConstructorPrimary(env, exp, trgt);
            case body_1.ExpressionTag.ConstructorPrimaryWithFactoryExpression:
                return this.checkConstructorPrimaryWithFactory(env, exp, trgt, (extraok && extraok.refok) || false);
            case body_1.ExpressionTag.ConstructorTupleExpression:
                return this.checkTupleConstructor(env, exp, trgt);
            case body_1.ExpressionTag.ConstructorRecordExpression:
                return this.checkRecordConstructor(env, exp, trgt);
            case body_1.ExpressionTag.CallNamespaceFunctionExpression:
                return this.checkCallNamespaceFunctionExpression(env, exp, trgt, (extraok && extraok.refok) || false);
            case body_1.ExpressionTag.CallStaticFunctionExpression:
                return this.checkCallStaticFunctionExpression(env, exp, trgt, (extraok && extraok.refok) || false);
            case body_1.ExpressionTag.PCodeInvokeExpression:
                return this.checkPCodeInvokeExpression(env, exp, trgt);
            case body_1.ExpressionTag.PostfixOpExpression:
                return this.checkPostfixExpression(env, exp, trgt, (extraok && extraok.refok) || false);
            case body_1.ExpressionTag.PrefixOpExpression:
                return this.checkPrefixOp(env, exp, trgt);
            case body_1.ExpressionTag.BinOpExpression:
                return this.checkBinOp(env, exp, trgt);
            case body_1.ExpressionTag.BinEqExpression:
                return this.checkBinEq(env, exp, trgt);
            case body_1.ExpressionTag.BinCmpExpression:
                return this.checkBinCmp(env, exp, trgt);
            case body_1.ExpressionTag.BinLogicExpression:
                return this.checkBinLogic(env, exp, trgt);
            case body_1.ExpressionTag.NonecheckExpression:
                return this.checkNonecheck(env, exp, trgt);
            case body_1.ExpressionTag.CoalesceExpression:
                return this.checkCoalesce(env, exp, trgt);
            case body_1.ExpressionTag.SelectExpression:
                return this.checkSelect(env, exp, trgt);
            case body_1.ExpressionTag.ExpOrExpression:
                return this.checkOrExpression(env, exp, trgt, extraok || { refok: false, orok: false });
            case body_1.ExpressionTag.BlockStatementExpression:
                return this.checkBlockExpression(env, exp, trgt);
            case body_1.ExpressionTag.IfExpression:
                return this.checkIfExpression(env, exp, trgt);
            default:
                this.raiseErrorIf(exp.sinfo, exp.tag !== body_1.ExpressionTag.MatchExpression, "Unknown expression");
                return this.checkMatchExpression(env, exp, trgt);
        }
    }
    checkVariableDeclarationStatement(env, stmt) {
        this.raiseErrorIf(stmt.sinfo, env.isVarNameDefined(stmt.name), "Cannot shadow previous definition");
        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = stmt.exp !== undefined ? this.checkExpression(env, stmt.exp, etreg, { refok: true, orok: true }) : undefined;
        this.raiseErrorIf(stmt.sinfo, venv === undefined && stmt.isConst, "Must define const var at declaration site");
        this.raiseErrorIf(stmt.sinfo, venv === undefined && stmt.vtype instanceof type_signature_1.AutoTypeSignature, "Must define auto typed var at declaration site");
        const vtype = (stmt.vtype instanceof type_signature_1.AutoTypeSignature) ? venv.getExpressionResult().etype : this.resolveAndEnsureTypeOnly(stmt.sinfo, stmt.vtype, env.terms);
        this.raiseErrorIf(stmt.sinfo, venv !== undefined && !this.m_assembly.subtypeOf(venv.getExpressionResult().etype, vtype), "Expression is not of declared type");
        if (this.m_emitEnabled) {
            const mirvtype = this.m_emitter.registerResolvedTypeReference(vtype);
            this.m_emitter.bodyEmitter.localLifetimeStart(stmt.sinfo, stmt.name, mirvtype.trkey);
            if (venv !== undefined) {
                this.m_emitter.bodyEmitter.emitVarStore(stmt.sinfo, etreg, stmt.name);
            }
        }
        return env.addVar(stmt.name, stmt.isConst, vtype, venv !== undefined, venv !== undefined ? venv.getExpressionResult().etype : vtype);
    }
    checkVariableAssignmentStatement(env, stmt) {
        const vinfo = env.lookupVar(stmt.name);
        this.raiseErrorIf(stmt.sinfo, vinfo === undefined, "Variable was not previously defined");
        this.raiseErrorIf(stmt.sinfo, vinfo.isConst, "Variable defined as const");
        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.exp, etreg, { refok: true, orok: true });
        this.raiseErrorIf(stmt.sinfo, !this.m_assembly.subtypeOf(venv.getExpressionResult().etype, vinfo.declaredType), "Assign value is not subtype of declared variable type");
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitVarStore(stmt.sinfo, etreg, stmt.name);
        }
        return env.setVar(stmt.name, venv.getExpressionResult().etype);
    }
    checkStructuredAssign(sinfo, env, isopt, cpath, assign, expt, allDeclared, allAssigned) {
        if (assign instanceof body_1.IgnoreTermStructuredAssignment) {
            this.raiseErrorIf(sinfo, isopt && !assign.isOptional, "Missing value for required entry");
            const itype = this.resolveAndEnsureTypeOnly(sinfo, assign.termType, env.terms);
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, itype), "Ignore type is not a subtype of declared type");
        }
        else if (assign instanceof body_1.ConstValueStructuredAssignment) {
            this.raiseErrorIf(sinfo, isopt, "Missing value for required entry");
            this.raiseError(sinfo, "Cannot use constants in structured assignment");
        }
        else if (assign instanceof body_1.VariableDeclarationStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[1] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");
            this.raiseErrorIf(sinfo, isopt && !assign.isOptional, "Missing value for required entry");
            const vtype = (assign.vtype instanceof type_signature_1.AutoTypeSignature)
                ? expt
                : (assign.isOptional
                    ? this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms)])
                    : this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms));
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, vtype), "Expression is not of declared type");
            allDeclared.push([assign.isConst, assign.vname, vtype, [...cpath], expt]);
        }
        else if (assign instanceof body_1.VariableAssignmentStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[1] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");
            this.raiseErrorIf(sinfo, isopt && !assign.isOptional, "Missing value for required entry");
            const vinfo = env.lookupVar(assign.vname);
            this.raiseErrorIf(sinfo, vinfo === undefined, "Variable was not previously defined");
            this.raiseErrorIf(sinfo, vinfo.isConst, "Variable defined as const");
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, vinfo.declaredType), "Assign value is not subtype of declared variable type");
            allAssigned.push([assign.vname, [...cpath], expt]);
        }
        else if (assign instanceof body_1.TupleStructuredAssignment) {
            this.raiseErrorIf(sinfo, isopt, "Missing value for required entry");
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, this.m_assembly.getSpecialTupleConceptType()), "Assign value is not subtype of declared variable type");
            const tuptype = resolved_type_1.ResolvedType.create(expt.options.map((opt) => {
                this.raiseErrorIf(sinfo, !(opt instanceof resolved_type_1.ResolvedTupleAtomType), "Cannot use 'Tuple' type in structured assignment");
                return opt;
            }));
            for (let i = 0; i < assign.assigns.length; ++i) {
                const aopt = tuptype.options.some((atom) => atom.types.length < i || atom.types[i].isOptional);
                const ttype = this.getInfoForLoadFromIndex(tuptype, i);
                this.checkStructuredAssign(sinfo, env, aopt, [...cpath, { p: i, t: ttype }], assign.assigns[i], ttype, allDeclared, allAssigned);
            }
            this.raiseErrorIf(sinfo, tuptype.options.some((atom) => atom.types.length > assign.assigns.length), "More values in tuple that assignment");
        }
        else {
            this.raiseErrorIf(sinfo, !(assign instanceof body_1.RecordStructuredAssignment), "Unknown structured assignment type");
            this.raiseErrorIf(sinfo, isopt, "Missing value for required entry");
            this.raiseErrorIf(sinfo, !this.m_assembly.subtypeOf(expt, this.m_assembly.getSpecialRecordConceptType()), "Assign value is not subtype of declared variable type");
            const rectype = resolved_type_1.ResolvedType.create(expt.options.map((opt) => {
                this.raiseErrorIf(sinfo, !(opt instanceof resolved_type_1.ResolvedRecordAtomType), "Cannot use 'Record' type in structured assignment");
                return opt;
            }));
            const rassign = assign;
            for (let i = 0; i < rassign.assigns.length; ++i) {
                const pname = rassign.assigns[i][0];
                const aopt = rectype.options.some((atom) => {
                    const entry = atom.entries.find((re) => re.name === pname);
                    return (entry === undefined || entry.isOptional);
                });
                const ttype = this.getInfoForLoadFromPropertyName(rectype, pname);
                this.checkStructuredAssign(sinfo, env, aopt, [...cpath, { p: pname, t: ttype }], rassign.assigns[i][1], ttype, allDeclared, allAssigned);
            }
            this.raiseErrorIf(sinfo, rectype.options.some((atom) => {
                return atom.entries.some((re) => {
                    const entry = rassign.assigns.find((e) => e[0] === re.name);
                    return entry === undefined;
                });
            }), "More values in record that assignment");
        }
    }
    generateAssignOps(sinfo, ereg, assign) {
        let creg = ereg;
        for (let i = 0; i < assign.length; ++i) {
            const nreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const lt = this.m_emitter.registerResolvedTypeReference(assign[i].t).trkey;
            if (typeof (assign[i].p) === "number") {
                this.m_emitter.bodyEmitter.emitLoadTupleIndex(sinfo, lt, creg, assign[i].p, nreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, lt, creg, assign[i].p, nreg);
            }
            creg = nreg;
        }
        return creg;
    }
    generateEqualityOps(env, sinfo, ergtype, ereg, assign, value) {
        let creg = ereg;
        let ctype = ergtype;
        for (let i = 0; i < assign.length; ++i) {
            const nreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const lt = this.m_emitter.registerResolvedTypeReference(assign[i].t).trkey;
            if (typeof (assign[i].p) === "number") {
                this.m_emitter.bodyEmitter.emitLoadTupleIndex(sinfo, lt, creg, assign[i].p, nreg);
            }
            else {
                this.m_emitter.bodyEmitter.emitLoadProperty(sinfo, lt, creg, assign[i].p, nreg);
            }
            creg = nreg;
            ctype = assign[i].t;
        }
        const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const vrenv = this.checkExpression(env, value, vreg);
        const rreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        this.m_emitter.bodyEmitter.emitBinEq(sinfo, this.m_emitter.registerResolvedTypeReference(ctype).trkey, creg, "==", this.m_emitter.registerResolvedTypeReference(vrenv.getExpressionResult().etype).trkey, vreg, rreg);
        return rreg;
    }
    checkStructuredVariableAssignmentStatement(env, stmt) {
        const expreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const eenv = this.checkExpression(env, stmt.exp, expreg, { refok: true, orok: true });
        let allDeclared = [];
        let allAssigned = [];
        this.checkStructuredAssign(stmt.sinfo, env, false, [], stmt.assign, eenv.getExpressionResult().etype, allDeclared, allAssigned);
        if (this.m_emitEnabled) {
            for (let i = 0; i < allDeclared.length; ++i) {
                const declv = allDeclared[i];
                const mirvtype = this.m_emitter.registerResolvedTypeReference(declv[2]);
                this.m_emitter.bodyEmitter.localLifetimeStart(stmt.sinfo, declv[1], mirvtype.trkey);
                const treg = this.generateAssignOps(stmt.sinfo, expreg, declv[3]);
                this.m_emitter.bodyEmitter.emitVarStore(stmt.sinfo, treg, declv[1]);
            }
            for (let i = 0; i < allAssigned.length; ++i) {
                const assignv = allAssigned[i];
                const treg = this.generateAssignOps(stmt.sinfo, expreg, assignv[1]);
                this.m_emitter.bodyEmitter.emitVarStore(stmt.sinfo, treg, assignv[0]);
            }
        }
        return eenv.multiVarUpdate(allDeclared, allAssigned);
    }
    checkIfElseStatement(env, stmt) {
        const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
        this.raiseErrorIf(stmt.sinfo, stmt.flow.conds.length > 1 && stmt.flow.elseAction === undefined, "Must terminate elseifs with an else clause");
        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lifstmt_done");
        let cenv = env;
        let results = [];
        for (let i = 0; i < stmt.flow.conds.length; ++i) {
            const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const test = this.checkExpressionMultiFlow(cenv, stmt.flow.conds[i].cond, testreg);
            this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");
            const [trueflow, falseflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
            this.raiseErrorIf(stmt.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false expression test is redundant");
            const trueblck = this.m_emitter.bodyEmitter.createNewBlock(`Lifstmt_${i}true`);
            const falseblck = (i < stmt.flow.conds.length - 1 || stmt.flow.elseAction !== undefined) ? this.m_emitter.bodyEmitter.createNewBlock(`Lifstmt_${i}false`) : doneblck;
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitBoolJump(stmt.sinfo, testreg, trueblck, falseblck);
            }
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock(trueblck);
            }
            const truestate = this.checkBlock(type_environment_1.TypeEnvironment.join(this.m_assembly, ...trueflow), stmt.flow.conds[i].action);
            if (this.m_emitEnabled) {
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, doneblck);
                }
                this.m_emitter.bodyEmitter.setActiveBlock(falseblck);
            }
            results.push(truestate);
            cenv = type_environment_1.TypeEnvironment.join(this.m_assembly, ...falseflow);
        }
        if (stmt.flow.elseAction === undefined) {
            results.push(cenv);
        }
        else {
            const aenv = this.checkStatement(cenv, stmt.flow.elseAction);
            results.push(aenv);
            if (this.m_emitEnabled && aenv.hasNormalFlow()) {
                this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, doneblck);
            }
        }
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }
        return type_environment_1.TypeEnvironment.join(this.m_assembly, ...results);
    }
    checkStructuredMatch(sinfo, env, cpath, assign, expt, allDeclared, allAssigned, allEqChecks) {
        if (assign instanceof body_1.IgnoreTermStructuredAssignment) {
            return [this.resolveAndEnsureTypeOnly(sinfo, assign.termType, env.terms), assign.isOptional];
        }
        else if (assign instanceof body_1.ConstValueStructuredAssignment) {
            allEqChecks.push([[...cpath], assign.constValue]);
            const emitRestore = this.m_emitEnabled;
            this.m_emitEnabled = false;
            let ctype = this.checkExpression(env, assign.constValue, this.m_emitter.bodyEmitter.generateTmpRegister()).getExpressionResult().etype;
            this.m_emitEnabled = emitRestore && true;
            return [ctype, false];
        }
        else if (assign instanceof body_1.VariableDeclarationStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[1] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");
            const vtype = (assign.isOptional
                ? this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms)])
                : this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms));
            allDeclared.push([assign.isConst, assign.vname, vtype, [...cpath], vtype]);
            return [this.resolveAndEnsureTypeOnly(sinfo, assign.vtype, env.terms), assign.isOptional];
        }
        else if (assign instanceof body_1.VariableAssignmentStructuredAssignment) {
            this.raiseErrorIf(sinfo, allDeclared.find((decl) => decl[1] === assign.vname) !== undefined || allAssigned.find((asgn) => asgn[0] === assign.vname) !== undefined, "Duplicate variables used in structured assign");
            const vinfo = env.lookupVar(assign.vname);
            this.raiseErrorIf(sinfo, vinfo === undefined, "Variable was not previously defined");
            this.raiseErrorIf(sinfo, vinfo.isConst, "Variable defined as const");
            allAssigned.push([assign.vname, [...cpath], vinfo.declaredType]);
            return [vinfo.declaredType, assign.isOptional];
        }
        else if (assign instanceof body_1.TupleStructuredAssignment) {
            const tupopts = expt.options.filter((opt) => opt instanceof resolved_type_1.ResolvedTupleAtomType);
            this.raiseErrorIf(sinfo, tupopts.length === 0, "Check will always fail");
            const tuptype = resolved_type_1.ResolvedType.create(tupopts);
            const tupcheck = [];
            for (let i = 0; i < assign.assigns.length; ++i) {
                const ttype = this.getInfoForLoadFromIndex(tuptype, i);
                const einfo = this.checkStructuredMatch(sinfo, env, [...cpath, { p: i, t: ttype }], assign.assigns[i], ttype, allDeclared, allAssigned, allEqChecks);
                tupcheck.push(new resolved_type_1.ResolvedTupleAtomTypeEntry(...einfo));
            }
            return [resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedTupleAtomType.create(tupcheck)), false];
        }
        else {
            this.raiseErrorIf(sinfo, !(assign instanceof body_1.RecordStructuredAssignment), "Unknown structured assignment type");
            const recopts = expt.options.filter((opt) => opt instanceof resolved_type_1.ResolvedRecordAtomType);
            this.raiseErrorIf(sinfo, recopts.length === 0, "Check will always fail");
            const rassign = assign;
            const rectype = resolved_type_1.ResolvedType.create(recopts);
            const reccheck = [];
            for (let i = 0; i < rassign.assigns.length; ++i) {
                const pname = rassign.assigns[i][0];
                const ttype = this.getInfoForLoadFromPropertyName(rectype, pname);
                const einfo = this.checkStructuredMatch(sinfo, env, [...cpath, { p: pname, t: ttype }], rassign.assigns[i][1], ttype, allDeclared, allAssigned, allEqChecks);
                reccheck.push(new resolved_type_1.ResolvedRecordAtomTypeEntry(pname, ...einfo));
            }
            return [resolved_type_1.ResolvedType.createSingle(resolved_type_1.ResolvedRecordAtomType.create(reccheck)), false];
        }
    }
    checkMatchGuard(sinfo, midx, vreg, sexp, env, guard, nextlabel, actionlabel, svname, lastoption) {
        let opts = [];
        let nexttype = sexp;
        let mreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        if (guard instanceof body_1.WildcardMatchGuard) {
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitLoadConstBool(sinfo, true, mreg);
            }
            opts = [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), type_environment_1.FlowTypeTruthValue.True)];
        }
        else if (guard instanceof body_1.TypeMatchGuard) {
            const tmatch = this.resolveAndEnsureTypeOnly(sinfo, guard.oftype, env.terms);
            if (this.m_emitEnabled) {
                const mt = this.m_emitter.registerResolvedTypeReference(tmatch);
                this.m_emitter.bodyEmitter.emitTypeOf(sinfo, mreg, mt.trkey, this.m_emitter.registerResolvedTypeReference(sexp).trkey, vreg);
            }
            if (svname === undefined) {
                opts = [env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType())];
            }
            else {
                this.raiseErrorIf(sinfo, this.m_assembly.restrictT(sexp, tmatch).isEmptyType(), "Value is never of type");
                this.raiseErrorIf(sinfo, !lastoption && this.m_assembly.restrictNotT(sexp, tmatch).isEmptyType(), "Value is always of type");
                const tval = env
                    .assumeVar(svname, this.m_assembly.restrictT(sexp, tmatch))
                    .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), type_environment_1.FlowTypeTruthValue.True);
                const ntval = env
                    .assumeVar(svname, this.m_assembly.restrictNotT(sexp, tmatch))
                    .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), type_environment_1.FlowTypeTruthValue.False);
                opts = [tval, ntval];
            }
            nexttype = this.m_assembly.restrictNotT(sexp, tmatch);
        }
        else {
            const sguard = guard;
            let allDeclared = [];
            let allAssigned = [];
            let allEqChecks = [];
            const oftype = this.checkStructuredMatch(sinfo, env, [], sguard.match, sexp, allDeclared, allAssigned, allEqChecks)[0];
            if (this.m_emitEnabled) {
                const oft = this.m_emitter.registerResolvedTypeReference(oftype);
                const tcreg = this.m_emitter.bodyEmitter.generateTmpRegister();
                this.m_emitter.bodyEmitter.emitTypeOf(sinfo, tcreg, oft.trkey, this.m_emitter.registerResolvedTypeReference(sexp).trkey, vreg);
                const filllabel = this.m_emitter.bodyEmitter.createNewBlock(`match${midx}_scfill`);
                if (allEqChecks.length === 0) {
                    this.m_emitter.bodyEmitter.emitRegAssign(sinfo, tcreg, mreg);
                    this.m_emitter.bodyEmitter.emitDirectJump(sinfo, filllabel);
                }
                else {
                    const eqlabel = this.m_emitter.bodyEmitter.createNewBlock(`match${midx}_sceq`);
                    this.m_emitter.bodyEmitter.emitBoolJump(sinfo, tcreg, eqlabel, nextlabel);
                    this.m_emitter.bodyEmitter.setActiveBlock(eqlabel);
                    this.m_emitter.bodyEmitter.emitLoadConstBool(sinfo, true, mreg);
                    for (let i = 0; i < allEqChecks.length; ++i) {
                        const eqreg = this.generateEqualityOps(env, sinfo, sexp, vreg, allEqChecks[i][0], allEqChecks[i][1]);
                        this.m_emitter.bodyEmitter.emitLogicStore(sinfo, mreg, mreg, "&", eqreg);
                    }
                    this.m_emitter.bodyEmitter.emitDirectJump(sinfo, filllabel);
                }
                this.m_emitter.bodyEmitter.setActiveBlock(filllabel);
                for (let i = 0; i < allDeclared.length; ++i) {
                    const declv = allDeclared[i];
                    const mirvtype = this.m_emitter.registerResolvedTypeReference(declv[2]);
                    this.m_emitter.bodyEmitter.localLifetimeStart(sinfo, declv[1], mirvtype.trkey);
                    const treg = this.generateAssignOps(sinfo, vreg, declv[3]);
                    this.m_emitter.bodyEmitter.emitVarStore(sinfo, treg, declv[1]);
                }
                for (let i = 0; i < allAssigned.length; ++i) {
                    const assignv = allAssigned[i];
                    const treg = this.generateAssignOps(sinfo, vreg, assignv[1]);
                    this.m_emitter.bodyEmitter.emitVarStore(sinfo, treg, assignv[0]);
                }
            }
            if (svname === undefined) {
                opts = [
                    env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), type_environment_1.FlowTypeTruthValue.False),
                    env.multiVarUpdate(allDeclared, allAssigned).setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), type_environment_1.FlowTypeTruthValue.True)
                ];
            }
            else {
                this.raiseErrorIf(sinfo, this.m_assembly.restrictT(sexp, oftype).isEmptyType(), "Value is never of type");
                const tval = env
                    .assumeVar(svname, this.m_assembly.restrictT(sexp, oftype))
                    .multiVarUpdate(allDeclared, allAssigned)
                    .setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), type_environment_1.FlowTypeTruthValue.True);
                const ntval = env.setExpressionResult(this.m_assembly, this.m_assembly.getSpecialBoolType(), type_environment_1.FlowTypeTruthValue.False);
                opts = [tval, ntval];
            }
            nexttype = this.m_assembly.restrictNotT(sexp, oftype);
        }
        if (guard.optionalWhen === undefined) {
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitBoolJump(sinfo, mreg, actionlabel, nextlabel);
            }
            return { envinfo: opts, nexttype: nexttype };
        }
        else {
            const [gtrueflow, gfalseflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, opts);
            if (this.m_emitEnabled) {
                const whenblck = this.m_emitter.bodyEmitter.createNewBlock(`match${midx}_when`);
                this.m_emitter.bodyEmitter.emitBoolJump(sinfo, mreg, whenblck, nextlabel);
                this.m_emitter.bodyEmitter.setActiveBlock(whenblck);
            }
            let wreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const wopts = this.checkExpressionMultiFlow(type_environment_1.TypeEnvironment.join(this.m_assembly, ...gtrueflow), guard.optionalWhen, wreg);
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitBoolJump(sinfo, wreg, actionlabel, nextlabel);
            }
            const [wtrueflow, wfalseflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, wopts);
            return { envinfo: [...wtrueflow, ...gfalseflow, ...wfalseflow], nexttype: nexttype };
        }
    }
    checkMatchStatement(env, stmt) {
        const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.sval, vreg);
        const svname = stmt.sval instanceof body_1.AccessVariableExpression ? stmt.sval.name : undefined;
        const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lswitchstmt_done");
        let cenv = venv;
        let vtype = venv.getExpressionResult().etype;
        let results = [];
        for (let i = 0; i < stmt.flow.length; ++i) {
            const nextlabel = this.m_emitter.bodyEmitter.createNewBlock(`Lswitchstmt_${i}next`);
            const actionlabel = this.m_emitter.bodyEmitter.createNewBlock(`Lswitchstmt_${i}action`);
            const test = this.checkMatchGuard(stmt.sinfo, i, vreg, vtype, cenv, stmt.flow[i].check, nextlabel, actionlabel, svname, i === stmt.flow.length - 1);
            vtype = test.nexttype;
            const [trueflow, falseflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test.envinfo);
            this.raiseErrorIf(stmt.sinfo, trueflow.length === 0 || (falseflow.length === 0 && i !== stmt.flow.length - 1), "Expression is always true/false expression test is redundant");
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.setActiveBlock(actionlabel);
            }
            const truestate = this.checkBlock(type_environment_1.TypeEnvironment.join(this.m_assembly, ...trueflow), stmt.flow[i].action);
            if (this.m_emitEnabled) {
                if (truestate.hasNormalFlow()) {
                    this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, doneblck);
                }
                this.m_emitter.bodyEmitter.setActiveBlock(nextlabel);
            }
            results.push(truestate);
            cenv = falseflow.length !== 0 ? type_environment_1.TypeEnvironment.join(this.m_assembly, ...falseflow) : cenv;
        }
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitAbort(stmt.sinfo, true, "exhaustive");
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "exit");
        }
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }
        return type_environment_1.TypeEnvironment.join(this.m_assembly, ...results);
    }
    checkReturnStatement(env, stmt) {
        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const venv = this.checkExpression(env, stmt.value, etreg, { refok: true, orok: false });
        this.raiseErrorIf(stmt.sinfo, env.isInYieldBlock(), "Cannot use return statment inside an expression block");
        if (this.m_emitEnabled) {
            const rtuple = this.generateRefInfoForReturnEmit(venv.getExpressionResult().etype, env);
            this.m_emitter.bodyEmitter.emitReturnAssign(stmt.sinfo, rtuple, env.refparams, etreg);
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "exit");
        }
        return env.setReturn(this.m_assembly, venv.getExpressionResult().etype);
    }
    checkYieldStatement(env, stmt) {
        const yinfo = env.getYieldTargetInfo();
        const venv = this.checkExpression(env, stmt.value, yinfo[0], { refok: true, orok: false });
        this.raiseErrorIf(stmt.sinfo, !env.isInYieldBlock(), "Cannot use yield statment outside expression blocks");
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, yinfo[1]);
            this.m_emitter.bodyEmitter.setActiveBlock(yinfo[1]);
        }
        return env.setYield(this.m_assembly, venv.getExpressionResult().etype);
    }
    checkAbortStatement(env, stmt) {
        if (this.m_emitEnabled) {
            this.m_emitter.bodyEmitter.emitAbort(stmt.sinfo, true, "abort");
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "exit");
        }
        return env.setAbort();
    }
    checkAssertStatement(env, stmt) {
        const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
        const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, stmt.cond, testreg);
        this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");
        const [trueflow, falseflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
        this.raiseErrorIf(stmt.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false assert is redundant");
        if (this.m_emitEnabled && this.m_doAssertCheck) {
            const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lassert_done");
            const failblck = this.m_emitter.bodyEmitter.createNewBlock("Lassert_fail");
            this.m_emitter.bodyEmitter.emitBoolJump(stmt.sinfo, testreg, doneblck, failblck);
            this.m_emitter.bodyEmitter.setActiveBlock(failblck);
            this.m_emitter.bodyEmitter.emitAbort(stmt.sinfo, false, "assert fail");
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "exit");
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }
        return type_environment_1.TypeEnvironment.join(this.m_assembly, ...trueflow);
    }
    checkCheckStatement(env, stmt) {
        const okType = this.m_assembly.typeUnion([this.m_assembly.getSpecialNoneType(), this.m_assembly.getSpecialBoolType()]);
        const testreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const test = this.checkExpressionMultiFlow(env, stmt.cond, testreg);
        this.raiseErrorIf(stmt.sinfo, test.some((opt) => !this.m_assembly.subtypeOf(opt.getExpressionResult().etype, okType)), "Type of logic op must be Bool | None");
        const [trueflow, falseflow] = type_environment_1.TypeEnvironment.convertToBoolFlowsOnExpressionResult(this.m_assembly, test);
        this.raiseErrorIf(stmt.sinfo, trueflow.length === 0 || falseflow.length === 0, "Expression is always true/false check is redundant");
        if (this.m_emitEnabled) {
            const doneblck = this.m_emitter.bodyEmitter.createNewBlock("Lcheck_done");
            const failblck = this.m_emitter.bodyEmitter.createNewBlock("Lcheck_fail");
            this.m_emitter.bodyEmitter.emitBoolJump(stmt.sinfo, testreg, doneblck, failblck);
            this.m_emitter.bodyEmitter.setActiveBlock(failblck);
            this.m_emitter.bodyEmitter.emitAbort(stmt.sinfo, true, "check fail");
            this.m_emitter.bodyEmitter.emitDirectJump(stmt.sinfo, "exit");
            this.m_emitter.bodyEmitter.setActiveBlock(doneblck);
        }
        return type_environment_1.TypeEnvironment.join(this.m_assembly, ...trueflow);
    }
    checkDebugStatement(env, stmt) {
        if (stmt.value === undefined) {
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitDebugBreak(stmt.sinfo);
            }
        }
        else {
            const vreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            this.checkExpression(env, stmt.value, vreg);
            if (this.m_emitEnabled) {
                this.m_emitter.bodyEmitter.emitDebugPrint(stmt.sinfo, vreg);
            }
        }
        return env;
    }
    checkStatement(env, stmt) {
        this.raiseErrorIf(stmt.sinfo, !env.hasNormalFlow(), "Unreachable statements");
        switch (stmt.tag) {
            case body_1.StatementTag.EmptyStatement:
                return env;
            case body_1.StatementTag.VariableDeclarationStatement:
                return this.checkVariableDeclarationStatement(env, stmt);
            case body_1.StatementTag.VariableAssignmentStatement:
                return this.checkVariableAssignmentStatement(env, stmt);
            case body_1.StatementTag.StructuredVariableAssignmentStatement:
                return this.checkStructuredVariableAssignmentStatement(env, stmt);
            case body_1.StatementTag.IfElseStatement:
                return this.checkIfElseStatement(env, stmt);
            case body_1.StatementTag.MatchStatement:
                return this.checkMatchStatement(env, stmt);
            case body_1.StatementTag.ReturnStatement:
                return this.checkReturnStatement(env, stmt);
            case body_1.StatementTag.YieldStatement:
                return this.checkYieldStatement(env, stmt);
            case body_1.StatementTag.AbortStatement:
                return this.checkAbortStatement(env, stmt);
            case body_1.StatementTag.AssertStatement:
                return this.checkAssertStatement(env, stmt);
            case body_1.StatementTag.CheckStatement:
                return this.checkCheckStatement(env, stmt);
            case body_1.StatementTag.DebugStatement:
                return this.checkDebugStatement(env, stmt);
            default:
                this.raiseErrorIf(stmt.sinfo, stmt.tag !== body_1.StatementTag.BlockStatement, "Unknown statement");
                return this.checkBlock(env, stmt);
        }
    }
    checkBlock(env, stmt) {
        let cenv = env.pushLocalScope();
        for (let i = 0; i < stmt.statements.length; ++i) {
            if (!cenv.hasNormalFlow()) {
                break;
            }
            cenv = this.checkStatement(cenv, stmt.statements[i]);
        }
        if (this.m_emitEnabled && cenv.hasNormalFlow()) {
            const deadvars = cenv.getCurrentFrameNames();
            for (let i = 0; i < deadvars.length; ++i) {
                this.m_emitter.bodyEmitter.localLifetimeEnd(stmt.sinfo, deadvars[i]);
            }
        }
        return cenv.popLocalScope();
    }
    checkBody(env, body, args, resultType) {
        if (body.body instanceof body_1.Expression) {
            if (this.m_emitEnabled) {
                this.m_emitter.initializeBodyEmitter();
            }
            const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
            const evalue = this.checkExpression(env, body.body, etreg);
            if (this.m_emitEnabled) {
                const rtuple = this.generateRefInfoForReturnEmit(resultType, env);
                this.m_emitter.bodyEmitter.emitReturnAssign(body.body.sinfo, rtuple, env.refparams, etreg);
                this.m_emitter.bodyEmitter.emitDirectJump(body.body.sinfo, "exit");
            }
            this.raiseErrorIf(body.body.sinfo, !this.m_assembly.subtypeOf(evalue.getExpressionResult().etype, resultType), "Did not produce the expected return type");
            return this.m_emitEnabled ? this.m_emitter.bodyEmitter.getBody(this.m_file, body.body.sinfo, env.scope, args) : undefined;
        }
        else if (body.body instanceof body_1.BlockStatement) {
            if (this.m_emitEnabled) {
                this.m_emitter.initializeBodyEmitter();
            }
            const renv = this.checkBlock(env, body.body);
            this.raiseErrorIf(body.body.sinfo, renv.hasNormalFlow(), "Not all flow paths return a value!");
            this.raiseErrorIf(body.body.sinfo, !this.m_assembly.subtypeOf(renv.returnResult, resultType), "Did not produce the expected return type");
            return this.m_emitEnabled ? this.m_emitter.bodyEmitter.getBody(this.m_file, body.body.sinfo, env.scope, args) : undefined;
        }
        else {
            return undefined;
        }
    }
    checkExpressionAsBody(env, bkey, exp, ofType) {
        if (this.m_emitEnabled) {
            this.m_emitter.initializeBodyEmitter();
        }
        const etreg = this.m_emitter.bodyEmitter.generateTmpRegister();
        const evalue = this.checkExpression(env, exp, etreg);
        if (this.m_emitEnabled) {
            const rtuple = this.generateRefInfoForReturnEmit(ofType, env);
            this.m_emitter.bodyEmitter.emitReturnAssign(exp.sinfo, rtuple, env.refparams, etreg);
            this.m_emitter.bodyEmitter.emitDirectJump(exp.sinfo, "exit");
        }
        this.raiseErrorIf(exp.sinfo, !this.m_assembly.subtypeOf(evalue.getExpressionResult().etype, ofType), "Did not produce the expected type");
        let argTypes = new Map();
        env.args.forEach((arg, name) => {
            const atype = this.m_emitter.registerResolvedTypeReference(arg.declaredType);
            argTypes.set(name, atype);
        });
        return this.m_emitter.bodyEmitter.getBody(this.m_file, exp.sinfo, bkey, argTypes);
    }
    abortIfTooManyErrors() {
        if (this.m_errors.length > 20) {
            throw new Error("More than 20 errors ... halting type checker");
        }
    }
    processPragmas(sinfo, pragmas) {
        const emptybinds = new Map();
        return pragmas.map((prg) => {
            const ptype = this.resolveAndEnsureTypeOnly(sinfo, prg[0], emptybinds);
            const pkey = this.m_emitter.registerResolvedTypeReference(ptype);
            return [pkey, prg[1]];
        });
    }
    processOOType(tkey, tdecl, binds) {
        try {
            this.m_file = tdecl.srcFile;
            let terms = new Map();
            tdecl.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name))));
            const provides = tdecl.provides.map((provide) => {
                const ptype = this.resolveAndEnsureTypeOnly(new parser_1.SourceInfo(0, 0, 0, 0), provide, binds);
                const cpt = (ptype.options[0]).conceptTypes[0];
                this.m_emitter.registerTypeInstantiation(cpt.concept, cpt.binds);
                return this.m_emitter.registerResolvedTypeReference(ptype).trkey;
            });
            const invariants = this.m_doInvariantCheck
                ? tdecl.invariants.map((inv) => {
                    const thistype = resolved_type_1.ResolvedType.createSingle(tdecl instanceof assembly_1.EntityTypeDecl ? resolved_type_1.ResolvedEntityAtomType.create(tdecl, binds) : resolved_type_1.ResolvedConceptAtomType.create([resolved_type_1.ResolvedConceptAtomTypeEntry.create(tdecl, binds)]));
                    const invscope = mir_emitter_1.MIRKeyGenerator.generateBodyKey("invariant", tkey);
                    const invenv = type_environment_1.TypeEnvironment.createInitialEnvForCall(invscope, binds, [], new Map(), new Map().set("this", new type_environment_1.VarInfo(thistype, true, false, true, thistype)));
                    return this.checkExpressionAsBody(invenv, invscope, inv, this.m_assembly.getSpecialBoolType());
                })
                : [];
            //
            //TODO: we need to check inheritance and provides rules here -- diamonds, virtual/abstract/override use, etc.
            //
            const fields = [];
            tdecl.memberFields.forEach((f) => {
                const fkey = mir_emitter_1.MIRKeyGenerator.generateFieldKey(tdecl, binds, f.name);
                const fdscope = mir_emitter_1.MIRKeyGenerator.generateBodyKey("fdefault", fkey);
                const fpragmas = this.processPragmas(f.sourceLocation, f.pragmas);
                const dtypeResolved = this.resolveAndEnsureTypeOnly(f.sourceLocation, f.declaredType, binds);
                const dtype = this.m_emitter.registerResolvedTypeReference(dtypeResolved);
                let value = undefined;
                if (f.value !== undefined) {
                    const fdenv = type_environment_1.TypeEnvironment.createInitialEnvForCall(fdscope, binds, [], new Map(), new Map());
                    value = this.checkExpressionAsBody(fdenv, fdscope, f.value, dtypeResolved);
                }
                const fname = `${tdecl.ns}::${tdecl.name}.${f.name}`;
                const mfield = new mir_assembly_1.MIRFieldDecl(tkey, f.attributes, fname, f.sourceLocation, f.srcFile, fkey, fpragmas, f.name, dtype.trkey, value);
                fields.push(mfield);
                this.m_emitter.masm.fieldDecls.set(fkey, mfield);
            });
            const ooname = `${tdecl.ns}::${tdecl.name}`;
            const pragmas = this.processPragmas(tdecl.sourceLocation, tdecl.pragmas);
            if (tdecl instanceof assembly_1.EntityTypeDecl) {
                const mirentity = new mir_assembly_1.MIREntityTypeDecl(ooname, tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, pragmas, tdecl.ns, tdecl.name, terms, provides, invariants, fields, tdecl.isTypeACollectionEntity(), tdecl.isTypeAMapEntity(), tdecl.isEnum, tdecl.isKey);
                this.m_emitter.masm.entityDecls.set(tkey, mirentity);
            }
            else {
                const mirconcept = new mir_assembly_1.MIRConceptTypeDecl(ooname, tdecl.sourceLocation, tdecl.srcFile, tkey, tdecl.attributes, pragmas, tdecl.ns, tdecl.name, terms, provides, invariants, fields);
                this.m_emitter.masm.conceptDecls.set(tkey, mirconcept);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }
    processGlobal(gkey, gdecl) {
        try {
            const emptybinds = new Map();
            this.m_file = gdecl.srcFile;
            const gscope = mir_emitter_1.MIRKeyGenerator.generateBodyKey("const", gkey);
            const pragmas = this.processPragmas(gdecl.sourceLocation, gdecl.pragmas);
            const ddecltype = this.resolveAndEnsureTypeOnly(gdecl.sourceLocation, gdecl.declaredType, emptybinds);
            const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
            const genv = type_environment_1.TypeEnvironment.createInitialEnvForCall(gscope, emptybinds, [], new Map(), new Map());
            const vbody = this.checkExpressionAsBody(genv, gscope, gdecl.value, ddecltype);
            const mirglobal = new mir_assembly_1.MIRConstantDecl(undefined, `${gdecl.ns}::${gdecl.name}`, gkey, pragmas, gdecl.sourceLocation, gdecl.srcFile, dtype.trkey, vbody);
            this.m_emitter.masm.constantDecls.set(gkey, mirglobal);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }
    processConst(ckey, containingDecl, cdecl, binds) {
        try {
            this.m_file = cdecl.srcFile;
            const cscope = mir_emitter_1.MIRKeyGenerator.generateBodyKey("const", ckey);
            const pragmas = this.processPragmas(cdecl.sourceLocation, cdecl.pragmas);
            const enclosingType = mir_emitter_1.MIRKeyGenerator.generateTypeKey(containingDecl, binds);
            const ddecltype = this.resolveAndEnsureTypeOnly(cdecl.sourceLocation, cdecl.declaredType, binds);
            const dtype = this.m_emitter.registerResolvedTypeReference(ddecltype);
            const cenv = type_environment_1.TypeEnvironment.createInitialEnvForCall(cscope, binds, [], new Map(), new Map());
            const vbody = this.checkExpressionAsBody(cenv, cscope, cdecl.value, ddecltype);
            const mirconst = new mir_assembly_1.MIRConstantDecl(enclosingType, `${enclosingType}::${cdecl.name}`, ckey, pragmas, cdecl.sourceLocation, cdecl.srcFile, dtype.trkey, vbody);
            this.m_emitter.masm.constantDecls.set(ckey, mirconst);
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }
    processInvokeInfo(enclosingDecl, iname, ikey, sinfo, invoke, binds, pcodes, pargs) {
        this.checkInvokeDecl(sinfo, invoke, binds, pcodes);
        let terms = new Map();
        invoke.terms.forEach((term) => terms.set(term.name, this.m_emitter.registerResolvedTypeReference(binds.get(term.name))));
        const recursive = invoke.recursive === "yes" || (invoke.recursive === "cond" && pcodes.some((pc) => pc.code.recursive === "yes"));
        const pragmas = this.processPragmas(invoke.sourceLocation, invoke.pragmas);
        let cargs = new Map();
        let fargs = new Map();
        let argTypes = new Map();
        let refNames = [];
        let params = [];
        invoke.params.forEach((p) => {
            const pdecltype = this.m_assembly.normalizeTypeGeneral(p.type, binds);
            if (pdecltype instanceof resolved_type_1.ResolvedFunctionType) {
                const pcarg = { pcode: pcodes[fargs.size], captured: [...pcodes[fargs.size].captured].map((cc) => cc[0]).sort() };
                fargs.set(p.name, pcarg);
            }
            else {
                const ptype = p.isOptional ? this.m_assembly.typeUnion([pdecltype, this.m_assembly.getSpecialNoneType()]) : pdecltype;
                cargs.set(p.name, new type_environment_1.VarInfo(ptype, !p.isRef, false, true, ptype));
                if (p.isRef) {
                    refNames.push(p.name);
                }
                const mtype = this.m_emitter.registerResolvedTypeReference(ptype);
                argTypes.set(p.name, mtype);
                params.push(new mir_assembly_1.MIRFunctionParameter(p.name, mtype.trkey));
            }
        });
        if (invoke.optRestType !== undefined) {
            const rtype = this.resolveAndEnsureTypeOnly(sinfo, invoke.optRestType, binds);
            cargs.set(invoke.optRestName, new type_environment_1.VarInfo(rtype, true, false, true, rtype));
            const resttype = this.m_emitter.registerResolvedTypeReference(rtype);
            argTypes.set(invoke.optRestName, resttype);
            params.push(new mir_assembly_1.MIRFunctionParameter(invoke.optRestName, resttype.trkey));
        }
        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new type_environment_1.VarInfo(pargs[i][1], true, true, true, pargs[i][1]));
            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            argTypes.set(this.m_emitter.bodyEmitter.generateCapturedVarName(pargs[i][0]), ctype);
            params.push(new mir_assembly_1.MIRFunctionParameter(this.m_emitter.bodyEmitter.generateCapturedVarName(pargs[i][0]), ctype.trkey));
        }
        const resolvedResult = this.resolveAndEnsureTypeOnly(sinfo, invoke.resultType, binds);
        let resultType = this.m_emitter.registerResolvedTypeReference(resolvedResult);
        if (invoke.params.some((p) => p.isRef)) {
            const pout = invoke.params.filter((p) => p.isRef).map((p) => this.m_emitter.registerResolvedTypeReference(this.resolveAndEnsureTypeOnly(sinfo, p.type, binds)));
            resultType = mir_assembly_1.MIRType.createSingle(mir_assembly_1.MIRTupleType.create([resultType, ...pout].map((tt) => new mir_assembly_1.MIRTupleTypeEntry(tt, false))));
        }
        const iscope = mir_emitter_1.MIRKeyGenerator.generateBodyKey("invoke", ikey);
        const env = type_environment_1.TypeEnvironment.createInitialEnvForCall(iscope, binds, refNames, fargs, cargs);
        const prescope = mir_emitter_1.MIRKeyGenerator.generateBodyKey("pre", ikey);
        const preargs = new Map(cargs);
        const preconds = invoke.preconditions.filter((pre) => this.m_doPrePostCheck || pre[1]).map((pre) => {
            const preenv = type_environment_1.TypeEnvironment.createInitialEnvForCall(prescope, binds, [], fargs, preargs);
            return [this.checkExpressionAsBody(preenv, prescope, pre[0], this.m_assembly.getSpecialBoolType()), pre[1]];
        });
        const postscope = mir_emitter_1.MIRKeyGenerator.generateBodyKey("post", ikey);
        const postargs = new Map(cargs).set("_return_", new type_environment_1.VarInfo(resolvedResult, true, false, true, resolvedResult));
        const postconds = invoke.postconditions.filter((post) => this.m_doPrePostCheck).map((post) => {
            const postenv = type_environment_1.TypeEnvironment.createInitialEnvForCall(postscope, binds, [], fargs, postargs);
            return this.checkExpressionAsBody(postenv, postscope, post, this.m_assembly.getSpecialBoolType());
        });
        if (typeof (invoke.body.body) === "string") {
            let mpc = new Map();
            fargs.forEach((v, k) => mpc.set(k, { code: mir_emitter_1.MIRKeyGenerator.generatePCodeKey(v.pcode.code), cargs: [...v.captured].map((cname) => this.m_emitter.bodyEmitter.generateCapturedVarName(cname)) }));
            let mbinds = new Map();
            binds.forEach((v, k) => mbinds.set(k, this.m_emitter.registerResolvedTypeReference(v).trkey));
            return new mir_assembly_1.MIRInvokePrimitiveDecl(enclosingDecl, iname, ikey, invoke.attributes, recursive, pragmas, sinfo, invoke.srcFile, mbinds, params, resultType.trkey, preconds, postconds, invoke.body.body, mpc);
        }
        else {
            const mirbody = this.checkBody(env, invoke.body, argTypes, resolvedResult);
            this.raiseErrorIf(sinfo, mirbody === undefined, "Type check of body failed");
            return new mir_assembly_1.MIRInvokeBodyDecl(enclosingDecl, iname, ikey, invoke.attributes, recursive, pragmas, sinfo, invoke.srcFile, params, resultType.trkey, preconds, postconds, mirbody);
        }
    }
    processPCodeInfo(iname, ikey, sinfo, pci, binds, fsig, pargs) {
        this.checkPCodeDecl(sinfo, fsig, pci.recursive);
        const pragmas = this.processPragmas(pci.sourceLocation, pci.pragmas);
        let cargs = new Map();
        let fargs = new Map();
        let argTypes = new Map();
        let refNames = [];
        let params = [];
        for (let i = 0; i < pci.params.length; ++i) {
            const p = fsig.params[i];
            const ptype = p.isOptional ? this.m_assembly.typeUnion([p.type, this.m_assembly.getSpecialNoneType()]) : p.type;
            cargs.set(pci.params[i].name, new type_environment_1.VarInfo(ptype, !p.isRef, false, true, ptype));
            if (p.isRef) {
                refNames.push(p.name);
            }
            const mtype = this.m_emitter.registerResolvedTypeReference(ptype);
            argTypes.set(pci.params[i].name, mtype);
            params.push(new mir_assembly_1.MIRFunctionParameter(pci.params[i].name, mtype.trkey));
        }
        if (fsig.optRestParamType !== undefined) {
            cargs.set(pci.optRestName, new type_environment_1.VarInfo(fsig.optRestParamType, true, false, true, fsig.optRestParamType));
            const resttype = this.m_emitter.registerResolvedTypeReference(fsig.optRestParamType);
            argTypes.set(pci.optRestName, resttype);
            params.push(new mir_assembly_1.MIRFunctionParameter(pci.optRestName, resttype.trkey));
        }
        for (let i = 0; i < pargs.length; ++i) {
            cargs.set(pargs[i][0], new type_environment_1.VarInfo(pargs[i][1], true, true, true, pargs[i][1]));
            const ctype = this.m_emitter.registerResolvedTypeReference(pargs[i][1]);
            argTypes.set(this.m_emitter.bodyEmitter.generateCapturedVarName(pargs[i][0]), ctype);
            params.push(new mir_assembly_1.MIRFunctionParameter(this.m_emitter.bodyEmitter.generateCapturedVarName(pargs[i][0]), ctype.trkey));
        }
        let resultType = this.m_emitter.registerResolvedTypeReference(fsig.resultType);
        if (fsig.params.some((p) => p.isRef)) {
            const pout = fsig.params.filter((p) => p.isRef).map((p) => this.m_emitter.registerResolvedTypeReference(p.type));
            resultType = mir_assembly_1.MIRType.createSingle(mir_assembly_1.MIRTupleType.create([resultType, ...pout].map((tt) => new mir_assembly_1.MIRTupleTypeEntry(tt, false))));
        }
        const env = type_environment_1.TypeEnvironment.createInitialEnvForCall(mir_emitter_1.MIRKeyGenerator.generateBodyKey("invoke", ikey), binds, refNames, fargs, cargs);
        const mirbody = this.checkBody(env, pci.body, argTypes, fsig.resultType);
        this.raiseErrorIf(sinfo, mirbody === undefined, "Type check of body failed");
        return new mir_assembly_1.MIRInvokeBodyDecl(undefined, iname, ikey, pci.attributes, pci.recursive === "yes", pragmas, sinfo, pci.srcFile, params, resultType.trkey, [], [], mirbody);
    }
    processNamespaceFunction(fkey, f, binds, pcodes, cargs) {
        try {
            this.m_file = f.srcFile;
            const iname = `${f.ns}::${f.name}`;
            const invinfo = this.processInvokeInfo(undefined, iname, fkey, f.sourceLocation, f.invoke, binds, pcodes, cargs);
            if (invinfo instanceof mir_assembly_1.MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(fkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(fkey, invinfo);
            }
            if (f.attributes.includes("entrypoint")) {
                this.m_emitter.masm.entryPoints.push(invinfo.key);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }
    processLambdaFunction(lkey, invoke, sigt, binds, cargs) {
        try {
            this.m_file = invoke.srcFile;
            const iname = `fn::${invoke.sourceLocation.line}`;
            const invinfo = this.processPCodeInfo(iname, lkey, invoke.sourceLocation, invoke, binds, sigt, cargs);
            if (invinfo instanceof mir_assembly_1.MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(lkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(lkey, invinfo);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }
    processStaticFunction(skey, ctype, cbinds, sfdecl, binds, pcodes, cargs) {
        try {
            this.m_file = sfdecl.srcFile;
            const enclosingdecl = mir_emitter_1.MIRKeyGenerator.generateTypeKey(ctype, cbinds);
            const iname = `${ctype.ns}::${ctype.name}::${sfdecl.name}`;
            const invinfo = this.processInvokeInfo(enclosingdecl, iname, skey, sfdecl.sourceLocation, sfdecl.invoke, binds, pcodes, cargs);
            if (invinfo instanceof mir_assembly_1.MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(skey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(skey, invinfo);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }
    processMethodFunction(vkey, mkey, ctype, cbinds, mdecl, binds, pcodes, cargs) {
        if (this.m_emitter.masm.primitiveInvokeDecls.has(mkey) || this.m_emitter.masm.invokeDecls.has(mkey)) {
            return;
        }
        try {
            this.m_file = mdecl.srcFile;
            const enclosingdecl = mir_emitter_1.MIRKeyGenerator.generateTypeKey(ctype, cbinds);
            const iname = `${ctype.ns}::${ctype.name}->${mdecl.name}`;
            const invinfo = this.processInvokeInfo(enclosingdecl, iname, mkey, mdecl.sourceLocation, mdecl.invoke, binds, pcodes, cargs);
            if (invinfo instanceof mir_assembly_1.MIRInvokePrimitiveDecl) {
                this.m_emitter.masm.primitiveInvokeDecls.set(mkey, invinfo);
            }
            else {
                this.m_emitter.masm.invokeDecls.set(mkey, invinfo);
            }
            const tkey = mir_emitter_1.MIRKeyGenerator.generateTypeKey(ctype, cbinds);
            if (ctype instanceof assembly_1.EntityTypeDecl) {
                this.m_emitter.masm.entityDecls.get(tkey).vcallMap.set(vkey, mkey);
            }
            else {
                this.m_emitter.masm.conceptDecls.get(tkey).vcallMap.set(vkey, mkey);
            }
        }
        catch (ex) {
            this.m_emitEnabled = false;
            this.abortIfTooManyErrors();
        }
    }
}
exports.TypeChecker = TypeChecker;
//# sourceMappingURL=type_checker.js.map