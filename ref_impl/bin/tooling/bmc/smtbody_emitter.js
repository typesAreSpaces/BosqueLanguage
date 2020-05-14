"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const mir_assembly_1 = require("../../compiler/mir_assembly");
const smttype_emitter_1 = require("./smttype_emitter");
const mir_ops_1 = require("../../compiler/mir_ops");
const smt_exp_1 = require("./smt_exp");
const assert = require("assert");
const mir_emitter_1 = require("../../compiler/mir_emitter");
function NOT_IMPLEMENTED(msg) {
    throw new Error(`Not Implemented: ${msg}`);
}
class SMTBodyEmitter {
    constructor(assembly, typegen, default_gas) {
        this.default_gas = 4;
        this.errorCodes = new Map();
        this.bmcCodes = new Map();
        this.bmcGas = new Map();
        this.typecheckgas = 4;
        this.currentFile = "[No File]";
        this.tmpvarctr = 0;
        this.currentSCC = new Set();
        this.vtypes = new Map();
        this.subtypeOrderCtr = 0;
        this.subtypeFMap = new Map();
        this.assembly = assembly;
        this.typegen = typegen;
        this.default_gas = default_gas;
        this.typecheckgas = default_gas;
        this.currentRType = typegen.noneType;
    }
    generateTempName() {
        return `@tmpvar@${this.tmpvarctr++}`;
    }
    generateErrorCreate(sinfo, rtype) {
        const errorinfo = `${this.currentFile} @ line ${sinfo.line} -- column ${sinfo.column}`;
        if (!this.errorCodes.has(errorinfo)) {
            this.errorCodes.set(errorinfo, this.errorCodes.size);
        }
        const errid = this.errorCodes.get(errorinfo);
        return new smt_exp_1.SMTValue(`(result_error@${rtype} (result_error ${errid}))`);
    }
    getErrorIds(...sinfos) {
        const ekeys = sinfos.map((sinfo) => `${this.currentFile} @ line ${sinfo.line} -- column ${sinfo.column}`);
        return [...new Set(ekeys.map((k) => this.errorCodes.get(k)))].sort();
    }
    getGasForOperation(key) {
        if (!this.bmcGas.has(key)) {
            this.bmcGas.set(key, this.default_gas);
        }
        return this.bmcGas.get(key);
    }
    generateBMCLimitCreate(key, rtype) {
        if (!this.bmcCodes.has(key)) {
            this.bmcCodes.set(key, this.bmcCodes.size);
        }
        const errid = this.bmcCodes.get(key);
        return new smt_exp_1.SMTValue(`(result_error@${rtype} (result_bmc ${errid}))`);
    }
    varNameToSMTName(name) {
        if (name === "_return_") {
            return "_return_";
        }
        else {
            return this.typegen.mangleStringForSMT(name);
        }
    }
    varToSMTName(varg) {
        return this.varNameToSMTName(varg.nameID);
    }
    invokenameToSMT(ivk) {
        return this.typegen.mangleStringForSMT(ivk);
    }
    getArgType(arg) {
        if (arg instanceof mir_ops_1.MIRRegisterArgument) {
            return this.vtypes.get(arg.nameID);
        }
        else {
            if (arg instanceof mir_ops_1.MIRConstantNone) {
                return this.typegen.noneType;
            }
            else if (arg instanceof mir_ops_1.MIRConstantTrue || arg instanceof mir_ops_1.MIRConstantFalse) {
                return this.typegen.boolType;
            }
            else if (arg instanceof mir_ops_1.MIRConstantInt) {
                return this.typegen.intType;
            }
            else {
                return this.typegen.stringType;
            }
        }
    }
    generateConstantExp(cval, into) {
        if (cval instanceof mir_ops_1.MIRConstantNone) {
            return this.typegen.coerce(new smt_exp_1.SMTValue("bsqkey_none"), this.typegen.noneType, into);
        }
        else if (cval instanceof mir_ops_1.MIRConstantTrue) {
            return this.typegen.coerce(new smt_exp_1.SMTValue("true"), this.typegen.boolType, into);
        }
        else if (cval instanceof mir_ops_1.MIRConstantFalse) {
            return this.typegen.coerce(new smt_exp_1.SMTValue("false"), this.typegen.boolType, into);
        }
        else if (cval instanceof mir_ops_1.MIRConstantInt) {
            return this.typegen.coerce(new smt_exp_1.SMTValue(cval.value), this.typegen.intType, into);
        }
        else {
            assert(cval instanceof mir_ops_1.MIRConstantString);
            return this.typegen.coerce(new smt_exp_1.SMTValue(cval.value), this.typegen.stringType, into);
        }
    }
    argToSMT(arg, into) {
        if (arg instanceof mir_ops_1.MIRRegisterArgument) {
            return this.typegen.coerce(new smt_exp_1.SMTValue(this.varToSMTName(arg)), this.getArgType(arg), into);
        }
        else {
            return this.generateConstantExp(arg, into);
        }
    }
    generateTruthyConvert(arg) {
        const argtype = this.getArgType(arg);
        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return new smt_exp_1.SMTValue("false");
        }
        else if (this.assembly.subtypeOf(argtype, this.typegen.boolType)) {
            return this.argToSMT(arg, this.typegen.boolType);
        }
        else if (this.typegen.isKeyType(argtype)) {
            return new smt_exp_1.SMTValue(`(= ${this.argToSMT(arg, this.typegen.keyType).emit()} (bsqkey_bool true))`);
        }
        else {
            return new smt_exp_1.SMTValue(`(= ${this.argToSMT(arg, this.typegen.anyType).emit()} (bsqterm_key (bsqkey_bool true)))`);
        }
    }
    generateNoneCheck(arg) {
        const argtype = this.getArgType(arg);
        if (this.assembly.subtypeOf(argtype, this.typegen.noneType)) {
            return new smt_exp_1.SMTValue("true");
        }
        else if (!this.assembly.subtypeOf(this.typegen.noneType, argtype)) {
            return new smt_exp_1.SMTValue("false");
        }
        else if (this.typegen.isUEntityType(argtype)) {
            return new smt_exp_1.SMTValue(`(is-${this.typegen.generateEntityNoneConstructor(smttype_emitter_1.SMTTypeEmitter.getUEntityType(argtype).ekey)} ${this.argToSMT(arg, argtype).emit()})`);
        }
        else if (this.typegen.isKeyType(argtype)) {
            return new smt_exp_1.SMTValue(`(= ${this.argToSMT(arg, this.typegen.keyType).emit()} bsqkey_none)`);
        }
        else {
            return new smt_exp_1.SMTValue(`(= ${this.argToSMT(arg, this.typegen.anyType).emit()} (bsqterm_key bsqkey_none))`);
        }
    }
    static expBodyTrivialCheck(bd) {
        if (bd.body.size !== 2 || bd.body.get("entry").ops.length !== 2) {
            return undefined;
        }
        const op = bd.body.get("entry").ops[0];
        if (op.tag === mir_ops_1.MIROpTag.MIRLoadConst) {
            return op;
        }
        else {
            return undefined;
        }
    }
    generateAccessConstantValue(cp) {
        const cdecl = this.assembly.constantDecls.get(cp.ckey);
        const top = SMTBodyEmitter.expBodyTrivialCheck(cdecl.value);
        if (top !== undefined) {
            const cvv = top;
            return new smt_exp_1.SMTLet(this.varToSMTName(cp.trgt), this.generateConstantExp(cvv.src, this.getArgType(cvv.trgt)));
        }
        else {
            const tv = this.generateTempName();
            const ivrtype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(cdecl.declaredType));
            const resulttype = this.typegen.typeToSMTCategory(this.currentRType);
            const constexp = new smt_exp_1.SMTValue(this.invokenameToSMT(cdecl.value.bkey));
            const checkerror = new smt_exp_1.SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const extracterror = (ivrtype !== resulttype) ? new smt_exp_1.SMTValue(`(result_error@${this.typegen.typeToSMTCategory(this.currentRType)} (result_error_code@${ivrtype} ${tv}))`) : new smt_exp_1.SMTValue(tv);
            const normalassign = new smt_exp_1.SMTLet(this.varToSMTName(cp.trgt), new smt_exp_1.SMTValue(`(result_success_value@${ivrtype} ${tv})`));
            return new smt_exp_1.SMTLet(tv, constexp, new smt_exp_1.SMTCond(checkerror, extracterror, normalassign));
        }
    }
    generateLoadFieldDefaultValue(ld) {
        const fdecl = this.assembly.fieldDecls.get(ld.fkey);
        const top = SMTBodyEmitter.expBodyTrivialCheck(fdecl.value);
        if (top !== undefined) {
            const cvv = top;
            return new smt_exp_1.SMTLet(this.varToSMTName(ld.trgt), this.generateConstantExp(cvv.src, this.getArgType(cvv.trgt)));
        }
        else {
            const tv = this.generateTempName();
            const ivrtype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(fdecl.declaredType));
            const resulttype = this.typegen.typeToSMTCategory(this.currentRType);
            const constexp = new smt_exp_1.SMTValue(this.invokenameToSMT(fdecl.value.bkey));
            const checkerror = new smt_exp_1.SMTValue(`(is-result_error@${ivrtype} ${tv})`);
            const extracterror = (ivrtype !== resulttype) ? new smt_exp_1.SMTValue(`(result_error@${resulttype} (result_error_code@${ivrtype} ${tv}))`) : new smt_exp_1.SMTValue(tv);
            const normalassign = new smt_exp_1.SMTLet(this.varToSMTName(ld.trgt), new smt_exp_1.SMTValue(`(result_success_value@${ivrtype} ${tv})`));
            return new smt_exp_1.SMTLet(tv, constexp, new smt_exp_1.SMTCond(checkerror, extracterror, normalassign));
        }
    }
    generateMIRConstructorPrimary(cp) {
        const ctype = this.assembly.entityDecls.get(cp.tkey);
        const fvals = cp.args.map((arg, i) => {
            const ftype = this.typegen.getMIRType(ctype.fields[i].declaredType);
            return this.argToSMT(arg, ftype).emit();
        });
        const smtctype = this.typegen.generateEntityConstructor(cp.tkey);
        const cexp = ctype.fields.length === 0 ? new smt_exp_1.SMTValue(smtctype) : new smt_exp_1.SMTValue(`(${smtctype} ${fvals.join(" ")})`);
        const bindexp = new smt_exp_1.SMTLet(this.varToSMTName(cp.trgt), cexp);
        if (ctype.invariants.length === 0) {
            return bindexp;
        }
        else {
            const testexp = new smt_exp_1.SMTValue(`(${this.typegen.mangleStringForSMT("invariant::" + cp.tkey)} ${this.varToSMTName(cp.trgt)})`);
            const resulttype = this.typegen.typeToSMTCategory(this.currentRType);
            const errexp = this.generateErrorCreate(cp.sinfo, resulttype);
            return bindexp.bind(new smt_exp_1.SMTCond(testexp, smt_exp_1.SMTFreeVar.generate(), errexp));
        }
    }
    generateMIRConstructorPrimaryCollectionEmpty(cpce) {
        const cpcetype = this.typegen.getMIRType(cpce.tkey);
        if (this.typegen.isListType(cpcetype)) {
            return new smt_exp_1.SMTLet(this.varToSMTName(cpce.trgt), new smt_exp_1.SMTValue("(cons@bsqlist 0 bsqlist_data_array_empty)"));
        }
        else {
            return new smt_exp_1.SMTLet(this.varToSMTName(cpce.trgt), new smt_exp_1.SMTValue("(cons@bsqkvcontainer 0 cons@bsqkeylist$none bsqkvp_array_empty)"));
        }
    }
    generateMIRConstructorPrimaryCollectionSingletons(cpcs) {
        const cpcstype = this.typegen.getMIRType(cpcs.tkey);
        if (this.typegen.isListType(cpcstype)) {
            let consv = "bsqlist_data_array_empty";
            for (let i = 0; i < cpcs.args.length; ++i) {
                consv = `(store ${consv} ${i} ${this.argToSMT(cpcs.args[i], this.typegen.anyType).emit()})`;
            }
            return new smt_exp_1.SMTLet(this.varToSMTName(cpcs.trgt), new smt_exp_1.SMTValue(`(cons@bsqlist ${cpcs.args.length} ${consv})`));
        }
        else if (this.typegen.isSetType(cpcstype)) {
            const invname = mir_emitter_1.MIRKeyGenerator.generateStaticKey_MIR(this.typegen.assembly.entityDecls.get(cpcs.tkey), "_cons_insert");
            const vtype = this.typegen.assembly.entityDecls.get(cpcs.tkey).terms.get("T");
            let conscall = `(cons@bsqkvcontainer 0 cons@bsqkeylist$none bsqkvp_array_empty)`;
            for (let i = 0; i < cpcs.args.length; ++i) {
                conscall = `(result_success_value@bsqkvcontainer (${this.invokenameToSMT(invname)} ${conscall} ${this.argToSMT(cpcs.args[i], vtype).emit()}))`;
            }
            return new smt_exp_1.SMTLet(this.varToSMTName(cpcs.trgt), new smt_exp_1.SMTValue(conscall));
        }
        else {
            const invname = mir_emitter_1.MIRKeyGenerator.generateStaticKey_MIR(this.typegen.assembly.entityDecls.get(cpcs.tkey), "_cons_insert");
            const ktype = this.typegen.assembly.entityDecls.get(cpcs.tkey).terms.get("K");
            const vtype = this.typegen.assembly.entityDecls.get(cpcs.tkey).terms.get("V");
            const ttype = mir_assembly_1.MIRType.createSingle(mir_assembly_1.MIRTupleType.create([new mir_assembly_1.MIRTupleTypeEntry(ktype, false), new mir_assembly_1.MIRTupleTypeEntry(vtype, false)]));
            let conscall = "(cons@bsqkvcontainer 0 cons@bsqkeylist$none bsqkvp_array_empty)";
            for (let i = 0; i < cpcs.args.length; ++i) {
                conscall = `(result_success_value@bsqkvcontainer (${this.invokenameToSMT(invname)} ${conscall} ${this.argToSMT(cpcs.args[i], ttype).emit()}))`;
            }
            return new smt_exp_1.SMTLet(this.varToSMTName(cpcs.trgt), new smt_exp_1.SMTValue(conscall));
        }
    }
    generateMIRConstructorTuple(op) {
        const tcons = this.typegen.generateTupleConstructor(this.typegen.getMIRType(op.resultTupleType));
        if (tcons === "bsqtuple_0@cons") {
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue("bsqtuple_0@cons"));
        }
        else {
            const argl = op.args.map((arg) => this.argToSMT(arg, this.typegen.anyType).emit());
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(${tcons} ${argl.join(" ")})`));
        }
    }
    generateMIRConstructorRecord(op) {
        const tcons = this.typegen.generateRecordConstructor(this.typegen.getMIRType(op.resultRecordType));
        if (tcons === "bsqrecord_empty@cons") {
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue("bsqrecord_empty@cons"));
        }
        else {
            const argl = op.args.map((arg) => this.argToSMT(arg[1], this.typegen.anyType).emit());
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTValue(`(${tcons} ${argl.join(" ")})`));
        }
    }
    generateMIRAccessFromIndex(op, resultAccessType) {
        const tuptype = this.getArgType(op.arg);
        if (this.typegen.isTupleType(tuptype)) {
            if (this.typegen.isKnownLayoutTupleType(tuptype)) {
                if (op.idx < smttype_emitter_1.SMTTypeEmitter.getKnownLayoutTupleType(tuptype).entries.length) {
                    return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(new smt_exp_1.SMTValue(`(${this.typegen.generateTupleAccessor(tuptype, op.idx)} ${this.argToSMT(op.arg, tuptype).emit()})`), this.typegen.anyType, resultAccessType));
                }
                else {
                    return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(new smt_exp_1.SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType));
                }
            }
            else {
                const tmax = smttype_emitter_1.SMTTypeEmitter.getTupleTypeMaxLength(tuptype);
                if (op.idx < tmax) {
                    const avalue = `(${this.typegen.generateTupleAccessor(tuptype, op.idx)} ${this.argToSMT(op.arg, tuptype).emit()})`;
                    const nval = this.typegen.coerce(new smt_exp_1.SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType);
                    const rval = this.typegen.coerce(new smt_exp_1.SMTValue(avalue), this.typegen.anyType, resultAccessType);
                    return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTCond(new smt_exp_1.SMTValue(`(is-bsqterm@clear ${avalue})`), nval, rval));
                }
                else {
                    return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(new smt_exp_1.SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType));
                }
            }
        }
        else {
            const avalue = `(select (bsqterm_tuple_entries ${this.argToSMT(op.arg, tuptype).emit()}) ${op.idx})`;
            if (!this.typegen.assembly.subtypeOf(this.typegen.noneType, resultAccessType)) {
                return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(new smt_exp_1.SMTValue(avalue), this.typegen.anyType, resultAccessType));
            }
            else {
                const nval = this.typegen.coerce(new smt_exp_1.SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType);
                const rval = this.typegen.coerce(new smt_exp_1.SMTValue(avalue), this.typegen.anyType, resultAccessType);
                return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTCond(new smt_exp_1.SMTValue(`(is-bsqterm@clear ${avalue})`), nval, rval));
            }
        }
    }
    generateMIRAccessFromProperty(op, resultAccessType) {
        const rectype = this.getArgType(op.arg);
        if (this.typegen.isRecordType(rectype)) {
            if (this.typegen.isKnownLayoutRecordType(rectype)) {
                if (smttype_emitter_1.SMTTypeEmitter.getKnownLayoutRecordType(rectype).entries.find((entry) => entry.name === op.property) !== undefined) {
                    return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(new smt_exp_1.SMTValue(`(${this.typegen.generateRecordAccessor(rectype, op.property)} ${this.argToSMT(op.arg, rectype).emit()})`), this.typegen.anyType, resultAccessType));
                }
                else {
                    return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(new smt_exp_1.SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType));
                }
            }
            else {
                const maxset = smttype_emitter_1.SMTTypeEmitter.getRecordTypeMaxPropertySet(rectype);
                if (maxset.includes(op.property)) {
                    const avalue = `(${this.typegen.generateRecordAccessor(rectype, op.property)} ${this.argToSMT(op.arg, rectype).emit()})`;
                    const nval = this.typegen.coerce(new smt_exp_1.SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType);
                    const rval = this.typegen.coerce(new smt_exp_1.SMTValue(avalue), this.typegen.anyType, resultAccessType);
                    return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTCond(new smt_exp_1.SMTValue(`(is-bsqterm@clear ${avalue})`), nval, rval));
                }
                else {
                    return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(new smt_exp_1.SMTValue("(bsqterm_key bsqkey_none)"), this.typegen.noneType, resultAccessType));
                }
            }
        }
        else {
            const avalue = `(select (bsqterm_record_entries ${this.argToSMT(op.arg, rectype).emit()}) "${op.property}")`;
            if (!this.typegen.assembly.subtypeOf(this.typegen.noneType, resultAccessType)) {
                return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(new smt_exp_1.SMTValue(avalue), this.typegen.anyType, resultAccessType));
            }
            else {
                const nval = this.typegen.coerce(new smt_exp_1.SMTValue("bsqkey_none"), this.typegen.noneType, resultAccessType);
                const rval = this.typegen.coerce(new smt_exp_1.SMTValue(avalue), this.typegen.anyType, resultAccessType);
                return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), new smt_exp_1.SMTCond(new smt_exp_1.SMTValue(`(is-bsqterm@clear ${avalue})`), nval, rval));
            }
        }
    }
    generateMIRAccessFromField(op, resultAccessType) {
        const argtype = this.getArgType(op.arg);
        const fdecl = this.assembly.fieldDecls.get(op.field);
        if (this.typegen.isUEntityType(argtype)) {
            const etype = smttype_emitter_1.SMTTypeEmitter.getUEntityType(argtype);
            const access = new smt_exp_1.SMTValue(`(${this.typegen.generateEntityAccessor(etype.ekey, op.field)} ${this.argToSMT(op.arg, argtype).emit()})`);
            return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(access, this.typegen.getMIRType(fdecl.declaredType), resultAccessType));
        }
        else {
            if (this.typegen.getMIRType(fdecl.enclosingDecl).options[0] instanceof mir_assembly_1.MIREntityType) {
                const etype = smttype_emitter_1.SMTTypeEmitter.getUEntityType(this.typegen.getMIRType(fdecl.enclosingDecl));
                const access = new smt_exp_1.SMTValue(`(${this.typegen.generateEntityAccessor(etype.ekey, op.field)} ${this.argToSMT(op.arg, this.typegen.getMIRType(fdecl.enclosingDecl)).emit()})`);
                return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(access, this.typegen.getMIRType(fdecl.declaredType), resultAccessType));
            }
            else {
                const access = new smt_exp_1.SMTValue(`(select (bsqterm_object_entries ${this.argToSMT(op.arg, this.typegen.anyType).emit()}) "${op.field}")`);
                return new smt_exp_1.SMTLet(this.varToSMTName(op.trgt), this.typegen.coerce(access, this.typegen.anyType, resultAccessType));
            }
        }
    }
    generateMIRInvokeFixedFunction(ivop, gas) {
        let vals = [];
        const idecl = (this.assembly.invokeDecls.get(ivop.mkey) || this.assembly.primitiveInvokeDecls.get(ivop.mkey));
        for (let i = 0; i < ivop.args.length; ++i) {
            vals.push(this.argToSMT(ivop.args[i], this.assembly.typeMap.get(idecl.params[i].type)).emit());
        }
        const tv = this.generateTempName();
        const ivrtype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(idecl.resultType));
        const resulttype = this.typegen.typeToSMTCategory(this.currentRType);
        const checkerror = new smt_exp_1.SMTValue(`(is-result_error@${ivrtype} ${tv})`);
        const extracterror = (ivrtype !== resulttype) ? new smt_exp_1.SMTValue(`(result_error@${resulttype} (result_error_code@${ivrtype} ${tv}))`) : new smt_exp_1.SMTValue(tv);
        const normalassign = new smt_exp_1.SMTLet(this.varToSMTName(ivop.trgt), new smt_exp_1.SMTValue(`(result_success_value@${ivrtype} ${tv})`));
        if (this.currentSCC === undefined || !this.currentSCC.has(ivop.mkey)) {
            const invokeexp = new smt_exp_1.SMTValue(vals.length !== 0 ? `(${this.invokenameToSMT(ivop.mkey)} ${vals.join(" ")})` : this.invokenameToSMT(ivop.mkey));
            return new smt_exp_1.SMTLet(tv, invokeexp, new smt_exp_1.SMTCond(checkerror, extracterror, normalassign));
        }
        else {
            if (gas === 0) {
                const invokeexp = this.generateBMCLimitCreate(ivop.mkey, ivrtype);
                return new smt_exp_1.SMTLet(tv, invokeexp, new smt_exp_1.SMTCond(checkerror, extracterror, normalassign));
            }
            else {
                const invokeexp = new smt_exp_1.SMTValue(vals.length !== 0 ? `(${this.invokenameToSMT(ivop.mkey)}@gas${gas} ${vals.join(" ")})` : this.invokenameToSMT(ivop.mkey));
                return new smt_exp_1.SMTLet(tv, invokeexp, new smt_exp_1.SMTCond(checkerror, extracterror, normalassign));
            }
        }
    }
    generateEquals(op, lhsinfertype, lhs, rhsinfertype, rhs) {
        const lhsargtype = this.getArgType(lhs);
        const rhsargtype = this.getArgType(rhs);
        let coreop = "";
        if (lhsinfertype.trkey === "NSCore::Bool" && rhsinfertype.trkey === "NSCore::Bool") {
            const lhsbool = (lhsargtype.trkey === "NSCore::Bool") ? this.argToSMT(lhs, lhsargtype).emit() : this.argToSMT(lhs, lhsinfertype).emit();
            const rhsbool = (rhsargtype.trkey === "NSCore::Bool") ? this.argToSMT(rhs, rhsargtype).emit() : this.argToSMT(rhs, rhsinfertype).emit();
            coreop = `(= ${lhsbool} ${rhsbool})`;
        }
        else if (lhsinfertype.trkey === "NSCore::Int" && rhsinfertype.trkey === "NSCore::Int") {
            const lhsint = (lhsargtype.trkey === "NSCore::Int") ? this.argToSMT(lhs, lhsargtype).emit() : this.argToSMT(lhs, lhsinfertype).emit();
            const rhsint = (rhsargtype.trkey === "NSCore::Int") ? this.argToSMT(rhs, rhsargtype).emit() : this.argToSMT(rhs, rhsinfertype).emit();
            coreop = `(= ${lhsint} ${rhsint})`;
        }
        else if (lhsinfertype.trkey === "NSCore::String" && rhsinfertype.trkey === "NSCore::String") {
            const lhsstring = (lhsargtype.trkey === "NSCore::String") ? this.argToSMT(lhs, lhsargtype).emit() : this.argToSMT(lhs, lhsinfertype).emit();
            const rhsstring = (rhsargtype.trkey === "NSCore::String") ? this.argToSMT(rhs, rhsargtype).emit() : this.argToSMT(rhs, rhsinfertype).emit();
            coreop = `(= ${lhsstring} ${rhsstring})`;
        }
        else if (lhsargtype.trkey === rhsargtype.trkey) {
            coreop = `(= ${this.argToSMT(lhs, lhsargtype).emit()} ${this.argToSMT(rhs, rhsargtype).emit()})`;
        }
        else {
            coreop = `(= ${this.argToSMT(lhs, this.typegen.keyType).emit()} ${this.argToSMT(rhs, this.typegen.keyType).emit()})`;
        }
        return op === "!=" ? `(not ${coreop})` : coreop;
    }
    generateCompare(op, lhsinfertype, lhs, rhsinfertype, rhs) {
        const lhsargtype = this.getArgType(lhs);
        const rhsargtype = this.getArgType(rhs);
        const lhsint = (lhsargtype.trkey === "NSCore::Int") ? this.argToSMT(lhs, lhsargtype).emit() : this.argToSMT(lhs, lhsinfertype).emit();
        const rhsint = (rhsargtype.trkey === "NSCore::Int") ? this.argToSMT(rhs, rhsargtype).emit() : this.argToSMT(rhs, rhsinfertype).emit();
        return `(${op} ${lhsint} ${rhsint})`;
    }
    generateSubtypeTupleCheck(argv, argt, accessor_macro, has_macro, argtype, oftype, gas) {
        const subtypesig = `(@subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}@gas${gas} ((atuple ${argt})) Bool`;
        if (this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let reqlen = oftype.entries.findIndex((entry) => entry.isOptional);
            if (reqlen === -1) {
                reqlen = oftype.entries.length;
            }
            let checks = [];
            const maxlength = smttype_emitter_1.SMTTypeEmitter.getTupleTypeMaxLength(argtype);
            checks.push(`(not (< ${maxlength} ${reqlen}))`);
            for (let i = 0; i < oftype.entries.length; ++i) {
                if (!oftype.entries[i].isOptional) {
                    if (!(this.typegen.isKnownLayoutTupleType(argtype) && this.typegen.assembly.subtypeOf(smttype_emitter_1.SMTTypeEmitter.getKnownLayoutTupleType(argtype).entries[i].type, oftype.entries[i].type))) {
                        checks.push(this.generateTypeCheck(`${accessor_macro.replace("ARG", "atuple").replace("IDX", i.toString())}`, this.typegen.anyType, oftype.entries[i].type, true, gas - 1));
                    }
                }
                else {
                    if (maxlength <= i) {
                        const chk = this.generateTypeCheck(`${accessor_macro.replace("ARG", "atuple").replace("IDX", i.toString())}`, this.typegen.anyType, oftype.entries[i].type, true, gas - 1);
                        checks.push(`(or (not ${has_macro.replace("ARG", "atuple").replace("IDX", i.toString())}) ${chk})`);
                    }
                }
            }
            if (maxlength > oftype.entries.length) {
                for (let i = oftype.entries.length; i < maxlength; ++i) {
                    checks.push(`(not ${has_macro.replace("ARG", "atuple").replace("IDX", i.toString())})`);
                }
            }
            let op = "";
            if (checks.includes("false")) {
                op = "false";
            }
            else {
                checks = checks.filter((chk) => chk !== "true");
                if (checks.length === 0) {
                    op = "true";
                }
                else if (checks.length === 1) {
                    op = checks[0];
                }
                else {
                    op = `(and ${checks.join(" ")})`;
                }
            }
            const decl = subtypesig
                + "\n  " + op;
            +")\n";
            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }
        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}@gas${gas} ${argv})`;
    }
    generateSubtypeRecordCheck(argv, argt, accessor_macro, has_macro, argtype, oftype, gas) {
        const subtypesig = `bool subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}@gas${gas} ((arecord ${argt})) Bool`;
        if (this.subtypeFMap.has(subtypesig)) {
            const order = this.subtypeOrderCtr++;
            let checks = [];
            for (let i = 0; i < oftype.entries.length; ++i) {
                const pname = oftype.entries[i].name;
                if (!oftype.entries[i].isOptional) {
                    if (!(this.typegen.isKnownLayoutRecordType(argtype) && this.typegen.assembly.subtypeOf(smttype_emitter_1.SMTTypeEmitter.getKnownLayoutRecordType(argtype).entries.find((e) => e.name === pname).type, oftype.entries[i].type))) {
                        checks.push(this.generateTypeCheck(`${accessor_macro.replace("ARG", "arecord").replace("PNAME", pname)}`, this.typegen.anyType, oftype.entries[i].type, true, gas - 1));
                    }
                }
                else {
                    const chk = this.generateTypeCheck(`${accessor_macro.replace("ARG", "arecord").replace("PNAME", pname)}`, this.typegen.anyType, oftype.entries[i].type, true, gas - 1);
                    checks.push(`(or (not${has_macro.replace("ARG", "arecord").replace("PNAME", pname)}) ${chk})`);
                }
            }
            const possibleargproperties = smttype_emitter_1.SMTTypeEmitter.getRecordTypeMaxPropertySet(argtype);
            for (let i = 0; i < possibleargproperties.length; ++i) {
                const pname = possibleargproperties[i];
                if (oftype.entries.find((p) => p.name === pname) === undefined) {
                    checks.push(`(not ${has_macro.replace("ARG", "arecord").replace("PNAME", pname)})`);
                }
            }
            let op = "";
            if (checks.includes("false")) {
                op = "false";
            }
            else {
                checks = checks.filter((chk) => chk !== "true");
                if (checks.length === 0) {
                    op = "true";
                }
                else if (checks.length === 1) {
                    op = checks[0];
                }
                else {
                    op = `(and ${checks.join(" ")})`;
                }
            }
            const decl = subtypesig
                + "\n  " + op;
            +")\n";
            this.subtypeFMap.set(subtypesig, { order: order, decl: decl });
        }
        return `(subtypeFROM_${this.typegen.mangleStringForSMT(argtype.trkey)}_TO_${this.typegen.mangleStringForSMT(oftype.trkey)}@gas${gas} ${argv})`;
    }
    generateFastTupleTypeCheck(arg, argtype, oftype, inline, gas) {
        if (this.typegen.isSimpleBoolType(argtype) || this.typegen.isSimpleIntType(argtype) || this.typegen.isSimpleStringType(argtype) || this.typegen.isKeyType(argtype)) {
            return "false";
        }
        if (this.typegen.isTupleType(argtype)) {
            if (this.typegen.isKnownLayoutTupleType(argtype)) {
                const atuple = smttype_emitter_1.SMTTypeEmitter.getKnownLayoutTupleType(argtype);
                if (atuple.entries.length === 0) {
                    return "true";
                }
                else if (oftype.entries.length < atuple.entries.length) {
                    return "false";
                }
                else if (oftype.entries.length > atuple.entries.length && !oftype.entries[atuple.entries.length].isOptional) {
                    return "false";
                }
                else {
                    if (inline) {
                        let ttests = atuple.entries.map((entry, i) => this.generateTypeCheck(`(${this.typegen.generateTupleAccessor(argtype, i)} ${arg})`, this.typegen.anyType, entry.type, false, gas));
                        if (ttests.includes("false")) {
                            return "false";
                        }
                        else {
                            ttests = ttests.filter((chk) => chk !== "true");
                            if (ttests.length === 0) {
                                return "true";
                            }
                            else if (ttests.length === 1) {
                                return ttests[0];
                            }
                            else {
                                return `(and ${ttests.join(" ")})`;
                            }
                        }
                    }
                    else {
                        return this.generateSubtypeTupleCheck(arg, this.typegen.typeToSMTCategory(argtype), `(bsqtuple_${smttype_emitter_1.SMTTypeEmitter.getTupleTypeMaxLength(argtype)}@IDX ARG)`, `(is-bsqterm@clear  (bsqtuple_${smttype_emitter_1.SMTTypeEmitter.getTupleTypeMaxLength(argtype)}@IDX ARG))`, argtype, oftype, gas);
                    }
                }
            }
            else {
                return this.generateSubtypeTupleCheck(arg, this.typegen.typeToSMTCategory(argtype), `(bsqtuple_${smttype_emitter_1.SMTTypeEmitter.getTupleTypeMaxLength(argtype)}@IDX ARG)`, `(is-bsqterm@clear  (bsqtuple_${smttype_emitter_1.SMTTypeEmitter.getTupleTypeMaxLength(argtype)}@IDX ARG))`, argtype, oftype, gas);
            }
        }
        else if (this.typegen.isRecordType(argtype) || this.typegen.isUEntityType(argtype)) {
            return "false";
        }
        else {
            assert(this.typegen.typeToSMTCategory(argtype) === "BTerm");
            const tsc = this.generateSubtypeTupleCheck(`(bsqterm_tuple_entries ${arg})`, "BTerm", "(select ARG IDX)", "(is-bsqterm@clear (select ARG IDX))", argtype, oftype, gas);
            return `(and (is-bsqterm_tuple ${arg}) ${tsc})`;
        }
    }
    generateFastRecordTypeCheck(arg, argtype, oftype, inline, gas) {
        if (this.typegen.isSimpleBoolType(argtype) || this.typegen.isSimpleIntType(argtype) || this.typegen.isSimpleStringType(argtype) || this.typegen.isKeyType(argtype) || this.typegen.isTupleType(argtype)) {
            return "false";
        }
        else if (this.typegen.isRecordType(argtype)) {
            if (this.typegen.isKnownLayoutRecordType(argtype)) {
                const arecord = smttype_emitter_1.SMTTypeEmitter.getKnownLayoutRecordType(argtype);
                if (arecord.entries.length === 0) {
                    return "true";
                }
                else if (arecord.entries.some((entry) => oftype.entries.find((oe) => entry.name === oe.name) === undefined)) {
                    return "false";
                }
                else if (oftype.entries.some((entry) => !entry.isOptional && arecord.entries.find((ae) => entry.name === ae.name) === undefined)) {
                    return "false";
                }
                else {
                    if (inline) {
                        let ttests = arecord.entries.map((entry) => {
                            const ofentry = oftype.entries.find((oe) => oe.name === entry.name);
                            return this.generateTypeCheck(`(${this.typegen.generateRecordAccessor(argtype, entry.name)} ${arg})`, this.typegen.anyType, ofentry.type, false, gas);
                        });
                        if (ttests.includes("false")) {
                            return "false";
                        }
                        else {
                            ttests = ttests.filter((chk) => chk !== "true");
                            if (ttests.length === 0) {
                                return "true";
                            }
                            else if (ttests.length === 1) {
                                return ttests[0];
                            }
                            else {
                                return `(and ${ttests.join(" ")})`;
                            }
                        }
                    }
                    else {
                        return this.generateSubtypeRecordCheck(arg, this.typegen.typeToSMTCategory(argtype), `(bsqrecord_${this.typegen.generateRecordTypePropertyName(argtype)}@PNAME ARG)`, `(is-bsqterm@clear  (bsqrecord_${this.typegen.generateRecordTypePropertyName(argtype)}@PNAME ARG))`, argtype, oftype, gas);
                    }
                }
            }
            else {
                return this.generateSubtypeRecordCheck(arg, this.typegen.typeToSMTCategory(argtype), `(bsqrecord_${this.typegen.generateRecordTypePropertyName(argtype)}@PNAME ARG)`, `(is-bsqterm@clear  (bsqrecord_${this.typegen.generateRecordTypePropertyName(argtype)}@PNAME ARG))`, argtype, oftype, gas);
            }
        }
        else {
            assert(this.typegen.typeToSMTCategory(argtype) === "BTerm");
            const tsc = this.generateSubtypeTupleCheck(`(bsqterm_record_entries ${arg})`, "BTerm", "(select ARG PNAME)", "(is-bsqterm@clear (select ARG PNAME))", argtype, oftype, gas);
            return `(and (is-bsqterm_record ${arg}) ${tsc})`;
        }
    }
    generateFastEntityTypeCheck(arg, argtype, oftype) {
        if (this.typegen.isSimpleBoolType(argtype) || this.typegen.isSimpleIntType(argtype) || this.typegen.isSimpleStringType(argtype)) {
            return argtype.options[0].trkey === oftype.trkey ? "true" : "false";
        }
        else if (this.typegen.isKeyType(argtype)) {
            const ofdecl = this.typegen.assembly.entityDecls.get(oftype.ekey);
            if (oftype.ekey === "NSCore::None") {
                return `(= ${arg} bsqkey_none)`;
            }
            else if (oftype.ekey === "NSCore::Bool") {
                return `(is-bsqkey_bool ${arg})`;
            }
            else if (oftype.ekey === "NSCore::Int") {
                return `(is-bsqkey_int ${arg})`;
            }
            else if (oftype.ekey === "NSCore::String") {
                return `(is-bsqkey_string ${arg})`;
            }
            else if (oftype.ekey.startsWith("NSCore::StringOf<")) {
                return `(and (is-bsqkey_typedstring ${arg}) (= (bsqkey_typedstring_type ${arg}) ${this.typegen.mangleStringForSMT(oftype.ekey)}))`;
            }
            else if (oftype.ekey === "NSCore::GUID") {
                return `(is-bsqkey_guid ${arg})`;
            }
            else if (ofdecl.provides.includes("NSCore::Enum")) {
                return `(and (is-bsqkey_enum ${arg}) (= (bsqkey_enum_type ${arg}) ${this.typegen.mangleStringForSMT(oftype.ekey)}))`;
            }
            else if (ofdecl.provides.includes("NSCore::IdKey")) {
                return `(and (is-bsqkey_idkey ${arg}) (= (bsqkey_idkey_type ${arg}) ${this.typegen.mangleStringForSMT(oftype.ekey)}))`;
            }
            else {
                return "false";
            }
        }
        else if (this.typegen.isTupleType(argtype) || this.typegen.isRecordType(argtype)) {
            return "false";
        }
        else if (this.typegen.isUEntityType(argtype)) {
            if (oftype.ekey === "NSCore::None") {
                return `(is-${this.typegen.generateEntityNoneConstructor(smttype_emitter_1.SMTTypeEmitter.getUEntityType(argtype).ekey)} ${arg})`;
            }
            else {
                return `(is-${this.typegen.generateEntityConstructor(oftype.ekey)} ${arg})`;
            }
        }
        else {
            assert(this.typegen.typeToSMTCategory(argtype) === "BTerm");
            const ofdecl = this.typegen.assembly.entityDecls.get(oftype.ekey);
            if (oftype.ekey === "NSCore::None") {
                return `(= (bsqterm_key bsqkey_none) ${arg})`;
            }
            else if (oftype.ekey === "NSCore::Bool") {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_bool (bsqterm_key_value ${arg})))`;
            }
            else if (oftype.ekey === "NSCore::Int") {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_int (bsqterm_key_value ${arg})))`;
            }
            else if (oftype.ekey === "NSCore::String") {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_string (bsqterm_key_value ${arg})))`;
            }
            else if (oftype.ekey.startsWith("NSCore::StringOf<")) {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_typedstring (bsqterm_key_value ${arg})) (= (bsqkey_typedstring_type (bsqterm_key_value ${arg})) "${this.typegen.mangleStringForSMT(oftype.ekey)}"))`;
            }
            else if (oftype.ekey.startsWith("NSCore::POBBuffer<")) {
                return `(and (is-bsqterm_podbuffer ${arg}) (= (bsqterm_podbuffer_type ${arg}) ${this.typegen.mangleStringForSMT(oftype.ekey)}))`;
            }
            else if (oftype.ekey === "NSCore::GUID") {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_guid (bsqterm_key_value ${arg})))`;
            }
            else if (ofdecl.provides.includes("NSCore::Enum")) {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_enum (bsqterm_key_value ${arg})) (= (bsqkey_enum_type (bsqterm_key_value ${arg})) "${this.typegen.mangleStringForSMT(oftype.ekey)}"))`;
            }
            else if (ofdecl.provides.includes("NSCore::IdKey")) {
                return `(and (is-bsqterm_key ${arg}) (is-bsqkey_idkey (bsqterm_key_value ${arg})) (= (bsqkey_idkey_type (bsqterm_key_value ${arg})) "${this.typegen.mangleStringForSMT(oftype.ekey)}"))`;
            }
            else if (oftype.ekey === "NSCore::Regex") {
                return `(is-bsqterm_regex ${arg})`;
            }
            else {
                if (oftype.ekey.startsWith("NSCore::List<")) {
                    return `(and (is-bsqterm_list ${arg}) (= (bsqterm_list_type ${arg}) "${oftype.ekey}"))`;
                }
                else if (oftype.ekey.startsWith("NSCore::Set<") || oftype.ekey.startsWith("NSCore::Map<")) {
                    return `(and (is-bsqterm_kvcontainer ${arg}) (= (bsqterm_kvcontainer_type ${arg}) "${oftype.ekey}"))`;
                }
                else {
                    return `(and (is-bsqterm_object ${arg}) (= (bsqterm_object_type ${arg}) "${oftype.ekey}"))`;
                }
            }
        }
    }
    generateFastConceptTypeCheck(arg, argtype, oftype) {
        let tests = [];
        //
        //TODO: should flip this were we can lookup the possible entity->concept[] subtype relations and check inclusion of oftype in them
        //
        if (oftype.trkey === "NSCore::Any") {
            tests.push("true");
        }
        else if (oftype.trkey === "NSCore::Some") {
            if (this.typegen.isSimpleBoolType(argtype) || this.typegen.isSimpleIntType(argtype) || this.typegen.isSimpleStringType(argtype) || this.typegen.isTupleType(argtype) || this.typegen.isRecordType(argtype)) {
                tests.push("true");
            }
            else if (this.typegen.isUEntityType(argtype)) {
                if (this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype)) {
                    tests.push(`(is-${this.typegen.generateEntityConstructor(smttype_emitter_1.SMTTypeEmitter.getUEntityType(argtype).ekey)} ${arg})`);
                }
            }
            else {
                tests.push(`(not (= ${arg} (bsqterm_key bsqkey_none)))`);
            }
        }
        else if (this.typegen.isSimpleBoolType(argtype) || this.typegen.isSimpleIntType(argtype) || this.typegen.isSimpleStringType(argtype)) {
            tests.push(...[this.typegen.boolType, this.typegen.intType, this.typegen.stringType].map((spe) => this.generateFastEntityTypeCheck(arg, argtype, spe.options[0])));
        }
        else if (this.typegen.isTupleType(argtype)) {
            tests.push(this.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Tuple"), this.typegen.getMIRType(oftype.trkey)) ? "true" : "false");
        }
        else if (this.typegen.isRecordType(argtype)) {
            tests.push(this.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Record"), this.typegen.getMIRType(oftype.trkey)) ? "true" : "false");
        }
        else if (this.typegen.isUEntityType(argtype)) {
            if (this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype) && this.typegen.assembly.subtypeOf(this.typegen.noneType, this.typegen.getMIRType(oftype.trkey))) {
                tests.push(`(is-${this.typegen.generateEntityNoneConstructor(smttype_emitter_1.SMTTypeEmitter.getUEntityType(argtype).ekey)} ${arg})`);
            }
            else {
                const nonesafe = this.typegen.assembly.subtypeOf(this.typegen.noneType, argtype) ? `and (not (is-${this.typegen.generateEntityNoneConstructor(smttype_emitter_1.SMTTypeEmitter.getUEntityType(argtype).ekey)} ${arg})) ` : "";
                tests.push(`(${nonesafe}($select MIRConceptSubtypeArray__${this.typegen.mangleStringForSMT(oftype.trkey)} "${this.typegen.mangleStringForSMT(smttype_emitter_1.SMTTypeEmitter.getUEntityType(argtype).ekey)}"))`);
            }
        }
        else {
            assert(this.typegen.typeToSMTCategory(argtype) === "BTerm");
            let allspecialentities = [];
            this.typegen.assembly.entityDecls.forEach((etd) => {
                if (this.typegen.isSpecialRepType(etd) && oftype.ckeys.every((ct) => this.assembly.subtypeOf(this.typegen.getMIRType(etd.tkey), this.typegen.getMIRType(ct)))) {
                    allspecialentities.push(this.typegen.getMIRType(etd.tkey).options[0]);
                }
            });
            if (allspecialentities.find((stype) => stype.ekey === "NSCore::None") !== undefined) {
                tests.push(this.generateFastEntityTypeCheck(arg, argtype, allspecialentities.find((stype) => stype.trkey === "NSCore::None")));
            }
            if (allspecialentities.find((stype) => stype.ekey === "NSCore::Bool") !== undefined) {
                tests.push(this.generateFastEntityTypeCheck(arg, argtype, allspecialentities.find((stype) => stype.trkey === "NSCore::Bool")));
            }
            if (allspecialentities.find((stype) => stype.ekey === "NSCore::Int") !== undefined) {
                tests.push(this.generateFastEntityTypeCheck(arg, argtype, allspecialentities.find((stype) => stype.trkey === "NSCore::Int")));
            }
            if (allspecialentities.find((stype) => stype.ekey === "NSCore::String") !== undefined) {
                tests.push(this.generateFastEntityTypeCheck(arg, argtype, allspecialentities.find((stype) => stype.trkey === "NSCore::String")));
            }
            if (allspecialentities.find((stype) => stype.ekey.startsWith("NSCore::StringOf<")) !== undefined) {
                tests.push(`(is-bsqterm_typedstring ${arg})`);
            }
            if (allspecialentities.find((stype) => stype.ekey.startsWith("NSCore::POBBuffer<")) !== undefined) {
                tests.push(`(is-bsqterm_podbuffer ${arg})`);
            }
            if (allspecialentities.find((stype) => stype.ekey === "NSCore::GUID") !== undefined) {
                tests.push(this.generateFastEntityTypeCheck(arg, argtype, allspecialentities.find((stype) => stype.trkey === "NSCore::GUID")));
            }
            if (allspecialentities.find((stype) => this.assembly.entityDecls.get(stype.ekey).provides.includes("NSCore::Enum")) !== undefined) {
                tests.push(`(is-bsqterm_enum ${arg})`);
            }
            if (allspecialentities.find((stype) => this.assembly.entityDecls.get(stype.ekey).provides.includes("NSCore::IdKey")) !== undefined) {
                tests.push(`(is-bsqterm_idkey ${arg})`);
            }
            if (allspecialentities.find((stype) => stype.ekey === "NSCore::Regex") !== undefined) {
                tests.push(this.generateFastEntityTypeCheck(arg, argtype, allspecialentities.find((stype) => stype.trkey === "NSCore::Regex")));
            }
            if (this.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Tuple"), this.typegen.getMIRType(oftype.trkey))) {
                tests.push(`(is-bsqterm_tuple ${arg})`);
            }
            if (this.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Record"), this.typegen.getMIRType(oftype.trkey))) {
                tests.push(`(is-bsqterm_record ${arg})`);
            }
            //TODO: podX
            if (this.assembly.subtypeOf(this.typegen.getMIRType("NSCore::Object"), this.typegen.getMIRType(oftype.trkey))) {
                //
                //TODO: should handle List, Set, Map here
                //
                tests.push(`(is-bsqterm_object ${arg})`);
            }
            else {
                //
                //TODO: should handle List, Set, Map here
                //
                tests.push(`(and (is-bsqterm_object ${arg}) (select MIRConceptSubtypeArray__${this.typegen.mangleStringForSMT(oftype.trkey)} (bsqterm_object_type ${arg})))`);
            }
        }
        tests = tests.filter((t) => t !== "false");
        if (tests.includes("true")) {
            return "true";
        }
        else if (tests.length === 0) {
            return "false";
        }
        else if (tests.length === 1) {
            return tests[0];
        }
        else {
            return `(or ${tests.join(" ")})`;
        }
    }
    generateTypeCheck(arg, argtype, oftype, inline, gas) {
        if (this.typegen.assembly.subtypeOf(argtype, oftype)) {
            return "true";
        }
        const tests = oftype.options.map((topt) => {
            const mtype = this.typegen.getMIRType(topt.trkey);
            assert(mtype !== undefined, "We should generate all the component types by default??");
            if (topt instanceof mir_assembly_1.MIREntityType) {
                return this.generateFastEntityTypeCheck(arg, argtype, topt);
            }
            else if (topt instanceof mir_assembly_1.MIRConceptType) {
                return this.generateFastConceptTypeCheck(arg, argtype, topt);
            }
            else if (topt instanceof mir_assembly_1.MIRTupleType) {
                return this.generateFastTupleTypeCheck(arg, argtype, topt, inline, gas);
            }
            else {
                assert(topt instanceof mir_assembly_1.MIRRecordType);
                return this.generateFastRecordTypeCheck(arg, argtype, topt, inline, gas);
            }
        })
            .filter((test) => test !== "false");
        if (tests.includes("true") || tests.length === 0) {
            return "true";
        }
        else {
            return `(or ${tests.join(" ")})`;
        }
    }
    generateStmt(op, fromblck, gas) {
        switch (op.tag) {
            case mir_ops_1.MIROpTag.MIRLoadConst: {
                const lcv = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(lcv.trgt), this.generateConstantExp(lcv.src, this.getArgType(lcv.trgt)));
            }
            case mir_ops_1.MIROpTag.MIRLoadConstTypedString: {
                return NOT_IMPLEMENTED("MIRLoadConstTypedString");
            }
            case mir_ops_1.MIROpTag.MIRAccessConstantValue: {
                const acv = op;
                return this.generateAccessConstantValue(acv);
            }
            case mir_ops_1.MIROpTag.MIRLoadFieldDefaultValue: {
                const ldv = op;
                return this.generateLoadFieldDefaultValue(ldv);
            }
            case mir_ops_1.MIROpTag.MIRAccessArgVariable: {
                const lav = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(lav.trgt), this.argToSMT(lav.name, this.getArgType(lav.trgt)));
            }
            case mir_ops_1.MIROpTag.MIRAccessLocalVariable: {
                const llv = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(llv.trgt), this.argToSMT(llv.name, this.getArgType(llv.trgt)));
            }
            case mir_ops_1.MIROpTag.MIRConstructorPrimary: {
                const cp = op;
                return this.generateMIRConstructorPrimary(cp);
            }
            case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionEmpty: {
                const cpce = op;
                return this.generateMIRConstructorPrimaryCollectionEmpty(cpce);
            }
            case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                const cpcs = op;
                return this.generateMIRConstructorPrimaryCollectionSingletons(cpcs);
            }
            case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                return NOT_IMPLEMENTED("MIRConstructorPrimaryCollectionCopies");
            }
            case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                return NOT_IMPLEMENTED("MIRConstructorPrimaryCollectionMixed");
            }
            case mir_ops_1.MIROpTag.MIRConstructorTuple: {
                const tc = op;
                return this.generateMIRConstructorTuple(tc);
            }
            case mir_ops_1.MIROpTag.MIRConstructorRecord: {
                const tr = op;
                return this.generateMIRConstructorRecord(tr);
            }
            case mir_ops_1.MIROpTag.MIRAccessFromIndex: {
                const ai = op;
                return this.generateMIRAccessFromIndex(ai, this.typegen.getMIRType(ai.resultAccessType));
            }
            case mir_ops_1.MIROpTag.MIRProjectFromIndecies: {
                return NOT_IMPLEMENTED("MIRProjectFromIndecies");
            }
            case mir_ops_1.MIROpTag.MIRAccessFromProperty: {
                const ap = op;
                return this.generateMIRAccessFromProperty(ap, this.typegen.getMIRType(ap.resultAccessType));
            }
            case mir_ops_1.MIROpTag.MIRProjectFromProperties: {
                return NOT_IMPLEMENTED("MIRProjectFromProperties");
            }
            case mir_ops_1.MIROpTag.MIRAccessFromField: {
                const af = op;
                return this.generateMIRAccessFromField(af, this.typegen.getMIRType(af.resultAccessType));
            }
            case mir_ops_1.MIROpTag.MIRProjectFromFields: {
                return NOT_IMPLEMENTED("MIRProjectFromFields");
            }
            case mir_ops_1.MIROpTag.MIRProjectFromTypeTuple: {
                return NOT_IMPLEMENTED("MIRProjectFromTypeTuple");
            }
            case mir_ops_1.MIROpTag.MIRProjectFromTypeRecord: {
                return NOT_IMPLEMENTED("MIRProjectFromTypeRecord");
            }
            case mir_ops_1.MIROpTag.MIRProjectFromTypeConcept: {
                return NOT_IMPLEMENTED("MIRProjectFromTypeConcept");
            }
            case mir_ops_1.MIROpTag.MIRModifyWithIndecies: {
                return NOT_IMPLEMENTED("MIRModifyWithIndecies");
            }
            case mir_ops_1.MIROpTag.MIRModifyWithProperties: {
                return NOT_IMPLEMENTED("MIRModifyWithProperties");
            }
            case mir_ops_1.MIROpTag.MIRModifyWithFields: {
                return NOT_IMPLEMENTED("MIRModifyWithFields");
            }
            case mir_ops_1.MIROpTag.MIRStructuredExtendTuple: {
                return NOT_IMPLEMENTED("MIRStructuredExtendTuple");
            }
            case mir_ops_1.MIROpTag.MIRStructuredExtendRecord: {
                return NOT_IMPLEMENTED("MIRStructuredExtendRecord");
            }
            case mir_ops_1.MIROpTag.MIRStructuredExtendObject: {
                return NOT_IMPLEMENTED("MIRStructuredExtendObject");
            }
            case mir_ops_1.MIROpTag.MIRInvokeFixedFunction: {
                const invk = op;
                return this.generateMIRInvokeFixedFunction(invk, gas);
            }
            case mir_ops_1.MIROpTag.MIRInvokeVirtualTarget: {
                return NOT_IMPLEMENTED("MIRInvokeVirtualTarget");
            }
            case mir_ops_1.MIROpTag.MIRPrefixOp: {
                const pfx = op;
                if (pfx.op === "!") {
                    const tval = this.generateTruthyConvert(pfx.arg);
                    return new smt_exp_1.SMTLet(this.varToSMTName(pfx.trgt), new smt_exp_1.SMTValue(`(not ${tval.emit()})`));
                }
                else {
                    if (pfx.op === "-") {
                        if (pfx.arg instanceof mir_ops_1.MIRConstantInt) {
                            return new smt_exp_1.SMTLet(this.varToSMTName(pfx.trgt), new smt_exp_1.SMTValue(`-${pfx.arg.value}`));
                        }
                        else {
                            return new smt_exp_1.SMTLet(this.varToSMTName(pfx.trgt), new smt_exp_1.SMTValue(`(* -1 ${this.argToSMT(pfx.arg, this.typegen.intType).emit()})`));
                        }
                    }
                    else {
                        return new smt_exp_1.SMTLet(this.varToSMTName(pfx.trgt), this.argToSMT(pfx.arg, this.typegen.intType));
                    }
                }
            }
            case mir_ops_1.MIROpTag.MIRBinOp: {
                const bop = op;
                if (bop.op === "*") {
                    if (bop.rhs instanceof mir_ops_1.MIRConstantInt || bop.lhs instanceof mir_ops_1.MIRConstantInt) {
                        return new smt_exp_1.SMTLet(this.varToSMTName(bop.trgt), new smt_exp_1.SMTValue(`(* ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                    }
                    else {
                        return new smt_exp_1.SMTLet(this.varToSMTName(bop.trgt), new smt_exp_1.SMTValue(`(mult_op ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                    }
                }
                else if (bop.op === "/") {
                    if (bop.rhs instanceof mir_ops_1.MIRConstantInt || bop.lhs instanceof mir_ops_1.MIRConstantInt) {
                        const divres = new smt_exp_1.SMTLet(this.varToSMTName(bop.trgt), new smt_exp_1.SMTValue(`(/ ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                        return new smt_exp_1.SMTCond(new smt_exp_1.SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.typeToSMTCategory(this.currentRType)), divres);
                    }
                    else {
                        const divres = new smt_exp_1.SMTLet(this.varToSMTName(bop.trgt), new smt_exp_1.SMTValue(`(div_op ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                        return new smt_exp_1.SMTCond(new smt_exp_1.SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.typeToSMTCategory(this.currentRType)), divres);
                    }
                }
                else if (bop.op === "%") {
                    const modres = new smt_exp_1.SMTLet(this.varToSMTName(bop.trgt), new smt_exp_1.SMTValue(`(mod_op ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                    return new smt_exp_1.SMTCond(new smt_exp_1.SMTValue(`(= ${this.argToSMT(bop.rhs, this.typegen.intType).emit()} 0)`), this.generateErrorCreate(op.sinfo, this.typegen.typeToSMTCategory(this.currentRType)), modres);
                }
                else {
                    return new smt_exp_1.SMTLet(this.varToSMTName(bop.trgt), new smt_exp_1.SMTValue(`(${bop.op} ${this.argToSMT(bop.lhs, this.typegen.intType).emit()} ${this.argToSMT(bop.rhs, this.typegen.intType).emit()})`));
                }
            }
            case mir_ops_1.MIROpTag.MIRGetKey: {
                return NOT_IMPLEMENTED("MIRGetKey");
            }
            case mir_ops_1.MIROpTag.MIRBinEq: {
                const beq = op;
                const lhvtypeinfer = this.typegen.getMIRType(beq.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(beq.rhsInferType);
                return new smt_exp_1.SMTLet(this.varToSMTName(beq.trgt), new smt_exp_1.SMTValue(this.generateEquals(beq.op, lhvtypeinfer, beq.lhs, rhvtypeinfer, beq.rhs)));
            }
            case mir_ops_1.MIROpTag.MIRBinCmp: {
                const bcmp = op;
                const lhvtypeinfer = this.typegen.getMIRType(bcmp.lhsInferType);
                const rhvtypeinfer = this.typegen.getMIRType(bcmp.rhsInferType);
                return new smt_exp_1.SMTLet(this.varToSMTName(bcmp.trgt), new smt_exp_1.SMTValue(this.generateCompare(bcmp.op, lhvtypeinfer, bcmp.lhs, rhvtypeinfer, bcmp.rhs)));
            }
            case mir_ops_1.MIROpTag.MIRIsTypeOfNone: {
                const ton = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(ton.trgt), this.generateNoneCheck(ton.arg));
            }
            case mir_ops_1.MIROpTag.MIRIsTypeOfSome: {
                const tos = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(tos.trgt), new smt_exp_1.SMTValue(`(not ${this.generateNoneCheck(tos.arg).emit()})`));
            }
            case mir_ops_1.MIROpTag.MIRIsTypeOf: {
                const top = op;
                const oftype = this.typegen.getMIRType(top.oftype);
                const argtype = this.getArgType(top.arg);
                return new smt_exp_1.SMTLet(this.varToSMTName(top.trgt), new smt_exp_1.SMTValue(this.generateTypeCheck(this.argToSMT(top.arg, argtype).emit(), argtype, oftype, true, this.typecheckgas)));
            }
            case mir_ops_1.MIROpTag.MIRRegAssign: {
                const regop = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(regop.trgt), this.argToSMT(regop.src, this.getArgType(regop.trgt)));
            }
            case mir_ops_1.MIROpTag.MIRTruthyConvert: {
                const tcop = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(tcop.trgt), this.generateTruthyConvert(tcop.src));
            }
            case mir_ops_1.MIROpTag.MIRLogicStore: {
                const llop = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(llop.trgt), new smt_exp_1.SMTValue(`(${llop.op === "&" ? "and" : "or"} ${this.argToSMT(llop.lhs, this.typegen.boolType).emit()} ${this.argToSMT(llop.rhs, this.typegen.boolType).emit()})`));
            }
            case mir_ops_1.MIROpTag.MIRVarStore: {
                const vsop = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(vsop.name), this.argToSMT(vsop.src, this.getArgType(vsop.name)));
            }
            case mir_ops_1.MIROpTag.MIRReturnAssign: {
                const raop = op;
                return new smt_exp_1.SMTLet(this.varToSMTName(raop.name), this.argToSMT(raop.src, this.getArgType(raop.name)));
            }
            case mir_ops_1.MIROpTag.MIRAbort: {
                const aop = op;
                return this.generateErrorCreate(aop.sinfo, this.typegen.typeToSMTCategory(this.currentRType));
            }
            case mir_ops_1.MIROpTag.MIRDebug: {
                return undefined;
            }
            case mir_ops_1.MIROpTag.MIRJump: {
                return undefined;
            }
            case mir_ops_1.MIROpTag.MIRJumpCond: {
                const cjop = op;
                const smttest = this.generateTruthyConvert(cjop.arg);
                return new smt_exp_1.SMTCond(smttest, smt_exp_1.SMTFreeVar.generate("#true_trgt#"), smt_exp_1.SMTFreeVar.generate("#false_trgt#"));
            }
            case mir_ops_1.MIROpTag.MIRJumpNone: {
                const njop = op;
                return new smt_exp_1.SMTCond(this.generateNoneCheck(njop.arg), smt_exp_1.SMTFreeVar.generate("#true_trgt#"), smt_exp_1.SMTFreeVar.generate("#false_trgt#"));
            }
            case mir_ops_1.MIROpTag.MIRPhi: {
                const pop = op;
                const uvar = pop.src.get(fromblck);
                return new smt_exp_1.SMTLet(this.varToSMTName(pop.trgt), this.argToSMT(uvar, this.getArgType(pop.trgt)));
            }
            case mir_ops_1.MIROpTag.MIRVarLifetimeStart:
            case mir_ops_1.MIROpTag.MIRVarLifetimeEnd: {
                return undefined;
            }
            default: {
                return NOT_IMPLEMENTED(`Missing case ${op.tag}`);
            }
        }
    }
    generateBlockExps(block, fromblock, blocks, gas) {
        const exps = [];
        for (let i = 0; i < block.ops.length; ++i) {
            const exp = this.generateStmt(block.ops[i], fromblock, gas);
            if (exp !== undefined) {
                exps.push(exp);
            }
        }
        if (block.label === "exit") {
            const resulttype = this.typegen.typeToSMTCategory(this.currentRType);
            let rexp = new smt_exp_1.SMTValue(`(result_success@${resulttype} _return_)`);
            for (let i = exps.length - 1; i >= 0; --i) {
                rexp = exps[i].bind(rexp, "#body#");
            }
            return rexp;
        }
        else {
            const jop = block.ops[block.ops.length - 1];
            if (jop.tag === mir_ops_1.MIROpTag.MIRJump) {
                let rexp = this.generateBlockExps(blocks.get(jop.trgtblock), block.label, blocks, gas);
                for (let i = exps.length - 1; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }
                return rexp;
            }
            else {
                assert(jop.tag === mir_ops_1.MIROpTag.MIRJumpCond || jop.tag === mir_ops_1.MIROpTag.MIRJumpNone);
                let tblock = ((jop.tag === mir_ops_1.MIROpTag.MIRJumpCond) ? blocks.get(jop.trueblock) : blocks.get(jop.noneblock));
                let texp = this.generateBlockExps(tblock, block.label, blocks, gas);
                let fblock = ((jop.tag === mir_ops_1.MIROpTag.MIRJumpCond) ? blocks.get(jop.falseblock) : blocks.get(jop.someblock));
                let fexp = this.generateBlockExps(fblock, block.label, blocks, gas);
                let rexp = exps[exps.length - 1].bind(texp, "#true_trgt#").bind(fexp, "#false_trgt#");
                for (let i = exps.length - 2; i >= 0; --i) {
                    rexp = exps[i].bind(rexp, "#body#");
                }
                return rexp;
            }
        }
    }
    generateSMTInvoke(idecl, cscc, gas, gasdown) {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.getMIRType(idecl.resultType);
        this.currentSCC = cscc;
        let argvars = new Map();
        idecl.params.forEach((arg) => argvars.set(arg.name, this.assembly.typeMap.get(arg.type)));
        const args = idecl.params.map((arg) => `(${this.varNameToSMTName(arg.name)} ${this.typegen.typeToSMTCategory(this.typegen.getMIRType(arg.type))})`);
        const restype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(idecl.resultType));
        const decl = `(define-fun ${this.invokenameToSMT(idecl.key)}${gas !== undefined ? `@gas${gas}` : ""} (${args.join(" ")}) Result@${restype}`;
        if (idecl instanceof mir_assembly_1.MIRInvokeBodyDecl) {
            this.vtypes = new Map();
            idecl.body.vtypes.forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });
            const blocks = idecl.body.body;
            const body = this.generateBlockExps(blocks.get("entry"), "[NO PREVIOUS]", blocks, gasdown);
            if (idecl.preconditions.length === 0 && idecl.postconditions.length === 0) {
                return `${decl} \n${body.emit("  ")})`;
            }
            else {
                let cbody = body;
                if (idecl.postconditions.length !== 0) {
                    //
                    //TODO -- ref parms don't get expanded correctly here -- need to coordinate with def and call here
                    //
                    const tbody = this.generateTempName();
                    const postinvoke = this.invokenameToSMT(mir_emitter_1.MIRKeyGenerator.generateBodyKey("post", idecl.key));
                    const callpost = new smt_exp_1.SMTValue(`(${postinvoke} ${idecl.params.map((arg) => this.varNameToSMTName(arg.name)).join(" ")} (result_success_value@${restype} ${tbody}))`);
                    cbody = new smt_exp_1.SMTLet(tbody, new smt_exp_1.SMTValue(cbody.emit("  ")), new smt_exp_1.SMTCond(callpost, new smt_exp_1.SMTValue(tbody), this.generateErrorCreate(idecl.sourceLocation, restype)));
                }
                if (idecl.preconditions.length !== 0) {
                    const preinvoke = this.invokenameToSMT(mir_emitter_1.MIRKeyGenerator.generateBodyKey("pre", idecl.key));
                    const callpre = new smt_exp_1.SMTValue(idecl.params.length !== 0 ? `(${preinvoke} ${idecl.params.map((arg) => this.varNameToSMTName(arg.name)).join(" ")})` : preinvoke);
                    cbody = new smt_exp_1.SMTCond(callpre, cbody, this.generateErrorCreate(idecl.sourceLocation, restype));
                }
                return `${decl} \n${cbody.emit("  ")})`;
            }
        }
        else {
            assert(idecl instanceof mir_assembly_1.MIRInvokePrimitiveDecl);
            const params = idecl.params.map((arg) => this.varNameToSMTName(arg.name));
            return `${decl} \n  ${this.generateBuiltinBody(idecl, params).emit("  ")}\n)`;
        }
    }
    generateSMTPre(prekey, idecl) {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.boolType;
        const args = idecl.params.map((arg) => `(${this.varNameToSMTName(arg.name)} ${this.typegen.typeToSMTCategory(this.typegen.getMIRType(arg.type))})`);
        const decl = `(define-fun ${this.invokenameToSMT(prekey)} (${args.join(" ")}) Bool`;
        const decls = idecl.preconditions.map((pc, i) => {
            this.vtypes = new Map();
            pc[0].vtypes.forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });
            const blocksi = pc[0].body;
            const bodyi = this.generateBlockExps(blocksi.get("entry"), "[NO PREVIOUS]", blocksi, undefined);
            const decli = `(define-fun ${this.invokenameToSMT(prekey)}$${i} (${args.join(" ")}) Result@Bool \n${bodyi.emit("  ")})`;
            const calli = (`(${this.invokenameToSMT(prekey)}$${i} ${idecl.params.map((p) => this.varNameToSMTName(p.name)).join(" ")})`);
            return [decli, calli];
        });
        const declsand = decls.map((cc) => {
            const tv = `@tmpvarda@${this.tmpvarctr++}`;
            return new smt_exp_1.SMTLet(tv, new smt_exp_1.SMTValue(cc[1]), new smt_exp_1.SMTValue(`(and (is-result_success@Bool ${tv}) (result_success_value@Bool ${tv}))`)).emit();
        });
        const rbody = declsand.length === 1 ? declsand[0] : `(and ${declsand.join(" ")})`;
        return `${decls.map((cc) => cc[0]).join("\n")}\n\n${decl}\n${rbody}\n)\n`;
    }
    generateSMTPost(postkey, idecl) {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.boolType;
        const restype = this.typegen.getMIRType(idecl.resultType);
        const args = idecl.params.map((arg) => `(${this.varNameToSMTName(arg.name)} ${this.typegen.typeToSMTCategory(this.typegen.getMIRType(arg.type))})`);
        args.push(`(__result__ ${this.typegen.typeToSMTCategory(restype)})`);
        const decl = `(define-fun ${this.invokenameToSMT(postkey)} (${args.join(" ")}) Bool`;
        const decls = idecl.postconditions.map((pc, i) => {
            this.vtypes = new Map();
            pc.vtypes.forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });
            const blocksi = pc.body;
            const bodyi = this.generateBlockExps(blocksi.get("entry"), "[NO PREVIOUS]", blocksi, undefined);
            const decli = `(define-fun ${this.invokenameToSMT(postkey)}$${i} (${args.join(" ")}) Result@Bool \n${bodyi.emit("  ")})`;
            const calli = (`(${this.invokenameToSMT(postkey)}$${i} ${[idecl.params.map((p) => this.varNameToSMTName(p.name)), "__result__"].join(" ")})`);
            return [decli, calli];
        });
        const declsand = decls.map((cc) => {
            const tv = `@tmpvarda@${this.tmpvarctr++}`;
            return new smt_exp_1.SMTLet(tv, new smt_exp_1.SMTValue(cc[1]), new smt_exp_1.SMTValue(`(and (is-result_success@Bool ${tv}) (result_success_value@Bool ${tv}))`)).emit();
        });
        const rbody = declsand.length === 1 ? declsand[0] : `(and ${declsand.join(" ")})`;
        return `${decls.map((cc) => cc[0]).join("\n")}\n\n${decl}\n${rbody})\n`;
    }
    generateSMTInv(invkey, idecl) {
        this.currentFile = idecl.srcFile;
        this.currentRType = this.typegen.boolType;
        const args = `(${this.varNameToSMTName("this")} ${this.typegen.typeToSMTCategory(this.typegen.getMIRType(idecl.tkey))})`;
        const decl = `(define-fun ${this.invokenameToSMT(invkey)} (${args}) Bool`;
        const decls = idecl.invariants.map((pc, i) => {
            this.vtypes = new Map();
            pc.vtypes.forEach((tkey, name) => {
                this.vtypes.set(name, this.typegen.getMIRType(tkey));
            });
            const blocksi = pc.body;
            const bodyi = this.generateBlockExps(blocksi.get("entry"), "[NO PREVIOUS]", blocksi, undefined);
            const decli = `(define-fun ${this.invokenameToSMT(invkey)}$${i} (${args}) Result@Bool \n${bodyi.emit("  ")})`;
            const calli = (`(${this.invokenameToSMT(invkey)}$${i} ${this.varNameToSMTName("this")})`);
            return [decli, calli];
        });
        const declsand = decls.map((cc) => {
            const tv = `@tmpvarda@${this.tmpvarctr++}`;
            return new smt_exp_1.SMTLet(tv, new smt_exp_1.SMTValue(cc[1]), new smt_exp_1.SMTValue(`(and (is-result_success@Bool ${tv}) (result_success_value@Bool ${tv}))`)).emit();
        });
        const rbody = declsand.length === 1 ? declsand[0] : `(and ${declsand.join(" ")})`;
        return `${decls.map((cc) => cc[0]).join("\n")}\n\n${decl}\n${rbody})\n`;
    }
    generateSMTConst(constkey, cdecl) {
        this.currentFile = cdecl.srcFile;
        this.currentRType = this.typegen.getMIRType(cdecl.declaredType);
        if (SMTBodyEmitter.expBodyTrivialCheck(cdecl.value)) {
            return undefined;
        }
        this.vtypes = new Map();
        cdecl.value.vtypes.forEach((tkey, name) => {
            this.vtypes.set(name, this.typegen.getMIRType(tkey));
        });
        const restype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(cdecl.declaredType));
        const decl = `(define-fun ${this.invokenameToSMT(constkey)} () Result@${restype}`;
        const blocks = cdecl.value.body;
        const body = this.generateBlockExps(blocks.get("entry"), "[NO PREVIOUS]", blocks, undefined);
        return `${decl} \n${body.emit("  ")})`;
    }
    generateSMTFDefault(fdkey, fdecl) {
        this.currentFile = fdecl.srcFile;
        this.currentRType = this.typegen.getMIRType(fdecl.declaredType);
        if (SMTBodyEmitter.expBodyTrivialCheck(fdecl.value)) {
            return undefined;
        }
        this.vtypes = new Map();
        fdecl.value.vtypes.forEach((tkey, name) => {
            this.vtypes.set(name, this.typegen.getMIRType(tkey));
        });
        const restype = this.typegen.typeToSMTCategory(this.typegen.getMIRType(fdecl.declaredType));
        const decl = `(define-fun ${this.invokenameToSMT(fdkey)} () Result@${restype}`;
        const blocks = fdecl.value.body;
        const body = this.generateBlockExps(blocks.get("entry"), "[NO PREVIOUS]", blocks, undefined);
        return `${decl} \n${body.emit("  ")})`;
    }
    generateBuiltinBody(idecl, params) {
        const rtype = this.typegen.getMIRType(idecl.resultType);
        let bodyres = undefined;
        let autowrap = true;
        switch (idecl.implkey) {
            case "list_size": {
                bodyres = new smt_exp_1.SMTValue(`(bsqlist@size ${params[0]})`);
                break;
            }
            case "list_unsafe_at": {
                bodyres = this.typegen.coerce(new smt_exp_1.SMTValue(`(select (bsqlist@entries ${params[0]}) ${params[1]})`), this.typegen.anyType, rtype);
                break;
            }
            case "list_unsafe_add": {
                const storeval = this.typegen.coerce(new smt_exp_1.SMTValue(params[1]), this.typegen.getMIRType(idecl.params[1].type), this.typegen.anyType).emit();
                const idx = `(bsqlist@size ${params[0]})`;
                bodyres = new smt_exp_1.SMTValue(`(cons@bsqlist (+ (bsqlist@size ${params[0]}) 1) (store (bsqlist@entries ${params[0]}) ${idx} ${storeval}))`);
                break;
            }
            case "list_unsafe_set": {
                const storeval = this.typegen.coerce(new smt_exp_1.SMTValue(params[2]), this.typegen.getMIRType(idecl.params[2].type), this.typegen.anyType).emit();
                bodyres = new smt_exp_1.SMTValue(`(cons@bsqlist (bsqlist@size ${params[0]}) (store (bsqlist@entries ${params[0]}) ${params[1]} ${storeval}))`);
                break;
            }
            case "list_destructive_add": {
                const storeval = this.typegen.coerce(new smt_exp_1.SMTValue(params[1]), this.typegen.getMIRType(idecl.params[1].type), this.typegen.anyType).emit();
                bodyres = new smt_exp_1.SMTValue(`(cons@bsqlist (+ (bsqlist@size ${params[0]}) 1) (store (bsqlist@entries ${params[0]}) (bsqlist@size ${params[0]}) ${storeval}))`);
                break;
            }
            case "keylist_cons": {
                bodyres = new smt_exp_1.SMTValue(`(cons@bsqkeylist ${params[0]} ${params[1]})`);
                break;
            }
            case "keylist_getkey": {
                bodyres = new smt_exp_1.SMTValue(`(bsqkeylist@key ${params[0]})`);
                break;
            }
            case "keylist_gettail": {
                bodyres = new smt_exp_1.SMTValue(`(bsqkeylist@tail ${params[0]})`);
                break;
            }
            case "set_size":
            case "map_size": {
                bodyres = new smt_exp_1.SMTValue(`(bsqkvcontainer@size ${params[0]})`);
                break;
            }
            case "set_has_key":
            case "map_has_key": {
                bodyres = new smt_exp_1.SMTValue(`(not (is-bsqterm@clear (select (bsqkvcontainer@entries ${params[0]}) ${params[1]})))`);
                break;
            }
            case "set_at_val":
            case "map_at_val": {
                bodyres = this.typegen.coerce(new smt_exp_1.SMTValue(`(select (bsqkvcontainer@entries ${params[0]}) ${params[1]})`), this.typegen.anyType, rtype);
                break;
            }
            case "set_get_keylist":
            case "map_get_keylist": {
                bodyres = new smt_exp_1.SMTValue(`(bsqkvcontainer@keylist ${params[0]})`);
                break;
            }
            case "set_clear_val":
            case "map_clear_val": {
                bodyres = new smt_exp_1.SMTValue(`(cons@bsqkvcontainer (- (bsqkvcontainer@size ${params[0]}) 1) ${params[2]} (store (bsqkvcontainer@entries ${params[0]}) ${params[1]} bsqterm@clear))`);
                break;
            }
            case "set_unsafe_update":
            case "map_unsafe_update":
            case "set_destuctive_update":
            case "map_destuctive_update": {
                const storeval = this.typegen.coerce(new smt_exp_1.SMTValue(params[2]), this.typegen.getMIRType(idecl.params[2].type), this.typegen.anyType).emit();
                bodyres = new smt_exp_1.SMTValue(`(cons@bsqkvcontainer (bsqkvcontainer@size ${params[0]}) (bsqkvcontainer@keylist ${params[0]}) (store (bsqkvcontainer@entries ${params[0]}) ${params[1]} ${storeval}))`);
                break;
            }
            case "set_unsafe_add":
            case "map_unsafe_add":
            case "set_destuctive_add":
            case "map_destuctive_add": {
                const storeval = this.typegen.coerce(new smt_exp_1.SMTValue(params[2]), this.typegen.getMIRType(idecl.params[2].type), this.typegen.anyType).emit();
                bodyres = new smt_exp_1.SMTValue(`(cons@bsqkvcontainer (+ (bsqkvcontainer@size ${params[0]}) 1) ${params[3]} (store (bsqkvcontainer@entries ${params[0]}) ${params[1]} ${storeval}))`);
                break;
            }
            default: {
                bodyres = new smt_exp_1.SMTValue(`[Builtin not defined -- ${idecl.iname}]`);
                break;
            }
        }
        if (!autowrap) {
            return bodyres;
        }
        else {
            return new smt_exp_1.SMTValue(`(result_success@${this.typegen.typeToSMTCategory(rtype)} ${bodyres.emit()})`);
        }
    }
}
exports.SMTBodyEmitter = SMTBodyEmitter;
//# sourceMappingURL=smtbody_emitter.js.map