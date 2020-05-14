"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const mir_assembly_1 = require("../../compiler/mir_assembly");
const cpptype_emitter_1 = require("./cpptype_emitter");
const cppbody_emitter_1 = require("./cppbody_emitter");
const mir_callg_1 = require("../../compiler/mir_callg");
const mir_ops_1 = require("../../compiler/mir_ops");
const assert = require("assert");
class CPPEmitter {
    static emit(assembly, entrypointname) {
        const typeemitter = new cpptype_emitter_1.CPPTypeEmitter(assembly);
        typeemitter.initializeConceptSubtypeRelation();
        const bodyemitter = new cppbody_emitter_1.CPPBodyEmitter(assembly, typeemitter);
        let typedecls_fwd = [];
        let typedecls = [];
        let nominaltypeinfo = [];
        let vfieldaccesses = [];
        let vcalls = [];
        assembly.entityDecls.forEach((edecl) => {
            const cppdecl = typeemitter.generateCPPEntity(edecl);
            if (cppdecl !== undefined) {
                typedecls_fwd.push(cppdecl.fwddecl);
                typedecls.push(cppdecl.fulldecl);
            }
            if (!typeemitter.isSpecialRepType(edecl)) {
                const enumv = typeemitter.mangleStringForCpp(edecl.tkey);
                const displayv = edecl.tkey;
                nominaltypeinfo.push({ enum: enumv, display: displayv });
            }
            edecl.fields.forEach((fd) => {
                if (fd.enclosingDecl !== edecl.tkey) {
                    const rftype = typeemitter.typeToCPPType(typeemitter.getMIRType(fd.declaredType), "return");
                    const isig = `virtual ${rftype} get$${typeemitter.mangleStringForCpp(fd.fkey)}() { printf("%s\\n", "Bad v-field resolve -- ${fd.fkey}"); exit(1); return ${typeemitter.typeToCPPDefaultValue(typeemitter.getMIRType(fd.declaredType))}; }`;
                    if (!vfieldaccesses.includes(isig)) {
                        vfieldaccesses.push(isig);
                    }
                }
            });
            [...edecl.vcallMap].map((callp) => {
                const rcall = (typeemitter.assembly.invokeDecls.get(callp[1]) || typeemitter.assembly.primitiveInvokeDecls.get(callp[1]));
                if (rcall.enclosingDecl !== edecl.tkey) {
                    const rtype = typeemitter.typeToCPPType(typeemitter.getMIRType(rcall.resultType), "return");
                    const vargs = rcall.params.slice(1).map((fp) => `${typeemitter.typeToCPPType(typeemitter.getMIRType(fp.type), "parameter")} ${fp.name}`);
                    const vcall = `virtual ${rtype} ${typeemitter.mangleStringForCpp(callp[0])}(${vargs.join(", ")}) { printf("%s\\n", "Bad v-call resolve ${callp[1]}"); exit(1); return ${typeemitter.typeToCPPDefaultValue(typeemitter.getMIRType(rcall.resultType))}; }`;
                    if (!vcalls.includes(vcall)) {
                        vcalls.push(vcall);
                    }
                }
            });
        });
        nominaltypeinfo = nominaltypeinfo.sort((a, b) => a.enum.localeCompare(b.enum));
        const cginfo = mir_callg_1.constructCallGraphInfo(assembly.entryPoints, assembly);
        const rcg = [...cginfo.topologicalOrder].reverse();
        let funcdecls_fwd = [];
        let funcdecls = [];
        for (let i = 0; i < rcg.length; ++i) {
            const bbup = rcg[i];
            const tag = mir_ops_1.extractMirBodyKeyPrefix(bbup.invoke);
            //
            //TODO: rec is implmented via stack recusion -- want to add option for bounded stack version
            //
            if (tag === "invoke") {
                const ikey = mir_ops_1.extractMirBodyKeyData(bbup.invoke);
                const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey));
                const finfo = bodyemitter.generateCPPInvoke(idcl);
                funcdecls_fwd.push(finfo.fwddecl);
                funcdecls.push(finfo.fulldecl);
            }
            else if (tag === "pre") {
                const ikey = mir_ops_1.extractMirBodyKeyData(bbup.invoke);
                const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey));
                const finfo = bodyemitter.generateCPPPre(bbup.invoke, idcl);
                funcdecls.push(finfo);
            }
            else if (tag === "post") {
                const ikey = mir_ops_1.extractMirBodyKeyData(bbup.invoke);
                const idcl = (assembly.invokeDecls.get(ikey) || assembly.primitiveInvokeDecls.get(ikey));
                const finfo = bodyemitter.generateCPPPost(bbup.invoke, idcl);
                funcdecls.push(finfo);
            }
            else if (tag === "invariant") {
                const edcl = assembly.entityDecls.get(mir_ops_1.extractMirBodyKeyData(bbup.invoke));
                const finfo = bodyemitter.generateCPPInv(bbup.invoke, edcl);
                funcdecls.push(finfo);
            }
            else if (tag === "const") {
                const cdcl = assembly.constantDecls.get(mir_ops_1.extractMirBodyKeyData(bbup.invoke));
                const finfo = bodyemitter.generateCPPConst(bbup.invoke, cdcl);
                if (finfo !== undefined) {
                    funcdecls_fwd.push(finfo.fwddecl);
                    funcdecls.push(finfo.fulldecl);
                }
            }
            else {
                assert(tag === "fdefault");
                const fdcl = assembly.fieldDecls.get(mir_ops_1.extractMirBodyKeyData(bbup.invoke));
                const finfo = bodyemitter.generateCPPFDefault(bbup.invoke, fdcl);
                if (finfo !== undefined) {
                    funcdecls_fwd.push(finfo.fwddecl);
                    funcdecls.push(finfo.fulldecl);
                }
            }
        }
        let conceptSubtypes = [];
        typeemitter.conceptSubtypeRelation.forEach((stv, cpt) => {
            const nemums = stv.map((ek) => `MIRNominalTypeEnum::${typeemitter.mangleStringForCpp(ek)}`).sort();
            const sta = `constexpr MIRNominalTypeEnum MIRConceptSubtypeArray__${typeemitter.mangleStringForCpp(cpt)}[${nemums.length}] = {${nemums.join(", ")}};`;
            conceptSubtypes.push(sta);
        });
        const typechecks = [...bodyemitter.subtypeFMap].map(tcp => tcp[1]).sort((tc1, tc2) => tc1.order - tc2.order).map((tc) => tc.decl);
        let conststring_declare = [];
        let conststring_create = [];
        bodyemitter.allConstStrings.forEach((v, k) => {
            conststring_declare.push(`static BSQString ${v};`);
            conststring_create.push(`BSQString Runtime::${v}(${k}, 1);`);
        });
        let constint_declare = [];
        let constint_create = [];
        bodyemitter.allConstBigInts.forEach((v, k) => {
            constint_declare.push(`static BSQInt ${v};`);
            constint_create.push(`BSQInt Runtime::${v}(BigInt(${k}));`);
        });
        let propertyenums = new Set();
        let propertynames = new Set();
        let known_property_lists_declare = [];
        bodyemitter.allPropertyNames.forEach((pname) => {
            propertyenums.add(pname);
            propertynames.add(`"${pname}"`);
        });
        assembly.typeMap.forEach((tt) => {
            tt.options.forEach((topt) => {
                if (topt instanceof mir_assembly_1.MIRRecordType) {
                    topt.entries.forEach((entry) => {
                        propertyenums.add(entry.name);
                        propertynames.add(`"${entry.name}"`);
                    });
                }
                if (typeemitter.isKnownLayoutRecordType(tt)) {
                    const knownrec = cpptype_emitter_1.CPPTypeEmitter.getKnownLayoutRecordType(tt);
                    const knownenum = knownrec.entries.map((entry) => `MIRPropertyEnum::${entry.name}`);
                    const decl = `constexpr MIRPropertyEnum ${typeemitter.getKnownPropertyRecordArrayName(tt)}[${knownrec.entries.length}] = {${knownenum.join(", ")}};`;
                    if (knownrec.entries.length !== 0 && !known_property_lists_declare.includes(decl)) {
                        known_property_lists_declare.push(decl);
                    }
                }
            });
        });
        const entrypoint = assembly.invokeDecls.get(entrypointname);
        const restype = typeemitter.getMIRType(entrypoint.resultType);
        const mainsig = `int main(int argc, char** argv)`;
        const chkarglen = `    if(argc != ${entrypoint.params.length} + 1) { fprintf(stderr, "Expected ${entrypoint.params.length} arguments but got %i\\n", argc - 1); exit(1); }`;
        const convdecl = "    std::wstring_convert<std::codecvt_utf8<char32_t>, char32_t> conv;";
        const convargs = entrypoint.params.map((p, i) => {
            if (p.type === "NSCore::Bool") {
                const fchk = `if(std::string(argv[${i}+1]) != "true" && std::string(argv[${i}+1]) != "false") { fprintf(stderr, "Bad argument for ${p.name} -- expected Bool got %s\\n", argv[${i}+1]); exit(1); }`;
                const conv = `bool ${p.name} = std::string(argv[${i}+1]) == "true";`;
                return "    " + fchk + "\n    " + conv;
            }
            else if (p.type === "NSCore::Int") {
                const fchk = `if(!std::regex_match(std::string(argv[${i}+1]), std::regex("^([+]|[-])?[0-9]{1,8}$"))) { fprintf(stderr, "Bad argument for ${p.name} -- expected (small) Int got %s\\n", argv[${i}+1]); exit(1); }`;
                const conv = `BSQInt ${p.name}(std::stoi(std::string(argv[${i}+1])));`;
                return "    \n    " + fchk + "\n    " + conv;
            }
            else {
                const conv = `BSQString ${p.name}(argv[${i}+1], 1);`;
                return "    " + conv;
            }
        });
        let scopev = "";
        let callargs = entrypoint.params.map((p) => p.type !== "NSCore::String" ? p.name : `&${p.name}`);
        if (typeemitter.maybeRefableCountableType(restype)) {
            if (typeemitter.maybeRefableCountableType(restype)) {
                if (typeemitter.isTupleType(restype)) {
                    const maxlen = cpptype_emitter_1.CPPTypeEmitter.getTupleTypeMaxLength(restype);
                    scopev = `BSQRefScope<${maxlen}> __scopes__;`;
                    for (let i = 0; i < maxlen; ++i) {
                        callargs.push(`__scopes__.getCallerSlot<${i}>()`);
                    }
                }
                else if (typeemitter.isRecordType(restype)) {
                    const allprops = cpptype_emitter_1.CPPTypeEmitter.getRecordTypeMaxPropertySet(restype);
                    scopev = `BSQRefScope<${allprops.length}> __scopes__;`;
                    for (let i = 0; i < allprops.length; ++i) {
                        callargs.push(`__scopes__.getCallerSlot<${i}>()`);
                    }
                }
                else {
                    scopev = "BSQRefScope<1> __scopes__;";
                    callargs.push("__scopes__.getCallerSlot<0>()");
                }
            }
        }
        typeemitter.scopectr = 0;
        const callv = `${bodyemitter.invokenameToCPP(entrypointname)}(${callargs.join(", ")})`;
        const fcall = `std::cout << conv.to_bytes(Runtime::diagnostic_format(${typeemitter.coerce(callv, restype, typeemitter.anyType)})) << "\\n"`;
        if (typeemitter.scopectr !== 0) {
            const scopevar = bodyemitter.varNameToCppName("$scope$");
            const refscope = `BSQRefScope<${typeemitter.scopectr}> ${scopevar};`;
            scopev = scopev + " " + refscope;
        }
        const maincall = `${mainsig} {\n${chkarglen}\n\n${convdecl}\n${convargs.join("\n")}\n\n  try {\n    ${scopev}\n    ${fcall};\n    fflush(stdout);\n    return 0;\n  } catch (BSQAbort& abrt) HANDLE_BSQ_ABORT(abrt) \n}\n`;
        return {
            typedecls_fwd: typedecls_fwd.sort().join("\n"),
            typedecls: typedecls.sort().join("\n"),
            nominalenums: nominaltypeinfo.map((nti) => nti.enum).join(",\n    "),
            nomnialdisplaynames: nominaltypeinfo.map((nti) => `"${nti.display}"`).join(",\n  "),
            conceptSubtypeRelation: conceptSubtypes.sort().join("\n"),
            typechecks: typechecks.join("\n"),
            funcdecls_fwd: funcdecls_fwd.join("\n"),
            funcdecls: funcdecls.join("\n"),
            conststring_declare: conststring_declare.sort().join("\n  "),
            conststring_create: conststring_create.sort().join("\n  "),
            constint_declare: constint_declare.sort().join("\n  "),
            constint_create: constint_create.sort().join("\n  "),
            propertyenums: [...propertyenums].sort().join(",\n  "),
            propertynames: [...propertynames].sort().join(",\n  "),
            known_property_lists_declare: known_property_lists_declare.sort().join("\n"),
            vfield_decls: [...vfieldaccesses].sort().join("\n"),
            vmethod_decls: [...vcalls].sort().join("\n"),
            maincall: maincall
        };
    }
}
exports.CPPEmitter = CPPEmitter;
//# sourceMappingURL=cppdecls_emitter.js.map