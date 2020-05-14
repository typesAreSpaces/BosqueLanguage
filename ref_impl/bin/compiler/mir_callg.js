"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
//
//Compute the static call graph for an assembly
//
const assert = require("assert");
const mir_ops_1 = require("./mir_ops");
const mir_emitter_1 = require("./mir_emitter");
function computeCalleesInBlocks(blocks, invokeNode, assembly) {
    blocks.forEach((block) => {
        for (let i = 0; i < block.ops.length; ++i) {
            const op = block.ops[i];
            switch (op.tag) {
                case mir_ops_1.MIROpTag.MIRLoadConstTypedString: {
                    const pkey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("invoke", op.pfunckey);
                    invokeNode.callees.add(pkey);
                    break;
                }
                case mir_ops_1.MIROpTag.MIRAccessConstantValue: {
                    const constkey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("const", op.ckey);
                    invokeNode.callees.add(constkey);
                    break;
                }
                case mir_ops_1.MIROpTag.MIRLoadFieldDefaultValue: {
                    const fdefaultkey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("fdefault", op.fkey);
                    invokeNode.callees.add(fdefaultkey);
                    break;
                }
                case mir_ops_1.MIROpTag.MIRConstructorPrimary: {
                    const cop = op;
                    const edecl = assembly.entityDecls.get(cop.tkey);
                    if (edecl.invariants.length !== 0) {
                        const invkey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("invariant", cop.tkey);
                        invokeNode.callees.add(invkey);
                    }
                    break;
                }
                case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionSingletons: {
                    const cop = op;
                    const ctype = assembly.entityDecls.get(cop.tkey);
                    if (ctype.name === "List") {
                        //all handled inline
                    }
                    else if (ctype.name === "Set") {
                        const invkey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("invoke", mir_emitter_1.MIRKeyGenerator.generateStaticKey_MIR(ctype, "_cons_insert"));
                        invokeNode.callees.add(invkey);
                    }
                    else {
                        const invkey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("invoke", mir_emitter_1.MIRKeyGenerator.generateStaticKey_MIR(ctype, "_cons_insert"));
                        invokeNode.callees.add(invkey);
                    }
                    break;
                }
                case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionCopies: {
                    assert(false);
                    break;
                }
                case mir_ops_1.MIROpTag.MIRConstructorPrimaryCollectionMixed: {
                    assert(false);
                    break;
                }
                case mir_ops_1.MIROpTag.MIRInvokeFixedFunction: {
                    const iop = op;
                    const ikey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("invoke", iop.mkey);
                    invokeNode.callees.add(ikey);
                    break;
                }
                case mir_ops_1.MIROpTag.MIRInvokeVirtualTarget: {
                    //TODO lookup all possible vtargets and add them
                    assert(false);
                    break;
                }
                default: {
                    //ignore all other ops
                    break;
                }
            }
        }
    });
}
function sccVisit(cn, scc, marked, invokes) {
    if (marked.has(cn.invoke)) {
        return;
    }
    scc.add(cn.invoke);
    marked.add(cn.invoke);
    cn.callers.forEach((pred) => sccVisit(invokes.get(pred), scc, marked, invokes));
}
function topoVisit(cn, pending, tordered, invokes) {
    if (pending.findIndex((vn) => vn.invoke === cn.invoke) !== -1 || tordered.findIndex((vn) => vn.invoke === cn.invoke) !== -1) {
        return;
    }
    pending.push(cn);
    cn.callees.forEach((succ) => invokes.get(succ).callers.add(cn.invoke));
    cn.callees.forEach((succ) => topoVisit(invokes.get(succ), pending, tordered, invokes));
    tordered.push(cn);
}
function processBodyInfo(bkey, binfo, assembly) {
    let cn = { invoke: bkey, callees: new Set(), callers: new Set() };
    binfo.forEach((b) => {
        computeCalleesInBlocks(b.body, cn, assembly);
    });
    return cn;
}
function constructCallGraphInfo(entryPoints, assembly) {
    let invokes = new Map();
    assembly.constantDecls.forEach((cdecl) => {
        invokes.set(cdecl.value.bkey, processBodyInfo(cdecl.value.bkey, [cdecl.value], assembly));
    });
    assembly.entityDecls.forEach((edecl, ekey) => {
        if (edecl.invariants.length !== 0) {
            const invkey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("invariant", ekey);
            invokes.set(invkey, processBodyInfo(invkey, edecl.invariants, assembly));
        }
    });
    assembly.fieldDecls.forEach((fdecl, fkey) => {
        if (fdecl.value !== undefined) {
            const fdkey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("fdefault", fkey);
            invokes.set(fdkey, processBodyInfo(fdkey, [fdecl.value], assembly));
        }
    });
    assembly.invokeDecls.forEach((ivk, ikey) => {
        invokes.set(ivk.body.bkey, processBodyInfo(ivk.body.bkey, [ivk.body], assembly));
        if (ivk.preconditions.length !== 0) {
            const prekey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("pre", ikey);
            invokes.set(prekey, processBodyInfo(prekey, ivk.preconditions.map((pre) => pre[0]), assembly));
            invokes.get(ivk.body.bkey).callees.add(prekey);
        }
        if (ivk.postconditions.length !== 0) {
            const postkey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("post", ikey);
            invokes.set(postkey, processBodyInfo(postkey, ivk.postconditions, assembly));
            invokes.get(ivk.body.bkey).callees.add(postkey);
        }
    });
    assembly.primitiveInvokeDecls.forEach((ivk, ikey) => {
        let cn = { invoke: mir_emitter_1.MIRKeyGenerator.generateBodyKey("invoke", ikey), callees: new Set(), callers: new Set() };
        ivk.pcodes.forEach((pc) => cn.callees.add(mir_emitter_1.MIRKeyGenerator.generateBodyKey("invoke", pc.code)));
        invokes.set(cn.invoke, cn);
        if (ivk.preconditions.length !== 0) {
            const prekey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("pre", ikey);
            invokes.set(prekey, processBodyInfo(prekey, ivk.preconditions.map((pre) => pre[0]), assembly));
            cn.callees.add(prekey);
        }
        if (ivk.postconditions.length !== 0) {
            const postkey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("post", ikey);
            invokes.set(postkey, processBodyInfo(postkey, ivk.postconditions, assembly));
            cn.callees.add(postkey);
        }
    });
    let roots = [];
    let tordered = [];
    entryPoints.forEach((ivk) => {
        const ikey = mir_emitter_1.MIRKeyGenerator.generateBodyKey("invoke", ivk);
        roots.push(invokes.get(ikey));
        topoVisit(invokes.get(ikey), [], tordered, invokes);
    });
    tordered = tordered.reverse();
    let marked = new Set();
    let recursive = [];
    for (let i = 0; i < tordered.length; ++i) {
        let scc = new Set();
        sccVisit(tordered[i], scc, marked, invokes);
        if (scc.size > 1 || tordered[i].callees.has(tordered[i].invoke)) {
            recursive.push(scc);
        }
    }
    return { invokes: invokes, topologicalOrder: tordered, roots: roots, recursive: recursive };
}
exports.constructCallGraphInfo = constructCallGraphInfo;
//# sourceMappingURL=mir_callg.js.map