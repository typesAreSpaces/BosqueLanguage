"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const FS = require("fs");
const Path = require("path");
const chalk_1 = require("chalk");
const mir_emitter_1 = require("../../compiler/mir_emitter");
const mir_assembly_1 = require("../../compiler/mir_assembly");
function bosqueToMASM(info) {
    let bosque_dir = Path.normalize(Path.join(__dirname, "./../../../"));
    let files = [];
    try {
        // const coredir = Path.join(bosque_dir, "src/core/core.bsq");
        const coredir = Path.join(bosque_dir, "src/core/direct/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();
        // const collectionsdir = Path.join(bosque_dir, "src/core/collections.bsq");
        const collectionsdir = Path.join(bosque_dir, "src/core/direct/collections.bsq");
        const collectionsdata = FS.readFileSync(collectionsdir).toString();
        const appdir = info.file_directory + "/" + info.file_name;
        const appdata = FS.readFileSync(appdir).toString();
        files = [{ relativePath: coredir, contents: coredata }, { relativePath: collectionsdir, contents: collectionsdata }, { relativePath: appdir, contents: appdata }];
    }
    catch (ex) {
        process.stdout.write(chalk_1.default.red(`Read failed with exception -- ${ex}\n`));
        throw new Error(`Read failed with exception -- ${ex}\n`);
    }
    const { masm, errors } = mir_emitter_1.MIREmitter.generateMASM(new mir_assembly_1.PackageConfig(), true, true, true, files);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk_1.default.red(`Parse error -- ${errors[i]}\n`));
        }
        throw new Error("Too many Parsing errors!\n");
    }
    try {
        return masm;
    }
    catch (ex) {
        process.stdout.write(chalk_1.default.red(`fail with exception -- ${ex}\n`));
        throw new Error(`fail with exception -- ${ex}\n`);
    }
}
exports.bosqueToMASM = bosqueToMASM;
function sanitizeName(name) {
    // TOUPDATE: Add more `replace operations' if the IR syntax (names)
    // conflicts with FStar syntax
    let result = name
        .replace(new RegExp("#", 'g'), "_")
        .replace(new RegExp("\\$", 'g'), "_")
        .replace(new RegExp(":", 'g'), "_");
    // We lowercase the first character because variable/function
    // declaration in fstar requires that
    return result.charAt(0).toLowerCase() + result.slice(1);
}
exports.sanitizeName = sanitizeName;
function toFStarSequence(seq) {
    if (seq.length == 0) {
        return "SNil";
    }
    else {
        const tail = seq.slice(1);
        return "(SCons " + seq[0] + " "
            + (seq.length - 1) + " " + toFStarSequence(tail) + ")";
    }
}
exports.toFStarSequence = toFStarSequence;
function toFStarList(seq) {
    if (seq.length == 0) {
        return "LNil";
    }
    else {
        const tail = seq.slice(1);
        return "(LCons " + seq[0] + " " + toFStarList(tail) + ")";
    }
}
exports.toFStarList = toFStarList;
function topoVisit(n, tordered, neighbors) {
    if (tordered.findIndex(element => element === n) !== -1) {
        return;
    }
    const n_neighbors = neighbors.get(n);
    n_neighbors.forEach(neighbor => topoVisit(neighbor, tordered, neighbors));
    tordered.push(n);
}
function topologicalOrder(neighbors) {
    let tordered = [];
    neighbors.forEach((_, node) => topoVisit(node, tordered, neighbors));
    return tordered.reverse();
}
exports.topologicalOrder = topologicalOrder;
//# sourceMappingURL=util.js.map