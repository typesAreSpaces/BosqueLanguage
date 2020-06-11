//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import { MIREmitter } from "../../compiler/mir_emitter";
import { PackageConfig, MIRAssembly } from "../../compiler/mir_assembly";

interface PathFile {
  file_directory: string;
  file_name: string;
}

function bosqueToMASM(files: string[], core: string) : MIRAssembly | undefined {
  process.stdout.write("Reading app code...\n");

  let bosque_dir: string = Path.normalize(Path.join(__dirname, "./../../"));
  let code: { relativePath: string, contents: string }[] = [];
  try {
    const coredir = Path.join(bosque_dir, "core/", core);
    const corefiles = FS.readdirSync(coredir);

    for (let i = 0; i < corefiles.length; ++i) {
      const cfpath = Path.join(coredir, corefiles[i]);
      code.push({ relativePath: cfpath, contents: FS.readFileSync(cfpath).toString() });
    }

    for (let i = 0; i < files.length; ++i) {
      const file = { relativePath: files[i], contents: FS.readFileSync(files[i]).toString() };
      code.push(file);
    }
  }
  catch (ex) {
    process.stdout.write(`Read failed with exception -- ${ex}\n`);
    process.exit(1);
  }

  process.stdout.write("Compiling assembly...\n");

  const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), "debug", true, true, code);
  if (errors.length !== 0) {
    for (let i = 0; i < errors.length; ++i) {
      process.stdout.write(`Parse error -- ${errors[i]}\n`);
    }

    process.exit(1);
  }

  return masm;
}

function sanitizeName(name: string): string {
  // TOUPDATE: Add more `replace operations' if the IR syntax (names)
  // conflicts with FStar syntax
  let result = name
    .replace(/#/g,  "_")
    .replace(/:/g,  "_")
    .replace(/-/g,  "_")
    .replace(/\//g, "_")
    .replace(/%/g,  "_")
    .replace(/\[/g, "_")
    .replace(/\]/g, "_")
    .replace(new RegExp("\\$", 'g'), "_")
    .replace(new RegExp("\\.", 'g'), "_")
  // We lowercase the first character because variable/function
  // declaration in fstar requires that
  return result.charAt(0).toLowerCase() + result.slice(1);
}

function toFStarSequence(seq: string[]): string {
  if (seq.length == 0) {
    return "SNil";
  }
  else {
    const tail = seq.slice(1);
    return "(SCons " + seq[0] + " "
      + (seq.length - 1) + " " + toFStarSequence(tail) + ")";
  }
}

function toFStarList(seq: string[]): string {
  if (seq.length == 0) {
    return "LNil";
  }
  else {
    const tail = seq.slice(1);
    return "(LCons " + seq[0] + " " + toFStarList(tail) + ")";
  }
}

function topoVisit(n: any, tordered: any[], neighbors: Map<any, Set<any>>) {
  if (tordered.findIndex(element => element === n) !== -1) {
    return;
  }

  const n_neighbors = neighbors.get(n) as Set<any>;
  n_neighbors.forEach(neighbor => topoVisit(neighbor, tordered, neighbors));

  tordered.push(n);
}

function topologicalOrder(neighbors: Map<any, Set<any>>): any[] {
  let tordered: any[] = [];

  neighbors.forEach((_, node) => topoVisit(node, tordered, neighbors));

  return tordered.reverse();
}

export {
  bosqueToMASM, PathFile,
  sanitizeName, toFStarSequence, toFStarList,
  topologicalOrder
};
