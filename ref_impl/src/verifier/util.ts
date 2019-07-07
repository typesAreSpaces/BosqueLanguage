//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import chalk from "chalk";
import { MIREmitter } from "./../compiler/mir_emitter";
import { PackageConfig, MIRAssembly, MIRFunctionDecl } from "./../compiler/mir_assembly";
import { MIRBody, MIRBasicBlock } from "./../compiler/mir_ops";

interface InfoFunctionCall {
    directory: string;
    fileName: string;
    section: string;
}

function bosqueToIRBody(info: InfoFunctionCall): Map<string, MIRBasicBlock> {

    let bosque_dir: string = Path.normalize(Path.join(__dirname, "./../../"));
    let files: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(bosque_dir, "src/core/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();

        const collectionsdir = Path.join(bosque_dir, "src/core/collections.bsq");
        const collectionsdata = FS.readFileSync(collectionsdir).toString();

        const appdir = info.directory + info.fileName;
        const appdata = FS.readFileSync(appdir).toString();

        files = [{ relativePath: coredir, contents: coredata }, { relativePath: collectionsdir, contents: collectionsdata }, { relativePath: appdir, contents: appdata }];
    }
    catch (ex) {
        process.stdout.write(chalk.red(`Read failed with exception -- ${ex}\n`));
        throw new Error(`Read failed with exception -- ${ex}\n`);
    }

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), files);

    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk.red(`Parse error -- ${errors[i]}\n`));
        }
        throw new Error("Too many Parsing errors!\n");
    }

    try {
        // const sectionName = "__" + info.section.split(":").join("_");
        const invokeDecl = ((masm as MIRAssembly).functionDecls.get(info.section) as MIRFunctionDecl).invoke;
        const ir_body = (invokeDecl.body as MIRBody).body;

        // invokeDecl.params.map(arg => stringVariableToStringType.set(sectionName + "_" + arg.name, arg.type.trkey));
        // TODO: Make declaration about the function itself
        // Hint: Check invokeDecl properties
        // console.log(invokeDecl);
        // console.log();

        if (typeof (ir_body) === "string") {
            throw new Error("The program has string type\n");
        }
        else {
            return ir_body;
        }
    }
    catch (ex) {
        process.stdout.write(chalk.red(`fail with exception -- ${ex}\n`));
        throw new Error(`fail with exception -- ${ex}\n`);
    }
} 

function sanitizeName(name : string) : string {
    return name.replace("#", "_").replace("$", "_");
}

export { bosqueToIRBody, InfoFunctionCall, sanitizeName };