//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import chalk from "chalk";
import { MIREmitter } from "./../compiler/mir_emitter";
import { PackageConfig, MIRAssembly, MIRFunctionDecl } from "./../compiler/mir_assembly";

interface PathFile {
    directory: string;
    fileName: string;
}

function bosqueToInvokeDecl(info: PathFile): Map<string, MIRFunctionDecl> {

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
        return (masm as MIRAssembly).functionDecls;
    }
    catch (ex) {
        process.stdout.write(chalk.red(`fail with exception -- ${ex}\n`));
        throw new Error(`fail with exception -- ${ex}\n`);
    }
} 

function sanitizeName(name : string) : string {
    // TODO: Add more `replace operations' if the IR syntax (names)
    // conflicts with FStar syntax
    let result = name
    .replace(new RegExp("#", 'g'), "_")
    .replace(new RegExp("\\$", 'g'), "_")
    .replace(new RegExp(":", 'g'), "_")
    return result.charAt(0).toLowerCase() + result.slice(1);
}

export { bosqueToInvokeDecl, PathFile, sanitizeName };