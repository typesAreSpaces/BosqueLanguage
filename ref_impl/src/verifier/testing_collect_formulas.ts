//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import chalk from "chalk";
import { MIREmitter } from "../compiler/mir_emitter";
import { PackageConfig, MIRAssembly, MIRFunctionDecl } from "../compiler/mir_assembly";
import { MIRBody } from "../compiler/mir_ops";
import { collectFormulas, typesSeen } from "./collect_formulas_3"

function getControlFlow(app: string, section: string, fd: number): void {

    let bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));

    let files: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(bosque_dir, "src/core/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();

        const collectionsdir = Path.join(bosque_dir, "src/core/collections.bsq");
        const collectionsdata = FS.readFileSync(collectionsdir).toString();

        const appdir = app;
        const appdata = FS.readFileSync(appdir).toString();

        files = [{ relativePath: coredir, contents: coredata }, { relativePath: collectionsdir, contents: collectionsdata }, { relativePath: appdir, contents: appdata }];
    }
    catch (ex) {
        process.stdout.write(chalk.red(`Read failed with exception -- ${ex}\n`));
        FS.closeSync(fd);
        process.exit(1);
    }

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), files);

    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk.red(`Parse error -- ${errors[i]}\n`));
        }
        FS.closeSync(fd);
        process.exit(1);
    }

    try {
        const sectionName = section.split(":").join("_");
        const invokeDecl = ((masm as MIRAssembly).functionDecls.get(section) as MIRFunctionDecl).invoke;
        const ibody = (invokeDecl.body as MIRBody).body;
        // If this is a FunctionDecl then the array of parameters,
        // if it is not empty, will add more elements to the
        // variable typesSeen
        invokeDecl.params.map(x => typesSeen.set(sectionName + "__" + x.name, x.type.trkey));
        if (typeof (ibody) === "string") {
            FS.closeSync(fd);
            process.exit(0);
        }
        else {
            // --------------------------------------------------
            // Here we generate the file.z3, essentially
            // Since for Z3 is invalid a name with ":",
            // we replace it with a "_"
            let formula = collectFormulas(ibody, sectionName);
            formula.initialDeclarationZ3(fd);
            formula.toZ3(fd);
            formula.checkSatZ3(fd);
            // formula.getModelZ3(fd);
            // --------------------------------------------------
            FS.closeSync(fd);
            process.exit(0);
        }
    }
    catch (ex) {
        process.stdout.write(chalk.red(`fail with exception -- ${ex}\n`));
        FS.closeSync(fd);
        process.exit(1);
    }
}

////
//Entrypoint

setImmediate(() => {
    // Mac Machine
    let dirMachine = "/Users/joseabelcastellanosjoo/BosqueLanguage/ref_impl/src/test/apps"
    // Windows Machine
    // let dirMachine = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps";

    let bosqueFile = "/max/main.bsq";
    let section = "NSMain::max";
    let fd = FS.openSync(bosqueFile.split('/').join('_').replace("bsq", "z3"), 'w');
    getControlFlow(dirMachine + bosqueFile, section, fd);
});
