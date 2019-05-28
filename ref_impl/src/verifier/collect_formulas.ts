//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import chalk from "chalk";
import { MIREmitter } from "../compiler/mir_emitter";
import { PackageConfig, MIRAssembly, MIRFunctionDecl } from "../compiler/mir_assembly";
import { MIRBody, MIRBasicBlock } from "../compiler/mir_ops";
import { topologicalOrder, computeBlockLinks } from "../compiler/ir_info";

function getControlFlow(app: string, section: string): void {

    let bosque_dir: string = Path.normalize(Path.join(__dirname, "../../"));

    let files: { relativePath: string, contents: string }[] = [];
    try {
        const coredir = Path.join(bosque_dir, "src/core/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();

        const collectionsdir = Path.join(bosque_dir, "src/core/collections.bsq");
        const collectionsdata = FS.readFileSync(collectionsdir).toString();

        const appdir = app;
        console.log(appdir);
        const appdata = FS.readFileSync(appdir).toString();

        files = [{ relativePath: coredir, contents: coredata }, { relativePath: collectionsdir, contents: collectionsdata }, { relativePath: appdir, contents: appdata }];
    }
    catch (ex) {
        process.stdout.write(chalk.red(`Read failed with exception -- ${ex}\n`));
        process.exit(1);
    }

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), files);

    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk.red(`Parse error -- ${errors[i]}\n`));
        }
        process.exit(1);
    }

    try {
        const ibody = (((masm as MIRAssembly).functionDecls.get(section) as MIRFunctionDecl).invoke.body as MIRBody).body;
        if (typeof (ibody) === "string") {
            process.stdout.write("Success as string!\n");
            process.exit(0);
        }
        else {
            gatherFormulas(ibody);
            process.stdout.write("Success as blocks!\n");
            process.exit(0);
        }
    }
    catch (ex) {
        process.stdout.write(chalk.red(`fail with exception -- ${ex}\n`));
        process.exit(1);
    }
}

function gatherFormulas(ibody: Map<string, MIRBasicBlock>) {
    const blocks = topologicalOrder(ibody);
    const flow = computeBlockLinks(ibody);
    console.log("Blocks:-----------------------------------------------------------------------");
    console.log(blocks);
    console.log("More detailed Blocks:---------------------------------------------------------");
    blocks.map(x => console.log(x));
    console.log("More detailed++ Blocks:-------------------------------------------------------");
    blocks.map(x => console.log(x.jsonify()));
    console.log("Flow:-------------------------------------------------------------------------");
    console.log(flow);
}

////
//Entrypoint

setImmediate(() => getControlFlow("/Users/joseabelcastellanosjoo/BosqueLanguage/ref_impl/src/test/apps/max/main.bsq", "NSMain::max"));
