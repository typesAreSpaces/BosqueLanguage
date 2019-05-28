//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

// Idea: Take a MIRBody and
// gather the formulas from the blocks
// But MIRBody is a class!

// import { SourceInfo } from "../ast/parser";
// import { topologicalOrder, computeBlockLinks, FlowLink } from "../compiler/ir_info";
import * as FS from "fs";
import * as Path from "path";
import { MIREmitter } from "../compiler/mir_emitter";
import { PackageConfig, MIRAssembly, MIRFunctionDecl } from "../compiler/mir_assembly";
import { MIRBody, MIRBasicBlock } from "../compiler/mir_ops";
import { topologicalOrder, computeBlockLinks } from "../compiler/ir_info";

function getIRV(app: string, section: string): MIRBody | void {
    process.stdout.write("Reading app code...\n");

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
        process.exit(1);
    }

    const { masm, errors } = MIREmitter.generateMASM(new PackageConfig(), files);

    if (errors.length !== 0) {
        process.exit(1);
    }

    process.stdout.write("Emitting IR...\n");

    try {
        const ibody = (((masm as MIRAssembly).functionDecls.get(section) as MIRFunctionDecl).invoke.body as MIRBody).body;
        const blocks = topologicalOrder(ibody as Map<string, MIRBasicBlock>);
        const flow = computeBlockLinks(ibody as Map<string, MIRBasicBlock>);
        console.log("Blocks:\n");
        console.log(blocks);
        console.log("Flow:\n");
        console.log(flow);
        process.exit(1);
    }
    catch (ex) {
        process.exit(1);
    }
}

getIRV("../test/apps/max/main.bsq", "NSMain::max");
