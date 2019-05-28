//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import * as Path from "path";
import chalk from "chalk";
import { MIREmitter } from "../compiler/mir_emitter";
import { PackageConfig, MIRAssembly, MIRFunctionDecl } from "../compiler/mir_assembly";
import { MIRBody, MIRBasicBlock, MIROpTag } from "../compiler/mir_ops";
import { } from "../compiler/mir_ssa";
import { topologicalOrder, computeBlockLinks } from "../compiler/ir_info";
import assert = require("assert");

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

    blocks.map(block => block.ops.map(op => {
        switch (op.tag) {
            case MIROpTag.LoadConst:
            case MIROpTag.LoadConstTypedString:
            case MIROpTag.AccessNamespaceConstant:
            case MIROpTag.AccessConstField:
            case MIROpTag.LoadFieldDefaultValue: {
                break;
            }
            case MIROpTag.AccessCapturedVariable: {
                break;
            }
            case MIROpTag.AccessArgVariable: {
                break;
            }
            case MIROpTag.AccessLocalVariable: {
                break;
            }
            case MIROpTag.ConstructorPrimary: {
                break;
            }
            case MIROpTag.ConstructorPrimaryCollectionEmpty: {
                break;
            }
            case MIROpTag.ConstructorPrimaryCollectionSingletons: {
                break;
            }
            case MIROpTag.ConstructorPrimaryCollectionCopies: {
                break;
            }
            case MIROpTag.ConstructorPrimaryCollectionMixed: {
                break;
            }
            case MIROpTag.ConstructorTuple: {
                break;
            }
            case MIROpTag.ConstructorRecord: {
                break;
            }
            case MIROpTag.ConstructorLambda: {
                break;
            }
            case MIROpTag.CallNamespaceFunction: {
                break;
            }
            case MIROpTag.CallStaticFunction: {
                break;
            }
            case MIROpTag.MIRAccessFromIndex: {
                break;
            }
            case MIROpTag.MIRProjectFromIndecies: {
                break;
            }
            case MIROpTag.MIRAccessFromProperty: {
                break;
            }
            case MIROpTag.MIRProjectFromProperties: {
                break;
            }
            case MIROpTag.MIRAccessFromField: {
                break;
            }
            case MIROpTag.MIRProjectFromFields: {
                break;
            }
            case MIROpTag.MIRProjectFromTypeTuple: {
                break;
            }
            case MIROpTag.MIRProjectFromTypeRecord: {
                break;
            }
            case MIROpTag.MIRProjectFromTypeConcept: {
                break;
            }
            case MIROpTag.MIRModifyWithIndecies: {
                break;
            }
            case MIROpTag.MIRModifyWithProperties: {
                break;
            }
            case MIROpTag.MIRModifyWithFields: {
                break;
            }
            case MIROpTag.MIRStructuredExtendTuple: {
                break;
            }
            case MIROpTag.MIRStructuredExtendRecord: {
                break;
            }
            case MIROpTag.MIRStructuredExtendObject: {
                break;
            }
            case MIROpTag.MIRInvokeKnownTarget: {
                break;
            }
            case MIROpTag.MIRInvokeVirtualTarget: {
                break;
            }
            case MIROpTag.MIRCallLambda: {
                break;
            }
            case MIROpTag.MIRPrefixOp: {
                break;
            }
            case MIROpTag.MIRBinOp: {
                break;
            }
            case MIROpTag.MIRBinEq: {
                break;
            }
            case MIROpTag.MIRBinCmp: {
                break;
            }
            case MIROpTag.MIRRegAssign: {
                break;
            }
            case MIROpTag.MIRTruthyConvert: {
                break;
            }
            case MIROpTag.MIRVarStore: {
                break;
            }
            case MIROpTag.MIRReturnAssign: {
                break;
            }
            case MIROpTag.MIRAssert: {
                break;
            }
            case MIROpTag.MIRCheck: {
                break;
            }
            case MIROpTag.MIRDebug: {
                break;
            }
            case MIROpTag.MIRJump: {
                break;
            }
            case MIROpTag.MIRJumpCond: {
                break;
            }
            case MIROpTag.MIRJumpNone: {
                break;
            }
            case MIROpTag.MIRVarLifetimeStart:
            case MIROpTag.MIRVarLifetimeEnd: {
                break;
            }
            default:
                assert(false);
                break;
        }
    }
    ));

}

////
//Entrypoint

// Mac Machine
// let bosqueFile = "/Users/joseabelcastellanosjoo/BosqueLanguage/ref_impl/src/test/apps/max/main.bsq"

// Windows Machine
let bosqueFile = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/max/main.bsq";

let section = "NSMain::max";
setImmediate(() => getControlFlow(bosqueFile, section));