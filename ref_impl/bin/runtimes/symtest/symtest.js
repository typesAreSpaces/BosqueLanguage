"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const FS = require("fs");
const Path = require("path");
const child_process_1 = require("child_process");
const Commander = require("commander");
const mir_assembly_1 = require("../../compiler/mir_assembly");
const mir_emitter_1 = require("../../compiler/mir_emitter");
const smtdecls_emitter_1 = require("../../tooling/bmc/smtdecls_emitter");
const chalk_1 = require("chalk");
const binroot = Path.normalize(Path.join(__dirname, "../../"));
let platpathsmt = undefined;
if (process.platform === "win32") {
    platpathsmt = "bin/win/z3.exe";
}
else if (process.platform === "linux") {
    platpathsmt = "bin/linux/z3";
}
else {
    platpathsmt = "bin/macos/z3";
}
const z3path = Path.normalize(Path.join(__dirname, "../../tooling/bmc/runtime", platpathsmt));
function generateMASM(files, corelibpath) {
    let code = [];
    try {
        const coredir = Path.join(corelibpath, "/core.bsq");
        const coredata = FS.readFileSync(coredir).toString();
        const collectionsdir = Path.join(corelibpath, "/collections.bsq");
        const collectionsdata = FS.readFileSync(collectionsdir).toString();
        code = [{ relativePath: coredir, contents: coredata }, { relativePath: collectionsdir, contents: collectionsdata }];
        for (let i = 0; i < files.length; ++i) {
            const file = { relativePath: files[i], contents: FS.readFileSync(files[i]).toString() };
            code.push(file);
        }
    }
    catch (ex) {
        process.stdout.write(chalk_1.default.red(`Read failed with exception -- ${ex}\n`));
        process.exit(1);
    }
    const { masm, errors } = mir_emitter_1.MIREmitter.generateMASM(new mir_assembly_1.PackageConfig(), true, true, true, code);
    if (errors.length !== 0) {
        for (let i = 0; i < errors.length; ++i) {
            process.stdout.write(chalk_1.default.red(`Parse error -- ${errors[i]}\n`));
        }
        process.exit(1);
    }
    return masm;
}
Commander
    .option("-e --entrypoint [entrypoint]", "Entrypoint to symbolically test", "NSMain::main")
    .option("-m --model", "Try to get model for failing inputs", false)
    .option("-b --bound [size]", "Bound for testing", 4)
    .option("-o --output [file]", "Output the model to a given file");
Commander.parse(process.argv);
if (Commander.args.length === 0) {
    process.stdout.write(chalk_1.default.red("Error -- Please specify at least one source file as an argument\n"));
    process.exit(1);
}
console.log(`Symbolic testing of Bosque sources in files:\n${Commander.args.join("\n")}\n...\n`);
const massembly = generateMASM(Commander.args, Path.normalize(Path.join(__dirname, "../../", "core/direct/")));
setImmediate(() => {
    console.log(`Transpiling Bosque assembly to bytecode with entrypoint of ${Commander.entrypoint}...`);
    const smt_runtime = Path.join(binroot, "tooling/bmc/runtime/smtruntime.smt2");
    try {
        if (massembly.invokeDecls.get(Commander.entrypoint) === undefined) {
            process.stderr.write(chalk_1.default.red("Could not find specified entrypoint!!!\n"));
            process.exit(1);
        }
        const entrypoint = massembly.invokeDecls.get(Commander.entrypoint);
        if (entrypoint.params.some((p) => p.type !== "NSCore::Bool" && p.type !== "NSCore::Int" && p.type !== "NSCore::String")) {
            process.stderr.write("Only Bool/Int/String are supported as inputs for symbolic testing of Bosque programs.\n");
            process.exit(1);
        }
        const sparams = smtdecls_emitter_1.SMTEmitter.emit(massembly, entrypoint, Commander.bound, true);
        const lsrc = FS.readFileSync(smt_runtime).toString();
        const contents = lsrc
            .replace(";;FIXED_TUPLE_DECLS_FWD;;", "  " + sparams.fixedtupledecls_fwd)
            .replace(";;FIXED_RECORD_DECLS_FWD;;", "  " + sparams.fixedrecorddecls_fwd)
            .replace(";;FIXED_TUPLE_DECLS;;", "  " + sparams.fixedtupledecls)
            .replace(";;FIXED_RECORD_DECLS;;", "  " + sparams.fixedrecorddecls)
            .replace(";;NOMINAL_DECLS_FWD;;", "  " + sparams.typedecls_fwd)
            .replace(";;NOMINAL_DECLS;;", "  " + sparams.typedecls)
            .replace(";;CONCEPT_SUBTYPE_RELATION_DECLARE;;", sparams.conceptSubtypeRelation)
            .replace(";;NOMINAL_RESULT_FWD;;", "  " + sparams.resultdecls_fwd)
            .replace(";;NOMINAL_RESULT;;", "  " + sparams.resultdecls)
            .replace(";;SUBTYPE_DECLS;;", sparams.typechecks)
            .replace(";;FUNCTION_DECLS;;", "  " + sparams.function_decls)
            .replace(";;ARG_VALUES;;", sparams.args_info)
            .replace(";;INVOKE_ACTION;;", sparams.main_info)
            .replace(";;GET_MODEL;;", Commander.model ? "(get-model)" : "");
        console.log(`Running z3 on SMT encoding...`);
        if (Commander.output) {
            try {
                console.log(`Writing SMT output to "${Commander.output}..."`);
                FS.writeFileSync(Commander.output, contents);
            }
            catch (fex) {
                console.log(chalk_1.default.red(`Failed to write file -- ${fex}.`));
            }
        }
        try {
            const res = child_process_1.execSync(`${z3path} -smt2 -in`, { input: contents }).toString().trim();
            if (res === "unsat") {
                console.log(chalk_1.default.green("Verified up to bound -- no errors found!"));
            }
            else {
                console.log(chalk_1.default.red("Detected possible errors!"));
                if (!Commander.model) {
                    console.log("Rerun with '-m' flag to attempt to generate failing inputs.");
                }
                else {
                    console.log("Attempting to extract inputs...");
                    const splits = res.split("\n");
                    const inputs = entrypoint.params.map((p) => {
                        const ridx = splits.findIndex((str) => str.trim().startsWith(`(define-fun @${p.name}`));
                        if (ridx === -1) {
                            return `${p.name} = ??`;
                        }
                        else {
                            const mres = splits[ridx + 1].trim();
                            return `${p.name} = ${mres.substring(0, mres.length - 1).trim()}`;
                        }
                    });
                    console.log(inputs.join("\n"));
                }
            }
        }
        catch (exx) {
            if (Commander.model) {
                console.log("Cannot generate model '-m' as errors were not found?");
            }
            else {
                throw exx;
            }
        }
    }
    catch (ex) {
        process.stderr.write(chalk_1.default.red(`Error -- ${ex}\n`));
    }
});
//# sourceMappingURL=symtest.js.map