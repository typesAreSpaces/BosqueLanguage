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
const cppdecls_emitter_1 = require("../../tooling/aot/cppdecls_emitter");
const chalk_1 = require("chalk");
const scratchroot = Path.normalize(Path.join(__dirname, "../../scratch/"));
const binroot = Path.normalize(Path.join(__dirname, "../../"));
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
    .option("-e --entrypoint [entrypoint]", "Entrypoint of the exe", "NSMain::main")
    .option("-o --outfile [outfile]", "Optional name of the output exe", (process.platform === "win32") ? "a.exe" : "a.out")
    .option("-c --compiler [compiler]", "Compiler to use", (process.platform === "win32") ? "\"C:\\Program Files\\LLVM\\bin\\clang.exe\"" : "g++")
    .option("-d --debug", "Build debug version", false);
Commander.parse(process.argv);
if (Commander.args.length === 0) {
    process.stdout.write(chalk_1.default.red("Error -- Please specify at least one source file as an argument\n"));
    process.exit(1);
}
console.log(`Compiling Bosque sources in files:\n${Commander.args.join("\n")}\n...\n`);
const massembly = generateMASM(Commander.args, Path.normalize(Path.join(__dirname, "../../", "core/direct/")));
setImmediate(() => {
    console.log(`Transpiling Bosque assembly to C++ with entrypoint of ${Commander.entrypoint}...`);
    const cpp_runtime = Path.join(binroot, "tooling/aot/runtime/");
    try {
        const cparams = cppdecls_emitter_1.CPPEmitter.emit(massembly, Commander.entrypoint);
        const lsrc = FS.readdirSync(cpp_runtime).filter((name) => name.endsWith(".h") || name.endsWith(".cpp"));
        const linked = lsrc.map((fname) => {
            const contents = FS.readFileSync(Path.join(cpp_runtime, fname)).toString();
            const bcontents = contents
                .replace("//%%NOMINAL_TYPE_ENUM_DECLARE", "    " + cparams.nominalenums)
                .replace("//%%CONCEPT_SUBTYPE_RELATION_DECLARE", "    " + cparams.conceptSubtypeRelation)
                .replace("//%%STATIC_STRING_DECLARE%%", "  " + cparams.conststring_declare)
                .replace("//%%STATIC_STRING_CREATE%%", "  " + cparams.conststring_create)
                .replace("//%%STATIC_INT_DECLARE%%", "  " + cparams.constint_declare)
                .replace("//%%STATIC_INT_CREATE%%", "  " + cparams.constint_create)
                .replace("//%%PROPERTY_ENUM_DECLARE", "    " + cparams.propertyenums)
                .replace("//%%PROPERTY_NAMES", "  " + cparams.propertynames)
                .replace("//%%KNOWN_PROPERTY_LIST_DECLARE", "    " + cparams.known_property_lists_declare)
                .replace("//%%VFIELD_DECLS", "    " + cparams.vfield_decls)
                .replace("//%%VMETHOD_DECLS", "  " + cparams.vmethod_decls);
            return { file: fname, contents: bcontents };
        });
        if (massembly.invokeDecls.get(Commander.entrypoint) === undefined) {
            process.stderr.write("Could not find specified entrypoint!!!\n");
            process.exit(1);
        }
        const entrypoint = massembly.invokeDecls.get(Commander.entrypoint);
        if (entrypoint.params.some((p) => p.type !== "NSCore::Bool" && p.type !== "NSCore::Int" && p.type !== "NSCore::String")) {
            process.stderr.write("Only Bool/Int/String are supported as inputs for Bosque binaries.\n");
            process.exit(1);
        }
        const maincpp = "#include \"bsqruntime.h\"\n"
            + "namespace BSQ\n"
            + "{\n/*forward type decls*/\n"
            + cparams.typedecls_fwd
            + "\n\n/*forward function decls*/\n"
            + cparams.funcdecls_fwd
            + "\n\n/*type decls*/\n"
            + cparams.typedecls
            + "\n\n/*typecheck decls*/\n"
            + cparams.typechecks
            + "\n\n/*function decls*/\n"
            + cparams.funcdecls
            + "}\n\n"
            + "using namespace BSQ;"
            + "\n\n/*main decl*/\n"
            + cparams.maincall;
        linked.push({ file: "main.cpp", contents: maincpp });
        console.log(`Writting C++ files...`);
        const cpppath = Path.join(scratchroot, "cpp");
        FS.mkdirSync(cpppath, { recursive: true });
        linked.forEach((fp) => {
            const outfile = Path.join(cpppath, fp.file);
            FS.writeFileSync(outfile, fp.contents);
        });
        console.log(`Compiling C++ code with ${Commander.compiler} into exe file "${chalk_1.default.bold(Commander.outfile)}"...`);
        child_process_1.execSync(`${Commander.compiler}${Commander.debug ? " -g -DBDEBUG" : " -Os"} -std=c++14 -o ${Commander.outfile} ${cpppath}/*.cpp`);
    }
    catch (ex) {
        process.stderr.write(chalk_1.default.red(`Error -- ${ex}\n`));
    }
    console.log(chalk_1.default.green(`Done with executable -- ${Commander.outfile}`));
});
//# sourceMappingURL=exegen.js.map