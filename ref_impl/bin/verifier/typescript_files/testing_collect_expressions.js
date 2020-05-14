"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const util_1 = require("./util");
const translator_bosque_fstar_1 = require("./translator_bosque_fstar");
setImmediate(() => {
    // Mac Machine
    // const directory = "/Users/joseabelcastellanosjoo/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/max/"
    // const fstar_files_directory = "/Users/joseabelcastellanosjoo/Documents/GithubProjects/BosqueLanguage/ref_impl/src/verifier/fstar_files/";
    // const directory = "/Users/joseabelcastellanosjoo/BosqueLanguage/ref_impl/src/test/apps/tictactoe/"
    // Windows Machine
    // const directory = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/max/";
    // const directory = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/tictactoe/";
    // Linux Machine 
    const directory = "/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/max/";
    const fstar_files_directory = "/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/verifier/fstar_files/";
    // const directory = "/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/tictactoe/";
    const fileName = "main.bsq";
    const fkey = "NSMain::main";
    const fstarFileName = (util_1.sanitizeName(fkey) + "_" + fileName).replace("bsq", "fst");
    const masm = util_1.bosqueToMASM({ directory: directory, fileName: fileName });
    const translator = new translator_bosque_fstar_1.TranslatorBosqueFStar(masm, fstarFileName.charAt(0).toUpperCase() + fstarFileName.slice(1), fstar_files_directory);
    translator.generateFStarCode(fkey, 20, 15, 5);
});
//# sourceMappingURL=testing_collect_expressions.js.map