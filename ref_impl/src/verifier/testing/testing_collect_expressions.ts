//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { sanitizeName, bosqueToMASM } from "../util"
import { TranslatorBosqueFStar } from "../translator_bosque_fstar";

setImmediate(() => {
    
    // Mac Machine
    const directory = "/Users/joseabelcastellanosjoo/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/max/"
    const fstar_files_directory = "/Users/joseabelcastellanosjoo/Documents/GithubProjects/BosqueLanguage/ref_impl/src/verifier/fstar_files/";
    // const directory = "/Users/joseabelcastellanosjoo/BosqueLanguage/ref_impl/src/test/apps/tictactoe/"

    // Windows Machine
    // const directory = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/max/";
    // const directory = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/tictactoe/";
    
    // Linux Machine 
    // const directory = "/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/max/";
    // const fstar_files_directory = "/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/verifier/fstar_files/";
    // const directory = "/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/tictactoe/";

    const fileName = "main.bsq";
    const fkey = "NSMain::main";
    const masm = bosqueToMASM({ directory: directory, fileName: fileName }); 
    const fstarFileName = (sanitizeName(fkey) + "_" + fileName).replace("bsq", "fst");
    const translator = new TranslatorBosqueFStar(masm, fstarFileName.charAt(0).toUpperCase() + fstarFileName.slice(1), fstar_files_directory);

    translator.generateFStarCode(fkey);
});