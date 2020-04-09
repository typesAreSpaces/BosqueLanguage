//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { sanitizeName, bosqueToMASM } from "./util"
import { TranslatorBosqueFStar } from "./translator_bosque_fstar";

setImmediate(() => {
    
    // Mac Machine
    // const file_directory = "/Users/joseabelcastellanosjoo/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/max/"
    // const file_directory = "/Users/joseabelcastellanosjoo/BosqueLanguage/ref_impl/src/test/apps/tictactoe/"

    // Windows Machine
    // const file_directory = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/max/";
    // const file_directory = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/tictactoe/";
    
    // Linux Machine 
    const file_directory = "/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/max/";
    // const file_directory = "/home/jose/Documents/GithubProjects/BosqueLanguage/ref_impl/src/test/apps/tictactoe/";
    const file_name = "main.bsq";
    const fkey = "NSMain::main";

    const masm = bosqueToMASM({ file_directory: file_directory, file_name: file_name }); 

    const fstarFileName = (sanitizeName(fkey) + "_" + file_name).replace("bsq", "fst");

    const translator = new TranslatorBosqueFStar(masm, fstarFileName.charAt(0).toUpperCase() + fstarFileName.slice(1));

    translator.generateFStarCode(fkey, 20, 15, 5); 
});
