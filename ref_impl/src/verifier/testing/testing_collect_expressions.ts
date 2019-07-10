//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { sanitizeName, bosqueToInvokeDecl } from "../util"
import { TranslatorBosqueFStar, FStarDeclaration } from "../translator_bosque_fstar";

setImmediate(() => {
    // Mac Machine
    // let directory = "/Users/joseabelcastellanosjoo/BosqueLanguage/ref_impl/src/test/apps/max/"
    // Windows Machine
    const directory = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/max/";
    const fileName = "main.bsq";
    const fkey = "NSMain::main";

    const mapDeclarations = bosqueToInvokeDecl({ directory: directory, fileName: fileName }); 
    let fstarFileName = (sanitizeName(fkey) + "_" + fileName).replace("bsq", "fst");
    fstarFileName = fstarFileName.charAt(0).toUpperCase() + fstarFileName.slice(1);

    const translation = new TranslatorBosqueFStar(mapDeclarations, fstarFileName);
    const fstarStackProgram = translation.collectExpr(fkey);

    fstarStackProgram.reverse();
    translation.printPrelude();
    while (fstarStackProgram.length > 0) {
        (fstarStackProgram.pop() as FStarDeclaration).print(translation.fd);
    }
    translation.closeFS();
});