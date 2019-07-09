//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import { sanitizeName, bosqueToInvokeDecl } from "../util"
import { TranslatorBosqueFStar, FStarDeclaration } from "../translator_bosque_fstar";

setImmediate(() => {
    // Mac Machine
    let directory = "/Users/joseabelcastellanosjoo/BosqueLanguage/ref_impl/src/test/apps/max/"
    // Windows Machine
    // let directory = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/max/";
    let fileName = "main.bsq";
    let mapDeclarations = bosqueToInvokeDecl({ directory: directory, fileName: fileName });
    let fkey = "NSMain::main";
    let fstarFileName = (sanitizeName(fkey) + "_" + fileName).replace("bsq", "fst");
    fstarFileName = fstarFileName.charAt(0).toUpperCase() + fstarFileName.slice(1);
    
    let fd = FS.openSync(fstarFileName, 'w');
    FS.writeSync(fd, `module ${fstarFileName.slice(0, -4)}\n\n`);

    let translation = new TranslatorBosqueFStar(mapDeclarations);
    let fstarStackProgram = translation.collectExpr(fkey);
    fstarStackProgram.reverse();
    while (fstarStackProgram.length > 0) {
        let currentDeclaration = fstarStackProgram.pop() as FStarDeclaration;
        FS.writeSync(fd, currentDeclaration.printVal());
        FS.writeSync(fd, currentDeclaration.printLet());
    }
    FS.closeSync(fd);
});