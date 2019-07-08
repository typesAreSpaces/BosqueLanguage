//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import { sanitizeName, bosqueToInvokeDecl } from "../util"
import { TranslatorBosqueFStar } from "../translator_bosque_fstar";
import { ExprExpr } from "../expression_expr";

setImmediate(() => {
    // Mac Machine
    // let directory = "/Users/joseabelcastellanosjoo/BosqueLanguage/ref_impl/src/test/apps/max/"
    // Windows Machine
    let directory = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/max/";
    let fileName = "main.bsq";
    let mapDeclarations = bosqueToInvokeDecl({ directory: directory, fileName: fileName });
    let fkey = "NSMain::main";
    let fstarFileName = (sanitizeName(fkey) + "_" + fileName).replace("bsq", "fst");
    fstarFileName = fstarFileName.charAt(0).toUpperCase() + fstarFileName.slice(1);
    
    let fd = FS.openSync(fstarFileName, 'w');
    FS.writeSync(fd, `module ${fstarFileName}\n\n`);

    let translation = new TranslatorBosqueFStar(mapDeclarations);
    let fstarStackProgram = translation.collectExpr(fkey);
    fstarStackProgram.reverse();
    while (fstarStackProgram.length > 0) {
        let [funName, args, program] = (fstarStackProgram.pop() as [string, string[], ExprExpr]);
        FS.writeSync(fd, `let ${sanitizeName(funName)} ${args.join(" ")} = ${program.toML()}\n\n`);
    }
    FS.closeSync(fd);
});