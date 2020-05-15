//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as Path from "path";
import { bosqueToMASM } from "./util"
import { TranslatorBosqueFStar } from "./translator_bosque_fstar";

setImmediate(() => {

  const file_directory = Path.normalize(Path.join(__dirname, "./../../../src/test/apps/max"));
  const file_name = "main.bsq";
  const fkey = "NSMain::main";

  const masm = bosqueToMASM([`${file_directory}/${file_name}`], "cpp"); 

  const fstar_file_name = (fkey + "_" + file_name)
    .replace("bsq", "fst")
    .replace(new RegExp("#", 'g'), "_")
    .replace(new RegExp("\\$", 'g'), "_")
    .replace(new RegExp(":", 'g'), "_");

  if(masm !== undefined){

    const translator = new TranslatorBosqueFStar(masm, fstar_file_name);

    translator.generateFStarCode(fkey); 
    //translator.runFStarCode(20, 15, 5);

    process.stdout.write(`Done!\n`);
    process.exit(0);
  }

  process.stdout.write(`masm is undefined\n`);
  process.exit(1);  

});
