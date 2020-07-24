//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as Path from "path";
import { bosqueToMASM } from "./util"
import { TranslatorBosqueFStar } from "./translator_bosque_fstar";
import { MASMOptimizer  } from "../../optimizer/masm_optimizer"

setImmediate(() => {

  const file_directory = Path.normalize(Path.join(__dirname, "./../../../src/test/apps/max"));
  //const file_name = "simple_main.bsq";
  const file_name = "main.bsq";
  const fkey = "NSMain::main";

  const masm = bosqueToMASM([`${file_directory}/${file_name}`], "cpp"); 

  const fstar_file_name = (fkey + "_" + file_name)
    .replace(new RegExp("#", 'g'), "_")
    .replace(new RegExp("\\$", 'g'), "_")
    .replace(new RegExp(":", 'g'), "_")
    .replace("bsq", "fst");

  if(masm !== undefined){

    const to_remove = new MASMOptimizer(masm).functionDeclsToRemove();
    masm.invokeDecls.forEach((value, key) => {
      console.log("----New entry");
      console.log(key);
      console.log(value);
      console.log(value.body)});
    console.log("------ To remove");
    console.log(to_remove);
    masm.simplify(to_remove);

    const translator = new TranslatorBosqueFStar(masm, fstar_file_name);

    translator.generateFStarCode(fkey); 
    //translator.runFStarCode(20, 15, 5);

    process.stdout.write(`Done!\n`);
    process.exit(0);
  }

  process.stdout.write(`masm is undefined\n`);
  process.exit(1);  

});
