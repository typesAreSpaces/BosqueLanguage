//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as Commander from "commander";
import { bosqueToMASM } from "./util"
import { TranslatorBosqueFStar } from "./translator_bosque_fstar";
import { MASMOptimizer  } from "../../optimizer/masm_optimizer"

Commander
  .option("-e --entrypoint [entrypoint]", "Entrypoint to symbolically test", "NSMain::main")
Commander.parse(process.argv);

setImmediate(() => {

  const first_file_name = Commander.args[0];
  const file_name = first_file_name.substring(first_file_name.lastIndexOf('/') + 1);

  const masm = bosqueToMASM(Commander.args, "cpp"); 

  const fstar_file_name = (Commander.entrypoint + "_" + file_name)
    .replace(new RegExp("#", 'g'), "_")
    .replace(new RegExp("\\$", 'g'), "_")
    .replace(new RegExp(":", 'g'), "_")
    .replace("bsq", "fst");

  if(masm !== undefined){

    const to_remove = new MASMOptimizer(masm).functionDeclsToRemove();
    masm.simplify(to_remove);

    const translator = new TranslatorBosqueFStar(masm, fstar_file_name);

    translator.generateFStarCode(Commander.entrypoint); 
    // Comment/Uncomment to let fstar check the output file
    //translator.runFStarCode(20, 15, 5);

    process.stdout.write(`Done!\n`);
    process.exit(0);
  }

  process.stdout.write(`masm is undefined\n`);
  process.exit(1);  

});
