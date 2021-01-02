//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as Commander from "commander";
import { bosqueToMASM }      from "./../verifier/typescript_files/util"
import { MASMOptimizer }     from "./masm_optimizer"
  
Commander.parse(process.argv);

setImmediate(() => {

  const masm = bosqueToMASM(Commander.args, "cpp"); 

  if(masm !== undefined){
    const to_remove = new MASMOptimizer(masm).functionDeclsToRemove();
    console.log(to_remove);
    masm.simplify(to_remove);

    process.stdout.write(`Done!\n`);
    process.exit(0);
  }

  process.stdout.write(`masm is undefined\n`);
  process.exit(1);  
});

export { MASMOptimizer };
