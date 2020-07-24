//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as Path             from "path";
import { bosqueToMASM }      from "./../verifier/typescript_files/util"
import { MASMOptimizer }     from "./masm_optimizer"
  
setImmediate(() => {

  const file_directory = Path.normalize(Path.join(__dirname, "./../../src/test/tests/optimizer"));
  const file_name = "simple_test.bsq";

  const masm = bosqueToMASM([`${file_directory}/${file_name}`], "cpp"); 

  if(masm !== undefined){
    const to_remove = new MASMOptimizer(masm).functionDeclsToRemove();
    console.log(to_remove);
    //console.log(new MASMOptimizer(masm).functionDeclsToRemove2());
    masm.simplify(to_remove);
    //console.log(masm.invokeDecls);

    process.stdout.write(`Done!\n`);
    process.exit(0);
  }

  process.stdout.write(`masm is undefined\n`);
  process.exit(1);  
});

export { MASMOptimizer };
