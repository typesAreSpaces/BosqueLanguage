//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as Path             from "path";
import { MIRInvokeKey }      from "./../compiler/mir_ops"
import { MIRBasicBlock }     from "./../compiler/mir_ops"
import { MIRInvokeBodyDecl } from "./../compiler/mir_assembly"
import { bosqueToMASM }      from "./../verifier/typescript_files/util"

export function compare_MIRInvokeBodyDecl(mir1 : MIRInvokeBodyDecl, mir2 : MIRInvokeBodyDecl) : boolean {
  // TODO: What should we include/exclude for this comparison?
  // TODO: Implement an appropriate comparison method for ops
  
  // Check if they have same signature
  if(mir1.resultType != mir2.resultType)
    return false;
  const sig_mir1 = mir1.params.map(x => x.type);
  const sig_mir2 = mir2.params.map(x => x.type);
  if(sig_mir1 != sig_mir2)
    return false;

  // Check if they have same body
  //mir1.body == ...
  mir1.body.body;

  return true;
}

// The following is wrong btw
function current_way_to_hash(block : MIRBasicBlock) {
  const block_json = block.jsonify();
  return block.label + block_json.ops.reduce((x, y) => x + y, "");
}

function areEqualMIRBasicBlock(block1 : MIRBasicBlock, block2 : MIRBasicBlock) : boolean {
  return current_way_to_hash(block1) == current_way_to_hash(block2);
}

function areEqualMapMIRBasicBlock(map_b1 : Map<string, MIRBasicBlock>, map_b2 : Map<string, MIRBasicBlock>) : boolean {
  for(let [f_name, basic_block] of map_b1){
    const entry_second_map = map_b2.get(f_name);
    if(entry_second_map == undefined)
      return false;
    else{
      if(!areEqualMIRBasicBlock(basic_block, entry_second_map))
        return false;
    }
  }
  return true;
}

function functionDeclsToRemove(invokeDecls : Map<MIRInvokeKey, MIRInvokeBodyDecl> ) : Map<MIRInvokeKey, MIRInvokeKey> {
  const repr_funcs = new Set<MIRInvokeKey>();
  const to_remove  = new Map<MIRInvokeKey, MIRInvokeKey>();

  for(let [function_name, function_body_decl] of invokeDecls){
    let found = false;
    for(let repr_func of repr_funcs){
      // The following cannot be undefined, by construction
      const block = (invokeDecls.get(repr_func) as MIRInvokeBodyDecl).body.body;
      if(areEqualMapMIRBasicBlock(function_body_decl.body.body, block)){
        to_remove.set(function_name, repr_func);
        found = true;
        break;
      }
    }
    if(found == false){
      repr_funcs.add(function_name);
    }
  }

  return to_remove;
}

setImmediate(() => {

  const file_directory = Path.normalize(Path.join(__dirname, "./../../src/test/tests/optimizer"));
  const file_name = "simple_test.bsq";

  const masm = bosqueToMASM([`${file_directory}/${file_name}`], "cpp"); 

  if(masm !== undefined){
    masm.invokeDecls.forEach((value, key) => {
      console.log(`--Key: ${key}`);
      console.log("Printing body elements");
      value.body.body.forEach((value, key) => {
        console.log(`----${key}`);
        console.log("----Ops")
        console.log("[");
        value.ops.map(x => {
          console.log(x);
        });
        console.log("]");
      });
      value.body.body.forEach(x => {
        console.log(`Hmm: ${current_way_to_hash(x)}`);
      });
    })

    console.log(functionDeclsToRemove(masm.invokeDecls));

    process.stdout.write(`Done!\n`);
    process.exit(0);
  }

  process.stdout.write(`masm is undefined\n`);
  process.exit(1);  
});
