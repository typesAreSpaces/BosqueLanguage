//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as Path             from "path";
import { isEqual }           from "lodash"
import { MIRInvokeKey, 
  MIRBasicBlock, 
  NormalizationContext }     from "./../compiler/mir_ops"
import { MIRInvokeBodyDecl } from "./../compiler/mir_assembly"
import { bosqueToMASM }      from "./../verifier/typescript_files/util"

class Optimizer {

  ctx : NormalizationContext;

  constructor(){
    this.ctx = new Map<string, number>();
  }

  current_way_to_hash(block : MIRBasicBlock) : object {
    return block.ops.map(x => x.normalize(this.ctx));
  }

  areEqualMIRBasicBlock(block1 : MIRBasicBlock, block2 : MIRBasicBlock) : boolean {
    return isEqual(this.current_way_to_hash(block1), this.current_way_to_hash(block2));
  }

  areEqualMapMIRBasicBlock(map_b1 : Map<string, MIRBasicBlock>, map_b2 : Map<string, MIRBasicBlock>) : boolean {
    for(let [f_name, basic_block] of map_b1){
      const entry_second_map = map_b2.get(f_name);
      if(entry_second_map == undefined)
        return false;
      else{
        if(!this.areEqualMIRBasicBlock(basic_block, entry_second_map))
          return false;
      }
    }
    return true;
  }

  functionDeclsToRemove(invokeDecls : Map<MIRInvokeKey, MIRInvokeBodyDecl> ) 
    : Map<MIRInvokeKey, MIRInvokeKey> {
      const repr_funcs = new Set<MIRInvokeKey>();
      const to_remove  = new Map<MIRInvokeKey, MIRInvokeKey>();

      for(let [function_name, function_body_decl] of invokeDecls){
        let found = false;
        for(let repr_func of repr_funcs){
          // The following cannot be undefined, by construction
          const block = (invokeDecls.get(repr_func) as MIRInvokeBodyDecl).body.body;
          if(this.areEqualMapMIRBasicBlock(function_body_decl.body.body, block)){
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

  normalizeMapMIRBasicBlock(input : Map<string, MIRBasicBlock>) : Map<string , object> {
    const result = new Map<string, object>();
    input.forEach((value, key) => {
      result.set(key, value.ops.map(x => x.normalize(this.ctx)))
    });
    return result;
  }

  areEqualMapNormalizedMIRBasicBlock(map_b1 : Map<string, object>, map_b2 : Map<string, object>) : boolean {
    for(let [f_name, basic_block] of map_b1){
      const entry_second_map = map_b2.get(f_name);
      if(entry_second_map == undefined)
        return false;
      else{
        if(!isEqual(basic_block, entry_second_map))
          return false;
      }
    }
    return true;
  }

  functionDeclsToRemove2(invokeDecls : Map<MIRInvokeKey, MIRInvokeBodyDecl> ) 
    : Map<MIRInvokeKey, MIRInvokeKey> {
      const repr_funcs = new Set<MIRInvokeKey>();
      const to_remove  = new Map<MIRInvokeKey, MIRInvokeKey>();

      const normalized_invokeDecls = new Map<MIRInvokeKey, Map<string, object> >();

      invokeDecls.forEach((value, key) => {
        normalized_invokeDecls.set(key, this.normalizeMapMIRBasicBlock(value.body.body));
      });

      for(let [function_name, function_body_decl] of normalized_invokeDecls){
        let found = false;
        for(let repr_func of repr_funcs){
          // The following cannot be undefined, by construction
          const block = (normalized_invokeDecls.get(repr_func) as Map<string, object>);
          if(this.areEqualMapNormalizedMIRBasicBlock(function_body_decl, block)){
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

}

setImmediate(() => {

  const file_directory = Path.normalize(Path.join(__dirname, "./../../src/test/tests/optimizer"));
  const file_name = "simple_test.bsq";

  const masm = bosqueToMASM([`${file_directory}/${file_name}`], "cpp"); 

  if(masm !== undefined){
    //console.log(new Optimizer().functionDeclsToRemove(masm.invokeDecls));
    console.log(new Optimizer().functionDeclsToRemove2(masm.invokeDecls));

    process.stdout.write(`Done!\n`);
    process.exit(0);
  }

  process.stdout.write(`masm is undefined\n`);
  process.exit(1);  
});
