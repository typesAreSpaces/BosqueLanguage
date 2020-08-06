//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { isEqual }           from "lodash"
import * as assert           from "assert";
import { MIRInvokeKey, 
  MIRBasicBlock, 
  NormalizationContext }     from "./../compiler/mir_ops"
import { MIRInvokeBodyDecl,
  MIRAssembly}               from "./../compiler/mir_assembly"

class MASMOptimizer {

  ctx  : NormalizationContext;
  masm : MIRAssembly;

  constructor(masm : MIRAssembly){
    this.ctx = new Map<string, number>();
    this.masm = masm;
  }

  private normalizeMIRBasicBlock(block : MIRBasicBlock) : object {
    return block.ops.map(x => x.normalize(this.ctx));
  }

  private areEqualMIRBasicBlock(block1 : MIRBasicBlock, block2 : MIRBasicBlock) : boolean {
    return isEqual(this.normalizeMIRBasicBlock(block1), this.normalizeMIRBasicBlock(block2));
  }

  private areEqualMapMIRBasicBlock(map_b1 : Map<string, MIRBasicBlock>, map_b2 : Map<string, MIRBasicBlock>) : boolean {
    for(let [f_name, entry_b1] of map_b1){
      const entry_b2 = map_b2.get(f_name);
      if(entry_b2 == undefined)
        return false;
      else{
        if(!this.areEqualMIRBasicBlock(entry_b1, entry_b2))
          return false;
      }
    }
    return true;
  }

  functionDeclsToRemove() : Map<MIRInvokeKey, MIRInvokeKey> {

      const repr_funcs = new Set<MIRInvokeKey>();
      const to_remove  = new Map<MIRInvokeKey, MIRInvokeKey>();

      for(let [function_name, newest_invoke_decl] of this.masm.invokeDecls){
        let found = false;
        for(let repr_func of repr_funcs){
          // The following cannot be undefined, by construction
          const previous_invoke_decl = this.masm.invokeDecls.get(repr_func) as MIRInvokeBodyDecl;
          assert(previous_invoke_decl instanceof MIRInvokeBodyDecl);
          //console.log("--START");
          //console.log(function_name);
          //console.log(repr_func);
          //console.log("--END");
          if(this.areEqualMapMIRBasicBlock(newest_invoke_decl.body.body, previous_invoke_decl.body.body) 
          // Be careful with the comparision, these are Object in javascript i.e. comparision takes into consider some pointer logic
          //&& isEqual(newest_invoke_decl.enclosingDecl, previous_invoke_decl.enclosingDecl) // Dont include this one!
          //&& isEqual(newest_invoke_decl.key, previous_invoke_decl.key) // Dont include this one!
          //&& isEqual(newest_invoke_decl.attributes , previous_invoke_decl.attributes)
          && isEqual(newest_invoke_decl.recursive , previous_invoke_decl.recursive)
          //&& isEqual(newest_invoke_decl.pragmas , previous_invoke_decl.pragmas)
          && isEqual(newest_invoke_decl.params.map(x => x.type) , previous_invoke_decl.params.map(x => x.type))
          && isEqual(newest_invoke_decl.resultType , previous_invoke_decl.resultType)
          ){
            to_remove.set(function_name, repr_func);
            found = true;
            break;
          }
        }
        if(found == false)
          repr_funcs.add(function_name);
      }
      return to_remove;
    }

  private normalizeMapMIRBasicBlock(input : Map<string, MIRBasicBlock>) : Map<string , object> {
    const result = new Map<string, object>();
    input.forEach((value, key) => {
      result.set(key, value.ops.map(x => x.normalize(this.ctx)))
    });
    return result;
  }

  private areEqualMapNormalizedMIRBasicBlock(map_b1 : Map<string, object>, map_b2 : Map<string, object>) : boolean {
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

  functionDeclsToRemove2() : Map<MIRInvokeKey, MIRInvokeKey> {
      const repr_funcs = new Set<MIRInvokeKey>();
      const to_remove  = new Map<MIRInvokeKey, MIRInvokeKey>();

      const normalized_invokeDecls = new Map<MIRInvokeKey, Map<string, object> >();

      this.masm.invokeDecls.forEach((value, key) => {
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
        if(found == false)
          repr_funcs.add(function_name);
      }

      return to_remove;
    }
}

export { MASMOptimizer } ;
