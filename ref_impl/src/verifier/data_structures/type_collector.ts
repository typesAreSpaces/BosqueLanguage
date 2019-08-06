//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { TypeExpr } from "../type_expr"
import { sanitizeName } from "../util"
import { MIRArgument } from "../../compiler/mir_ops";
import { IgnoreTermStructuredAssignment } from "../../ast/body";

export class TypeCollector {
    readonly types = new Map<string, Set<TypeExpr> >();
    constructor() {
    }
    add(arg : MIRArgument, fkey : string, ty : TypeExpr){
        const nameID = sanitizeName(arg.nameID + fkey);
        const query = this.types.get(nameID);
        if(query == undefined){
            this.types.set(nameID, ty);
        }
        else{
            if(query != ty){

            }
        }
    }   
    get(arg : MIRArgument, fkey : string) : TypeExpr | undefined {
        const query = this.types.get(sanitizeName(arg.nameID + fkey));
        if(query !== undefined){ 
            return query;
        }   
        else{
            return undefined;
        }
    }
}