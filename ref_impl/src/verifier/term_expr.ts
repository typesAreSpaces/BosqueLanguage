//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as fs from "fs";
import { TypeExpr, FuncType } from "./type_expr";

abstract class TermExpr {
    readonly name : string;
    readonly symbolName : string;
    readonly ty : TypeExpr;
    static readonly symbolTable : Map<string, boolean> = new Map<string, boolean>();
    constructor(name : string, symbolName : string, ty : TypeExpr){
        this.name = name;
        this.symbolName = symbolName;
        this.ty = ty;
    }
    abstract toZ3Declaration(fd : number) : void;
    abstract sexpr() : string;
}

class VarExpr extends TermExpr {
    constructor(name : string, ty : TypeExpr){
        super(name, name, ty);
        VarExpr.symbolTable.set(this.name, false);
    }
    toZ3Declaration(fd : number){
        if(!VarExpr.symbolTable.get(this.symbolName)){
            fs.writeSync(fd, "(declare-fun " + this.symbolName + " () " + this.ty.getType() + ")\n");
            VarExpr.symbolTable.set(this.symbolName, true);
        }
    }
    sexpr(){
        return this.symbolName;
    }
}

class FuncExpr extends TermExpr {
    readonly terms : TermExpr[];
    constructor(name : string, ty : TypeExpr, terms : TermExpr[]){
        let collectType = new FuncType(terms.map(x => x.ty), ty);
        switch(terms.length){
            case 0: {
                super(name + "l__r", name, collectType);
                break;
            }   
            case 1: {
                super(name + "l_" + terms[0].name + "_r", name, collectType)
                break;
            }
            default: {
                super(name + "l_" + terms.slice(1).reduce((a, b) => a + "_" + b.name, terms[0].name) + "_r", name, collectType);
                break;  
            }
        }
        this.terms = terms;
        FuncExpr.symbolTable.set(this.symbolName, false);
    }
    toZ3Declaration(fd : number){
        for (let item of this.terms){
            item.toZ3Declaration(fd);
        }
        if(!FuncExpr.symbolTable.get(this.symbolName)){
            fs.writeSync(fd, "(declare-fun " + this.symbolName + " " + this.ty.getType() + ")\n");
            FuncExpr.symbolTable.set(this.symbolName, true);
        }
    }
    sexpr(){
        return "(" + this.symbolName + this.terms.reduce((a, b) => a + " " + b.sexpr(), "") + ")";
    }
}

export { TermExpr, VarExpr, FuncExpr };