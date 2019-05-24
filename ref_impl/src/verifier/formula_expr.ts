//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

// import * as deepEqual from "deep-equal"
import * as fs from "fs"

abstract class TypeExpr {
}

class IntType extends TypeExpr {
}


class BoolType extends TypeExpr {
}


class StringType extends TypeExpr {
}

// TODO: Add more elements to the 
// abstract class TypeExpr once we 
// have formalized the type system
// for Bosque. Actually, it is already
// established on the documentation,
// however, it needs additional formalization
// to deal with some rules and inference
// (Current approach to accomplish the latter: take 
// the grouded ast and build a `table' using

abstract class TermExpr {
    readonly name: string;
    readonly ty : TypeExpr;
    static readonly symbolTable : Map<string, TypeExpr> = new Map<String, TypeExpr>();
    constructor(name : string, ty : TypeExpr){
        this.name = name;
        this.ty = ty;
    }
    abstract toZ3(fd : number) : void;
}

class VarExpr extends TermExpr {
    constructor(name : string, ty : TypeExpr){
        super(name, ty);
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class FuncExpr extends TermExpr {
    readonly terms : TermExpr[];
    constructor(name : string, terms : TermExpr[]){
        switch(terms.length){
            case 0: {
                super(name + "()", ty);
                break;
            }   
            case 1: {
                super(name + "(" + terms[0].name + ")")
                break;
            }
            default: {
                super(name + "(" + terms.slice(1).reduce((a, b) => a + "," + b.name, terms[0].name) + ")");
                break;  
            }
        }
        this.terms = terms;
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

abstract class FormulaExpr {
    static fsFormula = require('fs');
    readonly name : string;
    constructor(name : string){
        this.name = name;
    }
    abstract toZ3(fd : number) : void;
}

class PredicateExpr extends FormulaExpr {
    readonly terms : TermExpr[];
    constructor(name : string, terms : TermExpr[]){
        switch(terms.length){
            case 0: {
                super(name + "()");
                break;
            }   
            case 1: {
                super(name + "(" + terms[0].name + ")")
                break;
            }
            default: {
                super(name + "(" + terms.slice(1).reduce((a, b) => a + "," + b.name, terms[0].name) + ")");
                break;  
            }
        }
        this.terms = terms;
        this.terms = terms;
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class EqualityExpr extends FormulaExpr {
    readonly leftHandSide : TermExpr;
    readonly rightHandSide : TermExpr;
    constructor(left : TermExpr, right : TermExpr){
        super(left.name + "=" + right.name);
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class NegExpr extends FormulaExpr {
    readonly formula : FormulaExpr;
    constructor(formula : FormulaExpr){
        super("neg " + formula.name);
        this.formula = formula;
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class AndExpr extends FormulaExpr {
    readonly leftHandSide : FormulaExpr;
    readonly rightHandSide : FormulaExpr;
    constructor(left : FormulaExpr, right : FormulaExpr){
        super(left.name + " and " + right.name);
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class OrExpr extends FormulaExpr {
    readonly leftHandSide : FormulaExpr;
    readonly rightHandSide : FormulaExpr;
    constructor(left : FormulaExpr, right : FormulaExpr){
        super(left.name + " or " + right.name);
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class ImplExpr extends FormulaExpr {
    readonly leftHandSide : FormulaExpr;
    readonly rightHandSide : FormulaExpr;
    constructor(left : FormulaExpr, right : FormulaExpr){
        super(left.name + " implies " + right.name);
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class ForAllExpr extends FormulaExpr {
    readonly nameBinder : VarExpr;
    readonly formula : FormulaExpr;
    constructor(nameBinder : VarExpr, formula : FormulaExpr){
        super("forall " + nameBinder.name + ".(" + formula.name + ")");
        this.nameBinder = nameBinder;
        this.formula = formula;
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class ExistsExpr extends FormulaExpr { 
    readonly nameBinder : VarExpr;
    readonly formula : FormulaExpr;
    constructor(nameBinder : VarExpr, formula : FormulaExpr){
        super("exists " + nameBinder.name + ".(" + formula.name + ")");
        this.nameBinder = nameBinder;
        this.formula = formula;
    }
    toZ3(fd : number) : void {
       fs.writeSync(fd, this.name + '\n');  
    }
}

// Testing
let x = new VarExpr("x");
let x2 = new VarExpr("x");
let y = new VarExpr("y");
let p = new PredicateExpr("p", [x, y]);
let not_p = new NegExpr(p);
let fxy = new FuncExpr("f", [x, y]);
let extraLong = new ForAllExpr(x, new ForAllExpr(y, new PredicateExpr("p", [fxy, x, x, y, fxy, x])));

// console.log("Examples---");
// console.log(x);
// console.log(p);
// console.log(not_p);
// console.log(fxy);
// console.log(new FuncExpr("g", [x, y, x, x, x]));
// console.log(new FuncExpr("g", [x]));
// console.log(new FuncExpr("g", []));
// console.log(new ForAllExpr(x, p));
// console.log("Ok---");

// // Testing equality
// console.log("is x equal to x2?");
// console.log(deepEqual(x, x2));
// console.log("is forall x . p equal to forall x2 . p");
// console.log(deepEqual(new ForAllExpr(x, p), new ForAllExpr(x2, p)));

// // Writing on a file
// // So we can use Z3 
// console.log('Testing writing on file');
// let fd = fs.openSync('file.z3', 'w');
// extraLong.toZ3(fd);
// fs.closeSync(fd);
// // Passed tests!