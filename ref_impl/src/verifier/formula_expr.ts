//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

// import * as deepEqual from "deep-equal"
import * as fs from "fs"

abstract class TypeExpr {
    abstract getType() : string;
}

class IntType extends TypeExpr {
    getType() {
        return "Int";
    }
}


class BoolType extends TypeExpr {
    getType() {
        return "Bool";
    }
}


class StringType extends TypeExpr {
    getType() {
        return "String";
    }
}

class FuncType extends TypeExpr {
    readonly domain : TypeExpr[];
    readonly image : TypeExpr;
    constructor(domain : TypeExpr[], image  : TypeExpr){
        super();
        this.domain = domain;
        this.image = image;
    }
    getType(){
        if(this.domain.length == 0){
            return "() " + this.image;
        }
        else{
            return "(" + this.domain.slice(1).reduce((a, b) => a + " " + b.getType(), this.domain[0].getType()) + ") (" + this.image.getType() + ")";
        }
    }
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
    static readonly symbolTable : Map<string, TypeExpr> = new Map<string, TypeExpr>();
    constructor(name : string, ty : TypeExpr){
        this.name = name;
        this.ty = ty;
    }
    abstract toZ3(fd : number) : void;
    abstract toZ3Declarations(fd : number) : void;
}

class VarExpr extends TermExpr {
    constructor(name : string, ty : TypeExpr){
        super(name, ty);
        VarExpr.symbolTable.set(this.name, this.ty);
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
    toZ3Declarations(fd : number) : void {
        fs.writeSync(fd, "(declare-fun " + this.name + " () " + this.ty.getType() + ")\n");
    }
}

class FuncExpr extends TermExpr {
    readonly terms : TermExpr[];
    constructor(name : string, ty : TypeExpr, terms : TermExpr[]){
        let collectType = new FuncType(terms.map(x => x.ty), ty);
        switch(terms.length){
            case 0: {
                super(name + "()", collectType);
                break;
            }   
            case 1: {
                super(name + "(" + terms[0].name + ")", collectType)
                break;
            }
            default: {
                super(name + "_" + terms.slice(1).reduce((a, b) => a + "," + b.name, terms[0].name) + "_", collectType);
                break;  
            }
        }
        this.terms = terms;
        FuncExpr.symbolTable.set(this.name, this.ty);
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
    toZ3Declarations(fd : number) : void {
        for (let item of this.terms){
            item.toZ3Declarations(fd);
        }
        fs.writeSync(fd, "(declare-fun " + this.name + " " + this.ty.getType() + ")\n");
    }
}

abstract class FormulaExpr {
    readonly name : string;
    readonly ty : TypeExpr;
    static readonly symbolTable : Map<string, TypeExpr> = new Map<string, TypeExpr>();
    constructor(name : string, ty : TypeExpr){
        this.name = name;
        this.ty = ty;
    }
    abstract toZ3(fd : number) : void;
}

class PredicateExpr extends FormulaExpr {
    readonly terms : TermExpr[];
    constructor(name : string, terms : TermExpr[]){
        switch(terms.length){
            case 0: {
                super(name + "__", new BoolType());
                break;
            }   
            case 1: {
                super(name + "_" + terms[0].name + "_", new BoolType())
                break;
            }
            default: {
                super(name + "_" + terms.slice(1).reduce((a, b) => a + "," + b.name, terms[0].name) + "_", new BoolType());
                break;  
            }
        }
        this.terms = terms;
        FormulaExpr.symbolTable.set(this.name, new BoolType());
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class EqualityExpr extends FormulaExpr {
    readonly leftHandSide : TermExpr;
    readonly rightHandSide : TermExpr;
    constructor(left : TermExpr, right : TermExpr){
        super(left.name + "=" + right.name, new BoolType());
        this.leftHandSide = left;
        this.rightHandSide = right;
        EqualityExpr.symbolTable.set(this.name, new BoolType());
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class NegExpr extends FormulaExpr {
    readonly formula : FormulaExpr;
    constructor(formula : FormulaExpr){
        super("neg " + formula.name, new BoolType());
        this.formula = formula;
        NegExpr.symbolTable.set(this.name, new BoolType());
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class AndExpr extends FormulaExpr {
    readonly leftHandSide : FormulaExpr;
    readonly rightHandSide : FormulaExpr;
    constructor(left : FormulaExpr, right : FormulaExpr){
        super(left.name + " and " + right.name, new BoolType());
        this.leftHandSide = left;
        this.rightHandSide = right;
        AndExpr.symbolTable.set(this.name, new BoolType());
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class OrExpr extends FormulaExpr {
    readonly leftHandSide : FormulaExpr;
    readonly rightHandSide : FormulaExpr;
    constructor(left : FormulaExpr, right : FormulaExpr){
        super(left.name + " or " + right.name, new BoolType());
        this.leftHandSide = left;
        this.rightHandSide = right;
        OrExpr.symbolTable.set(this.name, new BoolType());
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class ImplExpr extends FormulaExpr {
    readonly leftHandSide : FormulaExpr;
    readonly rightHandSide : FormulaExpr;
    constructor(left : FormulaExpr, right : FormulaExpr){
        super(left.name + " implies " + right.name, new BoolType());
        this.leftHandSide = left;
        this.rightHandSide = right;
        ImplExpr.symbolTable.set(this.name, new BoolType());
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class ForAllExpr extends FormulaExpr {
    readonly nameBinder : VarExpr;
    readonly formula : FormulaExpr;
    constructor(nameBinder : VarExpr, formula : FormulaExpr){
        super("forall " + nameBinder.name + ".(" + formula.name + ")", new BoolType());
        this.nameBinder = nameBinder;
        this.formula = formula;
        ForAllExpr.symbolTable.set(this.name, new BoolType());
    }
    toZ3(fd : number) : void {
        fs.writeSync(fd, this.name + '\n');
    }
}

class ExistsExpr extends FormulaExpr { 
    readonly nameBinder : VarExpr;
    readonly formula : FormulaExpr;
    constructor(nameBinder : VarExpr, formula : FormulaExpr){
        super("exists " + nameBinder.name + ".(" + formula.name + ")", new BoolType());
        this.nameBinder = nameBinder;
        this.formula = formula;
        ExistsExpr.symbolTable.set(this.name, new BoolType());
    }
    toZ3(fd : number) : void {
       fs.writeSync(fd, this.name + '\n');  
    }
}

// Testing
let x = new VarExpr("x", new IntType());
let y = new VarExpr("y", new IntType());
let pxy = new PredicateExpr("p", [x, y]);
let fxy = new FuncExpr("f", new StringType(), [x, y]);
let extraLong = new ForAllExpr(x, 
    new AndExpr( 
        pxy, 
        new ForAllExpr(y, new PredicateExpr("p", [fxy, x, x, y, fxy, x]))
    ));

//console.log(extraLong);

// // Writing on a file
// // So we can use Z3 
// console.log('Testing writing on file');
// let fd = fs.openSync('file.z3', 'w');
// extraLong.toZ3(fd);
// fs.closeSync(fd);
// // Passed!

// console.log(FormulaExpr.symbolTable)
// console.log(TermExpr.symbolTable)

let fd = fs.openSync('file.z3', 'w');
fxy.toZ3Declarations(fd);
fs.closeSync(fd);