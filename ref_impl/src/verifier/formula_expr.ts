//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

// import * as deepEqual from "deep-equal"
import * as fs from "fs"

abstract class TypeExpr {
    abstract readonly isPrimitiveType : boolean;
    abstract getType() : string;
}

class IntType extends TypeExpr {
    isPrimitiveType = true;
    getType() {
        return "Int";
    }
}

class BoolType extends TypeExpr {
    isPrimitiveType = true;
    getType(){
        return "Bool";
    }
}

class StringType extends TypeExpr {
    isPrimitiveType = true;
    getType() {
        return "String";
    }
}

class FuncType extends TypeExpr {
    isPrimitiveType = false;
    readonly domain : TypeExpr[];
    readonly image : TypeExpr;
    constructor(domain : TypeExpr[], image  : TypeExpr){
        super();
        this.domain = domain;
        this.image = image;
    }
    getType(){
        if(this.domain.length == 0){
            return "() " + this.image.getType();
        }
        else{
            return "(" + this.domain.slice(1).reduce((a, b) => a + " " + 
            (b.isPrimitiveType ? b.getType() : (b as FuncType).image.getType()), 
            this.domain[0].isPrimitiveType ? this.domain[0].getType() : (this.domain[0] as FuncType).image.getType())
            + ") " + this.image.getType();
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
        if(!VarExpr.symbolTable.get(this.name)){
            fs.writeSync(fd, "(declare-fun " + this.symbolName + " () " + this.ty.getType() + ")\n");
            VarExpr.symbolTable.set(this.name, true);
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
        FuncExpr.symbolTable.set(this.name, false);
    }
    toZ3Declaration(fd : number){
        for (let item of this.terms){
            item.toZ3Declaration(fd);
        }
        if(!FuncExpr.symbolTable.get(this.name)){
            fs.writeSync(fd, "(declare-fun " + this.symbolName + " " + this.ty.getType() + ")\n");
            FuncExpr.symbolTable.set(this.name, true);
        }
    }
    sexpr(){
        return "(" + this.symbolName + this.terms.reduce((a, b) => a + " " + b.sexpr(), "") + ")";
    }
}

abstract class FormulaExpr {
    readonly name : string;
    readonly symbolName : string;
    readonly ty : TypeExpr;
    static readonly symbolTable : Map<string, boolean> = new Map<string, boolean>();
    constructor(name : string, symbolName : string, ty : TypeExpr){
        this.name = name;
        this.symbolName = symbolName;
        this.ty = ty;
    }
    abstract sexpr() : string;
    toZ3(fd : number) : void {
        this.toZ3Declaration(fd);
        fs.writeSync(fd, "(assert " + this.sexpr() + ")\n");
    }
    abstract toZ3Declaration(fd : number) : void;
}

// PredicateExpr always takes a BoolType
// since we won't encode PARAMETRIZED 
// logical formulas

class PredicateExpr extends FormulaExpr {
    readonly terms : TermExpr[];
    constructor(name : string, terms : TermExpr[]){
        switch(terms.length){
            case 0: {
                super(name + "l__r", name, new BoolType());
                break;
            }   
            case 1: {
                super(name + "l_" + terms[0].name + "_r", name, new BoolType())
                break;
            }
            default: {
                super(name + "l_" + terms.slice(1).reduce((a, b) => a + "_" + b.name, terms[0].name) + "_r", name, new BoolType());
                break;  
            }
        }
        this.terms = terms;
        PredicateExpr.symbolTable.set(this.name, false);
    }
    sexpr(){
        return "(" + this.symbolName + this.terms.reduce((a, b) => a + " " + b.sexpr(), "") + ")";
    }
    toZ3Declaration(fd : number){
        for (let item of this.terms){
            item.toZ3Declaration(fd);
        }
        if(!PredicateExpr.symbolTable.get(this.name)){
            fs.writeSync(fd, "(declare-fun " + this.symbolName + " () " + this.ty.getType() + ")\n");
            PredicateExpr.symbolTable.set(this.name, true);
        }
    }
}

class EqualityExpr extends FormulaExpr {
    readonly leftHandSide : TermExpr;
    readonly rightHandSide : TermExpr;
    constructor(left : TermExpr, right : TermExpr){
        super(left.name + "=" + right.name, "=", new BoolType());
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    sexpr(){
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    }
    toZ3Declaration(fd : number){
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    }
}

class NegExpr extends FormulaExpr {
    readonly formula : FormulaExpr;
    constructor(formula : FormulaExpr){
        super("neg " + formula.name, "not", new BoolType());
        this.formula = formula;
    }
    sexpr(){
        return "(" + this.symbolName + this.formula.sexpr() + ")";
    }
    toZ3Declaration(fd : number){
        this.formula.toZ3Declaration(fd);
    }
}

class AndExpr extends FormulaExpr {
    readonly leftHandSide : FormulaExpr;
    readonly rightHandSide : FormulaExpr;
    constructor(left : FormulaExpr, right : FormulaExpr){
        super(left.name + " and " + right.name, "and", new BoolType());
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    sexpr(){
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    }
    toZ3Declaration(fd : number){
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    }
}

class OrExpr extends FormulaExpr {
    readonly leftHandSide : FormulaExpr;
    readonly rightHandSide : FormulaExpr;
    constructor(left : FormulaExpr, right : FormulaExpr){
        super(left.name + " or " + right.name, "or", new BoolType());
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    sexpr(){
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    }
    toZ3Declaration(fd : number){
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    }
}

class ImplExpr extends FormulaExpr {
    readonly leftHandSide : FormulaExpr;
    readonly rightHandSide : FormulaExpr;
    constructor(left : FormulaExpr, right : FormulaExpr){
        super(left.name + " implies " + right.name, "=>", new BoolType());
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    sexpr(){
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    }
    toZ3Declaration(fd : number){
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    }
}

class ForAllExpr extends FormulaExpr {
    readonly nameBinder : VarExpr;
    readonly formula : FormulaExpr;
    constructor(nameBinder : VarExpr, formula : FormulaExpr){
        super("forall " + nameBinder.name + ".l_" + formula.name + "_r", "forall", new BoolType());
        this.nameBinder = nameBinder;
        this.formula = formula;
    }
    sexpr(){
        return "(" + this.symbolName + " " + this.formula.sexpr() + ")";
    }
    toZ3Declaration(fd : number){
        this.formula.toZ3Declaration(fd);
    }
}

class ExistsExpr extends FormulaExpr { 
    readonly nameBinder : VarExpr;
    readonly formula : FormulaExpr;
    constructor(nameBinder : VarExpr, formula : FormulaExpr){
        super("exists " + nameBinder.name + ".l_" + formula.name + "_r", "exists", new BoolType());
        this.nameBinder = nameBinder;
        this.formula = formula;
    }
    sexpr(){
        return "(" + this.symbolName + " " + this.formula.sexpr() + ")";
    }
    toZ3Declaration(fd : number){
        this.formula.toZ3Declaration(fd);
    }
}

// IMPORTANT: Names cannot include `,'
// or any other symbol that Z3 cannot
// parse as a valid char for a name expression

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

let fd = fs.openSync('file.z3', 'w');
// (new FuncExpr("g", new IntType(), [fxy, fxy])).toZ3Declaration(fd);
// (new FuncExpr("h", new IntType(), [])).toZ3Declaration(fd);
// (new FuncExpr("k", new IntType(), [fxy])).toZ3Declaration(fd);
extraLong.toZ3(fd);
pxy.toZ3(fd);

fs.closeSync(fd);