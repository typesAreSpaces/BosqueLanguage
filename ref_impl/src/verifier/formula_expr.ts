//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as deepEqual from "deep-equal"

abstract class TypeExpr {
}

class IntType extends TypeExpr {
}


class BoolType extends TypeExpr {
}


class StringType extends TypeExpr {
}

abstract class TermExpr {
    readonly name: string;
    constructor(name : string){
        this.name = name;
    }
}

class VarExpr extends TermExpr {
    constructor(name : string){
        super(name);
    }
}

class FuncExpr extends TermExpr {
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
    }
}

abstract class FormulaExpr {
    readonly name : string;
    constructor(name : string){
        this.name = name;
    }
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
}

class EqualityExpr extends FormulaExpr {
    readonly leftHandSide : TermExpr;
    readonly rightHandSide : TermExpr;
    constructor(left : TermExpr, right : TermExpr){
        super(left.name + "=" + right.name);
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
}

class NegExpr extends FormulaExpr {
    readonly formula : FormulaExpr;
    constructor(formula : FormulaExpr){
        super("neg " + formula.name);
        this.formula = formula;
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
}

class OrExpr extends FormulaExpr {
    readonly leftHandSide : FormulaExpr;
    readonly rightHandSide : FormulaExpr;
    constructor(left : FormulaExpr, right : FormulaExpr){
        super(left.name + " or " + right.name);
        this.leftHandSide = left;
        this.rightHandSide = right;
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
}

class ForAllExpr extends FormulaExpr {
    readonly nameBinder : VarExpr;
    readonly formula : FormulaExpr;
    constructor(nameBinder : VarExpr, formula : FormulaExpr){
        super("forall " + nameBinder.name + ".(" + formula.name + ")");
        this.nameBinder = nameBinder;
        this.formula = formula;
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
}

// Testing
let x = new VarExpr("x");
let x2 = new VarExpr("x");
let y = new VarExpr("y");
let p = new PredicateExpr("p", [x, y]);
let not_p = new NegExpr(p);
let fxy = new FuncExpr("f", [x, y]);

console.log("Examples---");
console.log(x);
console.log(p);
console.log(not_p);
console.log(fxy);
console.log(new FuncExpr("g", [x, y, x, x, x]));
console.log(new FuncExpr("g", [x]));
console.log(new FuncExpr("g", []));
console.log(new ForAllExpr(x, p));
console.log("Ok---");

// Testing equality
console.log(deepEqual(x, x2));
console.log(deepEqual(new ForAllExpr(x, p), new ForAllExpr(x2, p)))