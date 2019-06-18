//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { TypeExpr, BoolType, FuncType, UninterpretedType, UnionType } from "./type_expr";
import { TermExpr, VarExpr } from "./term_expr";
import { stringVariableToStringType, resolveType } from "./collect_formulas"
import * as FS from "fs";

// REMARK: Names cannot include `,'
// or any other symbol that Z3 cannot
// parse as a valid char for a named expression
abstract class FormulaExpr {
    readonly symbolName: string;
    readonly ty: TypeExpr;
    // TODO: Add more reserved words from Z3
    static readonly symbolTable: Map<string, boolean> = new Map<string, boolean>(
        ([">", ">=", "<", "<=",
            ">_string", ">=_string", "<_string", "<=_string",
            "=", "true", "false"].map(x => [x, true]))
    );
    constructor(symbolName: string, ty: TypeExpr) {
        this.symbolName = symbolName;
        this.ty = ty;
    }
    abstract sexpr(): string;
    static initialDeclarationZ3(fd: number) {
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
        FS.writeSync(fd, "(set-option :smt.auto-config false) ; disable automatic self configuration\n");
        FS.writeSync(fd, "(set-option :smt.mbqi false) ; disable model-based quantifier instantiation\n");
        FS.writeSync(fd, "(set-option :model true)\n\n");
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
        FS.writeSync(fd, "(declare-sort Term)\n");
        // TODO: Add more BTypes if needed -----------------------------------------------------------------------------------------------------------------------------------------------------------------------------
        FS.writeSync(fd, "(declare-datatypes () ((BType BInt BBool BString BAny BSome BNone BTuple)))\n\n");
        // FS.writeSync(fd, "(declare-sort None)\n"); // To BoxNone/UnboxNone
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
        FS.writeSync(fd, "(declare-fun HasType (Term) BType)\n");
        FS.writeSync(fd, "(declare-fun BoxInt (Int) Term)\n");
        FS.writeSync(fd, "(declare-fun UnboxInt (Term) Int)\n");
        FS.writeSync(fd, "(declare-fun BoxBool (Bool) Term)\n");
        FS.writeSync(fd, "(declare-fun UnboxBool (Term) Bool)\n");
        FS.writeSync(fd, "(declare-fun BoxString (String) Term)\n");
        FS.writeSync(fd, "(declare-fun UnboxString (Term) String)\n");
        FS.writeSync(fd, "(declare-fun BoxAny (Any) Term)\n");
        FS.writeSync(fd, "(declare-fun UnboxAny (Term) Any)\n");
        FS.writeSync(fd, "(declare-fun BoxSome (Some) Term)\n");
        FS.writeSync(fd, "(declare-fun UnboxSome (Term) Some)\n");
        FS.writeSync(fd, "(declare-fun TupleElement (Term Int) Term)");
        FS.writeSync(fd, "(declare-fun TupleLength (Term) Int)");
        FS.writeSync(fd, "(declare-fun RecordElement (Term String) Term)");
        FS.writeSync(fd, "(declare-fun RecordLength (Term) Int)");
        // FS.writeSync(fd, "(declare-fun BoxNone (None) Term)\n");
        // FS.writeSync(fd, "(declare-fun UnboxNone (Term) None)\n\n");
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
        FS.writeSync(fd, "(define-fun head ((s String)) String (str.at s 0))\n");
        FS.writeSync(fd, "(define-fun tail ((s String)) String (str.substr s 1 (- (str.len s) 1)))\n");
        FS.writeSync(fd, "(declare-fun firstChar (String) (_ BitVec 8))\n");
        FS.writeSync(fd, "(assert (forall ((s String)) (! (or (= (seq.unit (firstChar s)) (seq.at s 0)) (= (as seq.empty String)  (seq.at s 0))) :pattern (firstChar s) :pattern (seq.at s 0))))\n");
        FS.writeSync(fd, "(declare-fun <_string (String String) Bool)\n");
        FS.writeSync(fd, "(assert (forall ((x String) (y String)) (! (= (<_string x y) (ite (= (head x) (head y)) (<_string (tail x) (tail y)) (bvult (firstChar x) (firstChar y)))) :pattern ((<_string x y)))))\n");
        FS.writeSync(fd, "(define-fun <=_string ((x String) (y String)) Bool (or (<_string x y) (= x y)))\n");
        FS.writeSync(fd, "(define-fun >_string ((x String) (y String)) Bool (not (<=_string x y)))\n");
        FS.writeSync(fd, "(define-fun >=_string ((x String) (y String)) Bool (not (<_string x y)))\n\n");
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
        FS.writeSync(fd, "(assert (forall ((@x Int)) (! (= (UnboxInt (BoxInt @x)) @x) :pattern ((BoxInt @x)))))\n");
        FS.writeSync(fd, "(assert (forall ((@x Bool)) (! (= (UnboxBool (BoxBool @x)) @x) :pattern ((BoxBool @x)))))\n");
        FS.writeSync(fd, "(assert (forall ((@x String)) (! (= (UnboxString (BoxString @x)) @x) :pattern ((BoxString @x)))))\n");
        // FS.writeSync(fd, "(assert (forall ((@x None)) (! (= (UnboxNone (BoxNone @x)) @x) :pattern ((BoxNone @x)))))\n");
        // -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------
    }
    toZ3(fd: number): void {
        this.toZ3Declaration(fd);
        FS.writeSync(fd, "\n");
        stringVariableToStringType.forEach((sType, sVariable) => {
            if (sType.includes("|")) {
                let unionType = resolveType(sType) as UnionType;
                FS.writeSync(fd, "(assert (or " + Array.from(unionType.elements).map(element =>
                    "(= (HasType " + sVariable + ") " + element.getBosqueType() + ")"
                ).join(" ") + "))\n");

            }
            else {
                FS.writeSync(fd, "(assert (= (HasType " + sVariable + ") " + resolveType(sType).getBosqueType() + "))\n");
            }
        });
        FS.writeSync(fd, "\n");
        let assertingZ3 = function (formula_: FormulaExpr) {
            if (formula_ instanceof AndExpr) {
                assertingZ3(formula_.leftHandSide);
                assertingZ3(formula_.rightHandSide);
            }
            else {
                FS.writeSync(fd, "(assert " + formula_.sexpr() + ")\n");
            }
        }
        assertingZ3(this);
        // FS.writeSync(fd, "(assert " + this.sexpr() + ")\n");
    }
    static checkSatZ3(fd: number) {
        FS.writeSync(fd, "(check-sat)\n");
    }
    static pushZ3(fd: number) {
        FS.writeSync(fd, "(push)\n");
    }
    static popZ3(fd: number) {
        FS.writeSync(fd, "(pop)\n");
    }
    static getModelZ3(fd: number) {
        FS.writeSync(fd, "(get-model)\n");
    }
    toZ3DeclarationSort(fd: number): void {
        let thisTypeTemp = this.ty.getType();
        // Second part of the following conjunction avoids repetitions
        // in the declaration section
        if (this.ty instanceof UninterpretedType && !UninterpretedType.symbolTable.get(thisTypeTemp)) {
            FS.writeSync(fd, "(declare-sort " + (this.ty as UninterpretedType).symbolName + ")\n");
            UninterpretedType.symbolTable.set(thisTypeTemp, true);
        }
    }
    abstract toZ3Declaration(fd: number): void;
}

class PredicateExpr extends FormulaExpr {
    readonly terms: TermExpr[];
    constructor(symbolName: string, terms: TermExpr[]) {
        let collectType = new FuncType(terms.map(x => x.ty), new BoolType())
        switch (terms.length) {
            case 0: {
                super(symbolName, collectType);
                break;
            }
            case 1: {
                super(symbolName, collectType)
                break;
            }
            default: {
                super(symbolName, collectType);
                break;
            }
        }
        this.terms = terms;
        if (!PredicateExpr.symbolTable.has(this.symbolName)) {
            PredicateExpr.symbolTable.set(this.symbolName, false);
        }
    }
    sexpr() {
        switch (this.terms.length) {
            case 0: {
                return this.symbolName;
            }
            default: {
                return "(" + this.symbolName + this.terms.reduce((a, b) => a + " " + b.sexpr(), "") + ")";
            }
        }
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        for (let item of this.terms) {
            item.toZ3Declaration(fd);
        }
        // This also checks the term symbols because some functions can return Boolean types
        if (!PredicateExpr.symbolTable.get(this.symbolName) && !TermExpr.symbolTable.get(this.symbolName)) {
            let declarationName = this.symbolName;
            FS.writeSync(fd, "(declare-fun " + declarationName + " " + this.ty.getAbstractType() + ")\n");
            PredicateExpr.symbolTable.set(this.symbolName, true);
        }
    }
}

class EqualityTerm extends FormulaExpr {
    readonly leftHandSide: TermExpr;
    readonly rightHandSide: TermExpr;
    constructor(left: TermExpr, right: TermExpr) {
        super("=", new FuncType([left.ty, right.ty], new BoolType()));
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    sexpr() {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    }
}

class EqualityFormula extends FormulaExpr {
    readonly leftHandSide: FormulaExpr;
    readonly rightHandSide: FormulaExpr;
    constructor(left: FormulaExpr, right: FormulaExpr) {
        super("=", new FuncType([left.ty, right.ty], new BoolType()));
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    sexpr() {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    }
}

class NegExpr extends FormulaExpr {
    readonly formula: FormulaExpr;
    constructor(formula: FormulaExpr) {
        super("not", new FuncType([formula.ty], new BoolType()));
        this.formula = formula;
    }
    sexpr() {
        return "(" + this.symbolName + " " + this.formula.sexpr() + ")";
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        this.formula.toZ3Declaration(fd);
    }
}

class AndExpr extends FormulaExpr {
    readonly leftHandSide: FormulaExpr;
    readonly rightHandSide: FormulaExpr;
    constructor(left: FormulaExpr, right: FormulaExpr) {
        super("and", new FuncType([left.ty, right.ty], new BoolType()));
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    sexpr() {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    }
}

class OrExpr extends FormulaExpr {
    readonly leftHandSide: FormulaExpr;
    readonly rightHandSide: FormulaExpr;
    constructor(left: FormulaExpr, right: FormulaExpr) {
        super("or", new FuncType([left.ty, right.ty], new BoolType()));
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    sexpr() {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    }
}

class ImplExpr extends FormulaExpr {
    readonly leftHandSide: FormulaExpr;
    readonly rightHandSide: FormulaExpr;
    constructor(left: FormulaExpr, right: FormulaExpr) {
        super("=>", new FuncType([left.ty, right.ty], new BoolType()));
        this.leftHandSide = left;
        this.rightHandSide = right;
    }
    sexpr() {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    }
}

class ForAllExpr extends FormulaExpr {
    readonly nameBinder: VarExpr;
    readonly formula: FormulaExpr;
    constructor(nameBinder: VarExpr, formula: FormulaExpr) {
        super("forall", new FuncType([nameBinder.ty, formula.ty], new BoolType()));
        this.nameBinder = nameBinder;
        this.formula = formula;
    }
    sexpr() {
        return "(" + this.symbolName + " ((" + this.nameBinder.symbolName + " " + this.nameBinder.ty.getAbstractType() + ")) " + this.formula.sexpr() + ")";
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        this.formula.toZ3Declaration(fd);
    }
}

class ExistsExpr extends FormulaExpr {
    readonly nameBinder: VarExpr;
    readonly formula: FormulaExpr;
    constructor(nameBinder: VarExpr, formula: FormulaExpr) {
        super("exists", new FuncType([nameBinder.ty, formula.ty], new BoolType()));
        this.nameBinder = nameBinder;
        this.formula = formula;
    }
    sexpr() {
        return "(" + this.symbolName + " ((" + this.nameBinder.symbolName + " " + this.nameBinder.ty.getAbstractType() + ")) " + this.formula.sexpr() + ")";
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        this.formula.toZ3Declaration(fd);
    }
}

function makeConjunction(formulas: FormulaExpr[]): FormulaExpr {
    let changeFormula = false;
    let result = new PredicateExpr("true", []) as FormulaExpr;
    for (let formula of formulas) {
        if (!changeFormula) {
            changeFormula = true;
            result = formula;
        }
        else {
            result = new AndExpr(result, formula);
        }
    }
    return result;
}

function makeDisjuction(formulas: Set<FormulaExpr>): FormulaExpr {
    let changeFormula = false;
    let result = new PredicateExpr("false", []) as FormulaExpr;
    for (let formula of formulas) {
        if (!changeFormula) {
            changeFormula = true;
            result = formula;
        }
        else {
            result = new OrExpr(result, formula);
        }
    }
    return result;
}

export { FormulaExpr, PredicateExpr, EqualityTerm, EqualityFormula, NegExpr, AndExpr, OrExpr, ImplExpr, ForAllExpr, ExistsExpr, makeConjunction, makeDisjuction };