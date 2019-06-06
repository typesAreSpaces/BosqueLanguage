//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

// import * as deepEqual from "deep-equal"
import { TypeExpr, BoolType, FuncType, UninterpretedType } from "./type_expr";
import { TermExpr, VarExpr } from "./term_expr";
import * as FS from "fs";

// REMARK: Names cannot include `,'
// or any other symbol that Z3 cannot
// parse as a valid char for a named expression
abstract class FormulaExpr {
    readonly name: string;
    readonly symbolName: string;
    readonly ty: TypeExpr;
    static fd = FS.openSync('file.z3', 'w');
    // TODO: Add more reserved words from Z3
    static readonly symbolTable: Map<string, boolean> = new Map<string, boolean>(
        ([">", ">=", "<", "<=", "=", "true", "false"].map(x => {
            if (x === "true" || x === "false") {
                return [x, true];
            }
            else {
                return ["op_" + x, true];
            }
        }))
    );
    constructor(name: string, symbolName: string, ty: TypeExpr) {
        this.name = name;
        this.symbolName = symbolName;
        this.ty = ty;
    }
    abstract sexpr(): string;
    initialDeclarationZ3(fd: number) {
        FS.writeSync(fd, "(set-option :smt.auto-config false) ; disable automatic self configuration\n");
        FS.writeSync(fd, "(set-option :smt.mbqi false) ; disable model-based quantifier instantiation\n");
        FS.writeSync(fd, "(set-option :model true)\n\n");

        FS.writeSync(fd, "(declare-sort Term)\n");
        // TODO: Add more BTypes if needed
        FS.writeSync(fd, "(declare-datatypes () ((BType BInt BBool BString)))\n\n");

        FS.writeSync(fd, "(declare-fun HasType (Term BType) Bool)\n");
        FS.writeSync(fd, "(declare-fun BoxInt (Int) Term)\n");
        FS.writeSync(fd, "(declare-fun UnboxInt (Term) Int)\n");
        FS.writeSync(fd, "(declare-fun BoxBool (Bool) Term)\n");
        FS.writeSync(fd, "(declare-fun UnboxBool (Term) Bool)\n");
        FS.writeSync(fd, "(declare-fun BoxString (String) Term)\n");
        FS.writeSync(fd, "(declare-fun UnboxString (Term) String)\n\n");

        FS.writeSync(fd, "(assert (forall ((@x Int)) (! (= (UnboxInt (BoxInt @x)) @x) :pattern ((BoxInt @x)))))\n");
        FS.writeSync(fd, "(assert (forall ((@x Bool)) (! (= (UnboxBool (BoxBool @x)) @x) :pattern ((BoxBool @x)))))\n");
        FS.writeSync(fd, "(assert (forall ((@x String)) (! (= (UnboxString (BoxString @x)) @x) :pattern ((BoxString @x)))))\n\n");

        // TODO: Add more operations 
        FS.writeSync(fd, "(define-fun op_=> ((@x Term) (@y Term)) Term (BoxBool (=> (UnboxBool @x) (UnboxBool @y))))\n");
        FS.writeSync(fd, "(define-fun op_or ((@x Term) (@y Term)) Term (BoxBool (or (UnboxBool @x) (UnboxBool @y))))\n");
        FS.writeSync(fd, "(define-fun op_and ((@x Term) (@y Term)) Term (BoxBool (and (UnboxBool @x) (UnboxBool @y))))\n");
        FS.writeSync(fd, "(define-fun op_= ((@x Term) (@y Term)) Term (BoxBool (= @x @y)))\n");
        FS.writeSync(fd, "(define-fun op_not ((@x Term)) Term (BoxBool (not (UnboxBool @x))))\n");
        FS.writeSync(fd, "(define-fun op_> ((@x Term) (@y Term)) Term (BoxBool (> (UnboxInt @x) (UnboxInt @y))))\n");
        FS.writeSync(fd, "(define-fun op_< ((@x Term) (@y Term)) Term (BoxBool (< (UnboxInt @x) (UnboxInt @y))))\n");
        FS.writeSync(fd, "(define-fun op_>= ((@x Term) (@y Term)) Term (BoxBool (>= (UnboxInt @x) (UnboxInt @y))))\n");
        FS.writeSync(fd, "(define-fun op_<= ((@x Term) (@y Term)) Term (BoxBool (<= (UnboxInt @x) (UnboxInt @y))))\n\n");
    }
    toZ3(fd: number): void {
        this.toZ3Declaration(fd);
        let assertingZ3 = function (formula: FormulaExpr) {
            if (formula instanceof AndExpr) {
                let lhsName = formula.leftHandSide.name;
                let rhsName = formula.rightHandSide.name;
                if (lhsName !== "MIRJumpCondFormulal__r" && lhsName !== "MIRJumpFormulal__r") {
                    assertingZ3(formula.leftHandSide);
                    if (rhsName !== "MIRJumpCondFormulal__r" && rhsName !== "MIRJumpFormulal__r") {
                        assertingZ3(formula.rightHandSide);
                    }
                }
                else {
                    if (rhsName !== "MIRJumpCondFormulal__r" && rhsName !== "MIRJumpFormulal__r") {
                        assertingZ3(formula.rightHandSide);
                    }
                }
            }
            else {
                let formulaName = formula.name;
                if (formulaName != "MIRJumpCondFormulal__r" && formulaName != "MIRJumpFormulal__r") {
                    FS.writeSync(fd, "(assert (UnboxBool " + formula.sexpr() + "))\n");
                }
            }
        }
        assertingZ3(this);
    }
    checkSatZ3(fd: number) {
        FS.writeSync(fd, "(check-sat)\n");
    }
    pushZ3(fd: number) {
        FS.writeSync(fd, "(push)\n");
    }
    popZ3(fd: number) {
        FS.writeSync(fd, "(pop)\n");
    }
    getModelZ3(fd: number) {
        FS.writeSync(fd, "(get-model)\n");
    }
    toZ3DeclarationSort(fd: number): void {
        let thisTypeTemp = this.ty.getAbstractType();
        // Second part of the following conjunction avoids repetitions
        // in the declaration section
        if (this.ty instanceof UninterpretedType && !UninterpretedType.symbolTable.get(thisTypeTemp)) {
            FS.writeSync(fd, "(declare-sort " + (this.ty as UninterpretedType).name + ")\n");
            UninterpretedType.symbolTable.set(thisTypeTemp, true);
        }
    }
    abstract toZ3Declaration(fd: number): void;
}

class PredicateExpr extends FormulaExpr {
    readonly terms: TermExpr[];
    constructor(name: string, terms: TermExpr[]) {
        let collectType = new FuncType(terms.map(x => x.ty), new BoolType())
        switch (terms.length) {
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
        if (!PredicateExpr.symbolTable.get(this.symbolName)) {
            let declarationName = this.symbolName;
            FS.writeSync(fd, "(declare-fun " + declarationName + " " + this.ty.getAbstractType() + ")\n");
            // FS.writeSync(fd, "(HasType " + declarationName + " " + this.ty.getType() + ")\n");
            PredicateExpr.symbolTable.set(this.symbolName, true);
        }
    }
}

class EqualityExpr extends FormulaExpr {
    readonly leftHandSide: TermExpr;
    readonly rightHandSide: TermExpr;
    constructor(left: TermExpr, right: TermExpr) {
        super(left.name + " op_= " + right.name, "op_=", new FuncType([left.ty, right.ty], new BoolType()));
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
        super("op_not " + formula.name, "op_not", new FuncType([formula.ty], new BoolType()));
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
        super(left.name + " op_and " + right.name, "op_and", new FuncType([left.ty, right.ty], new BoolType()));
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
        super(left.name + " op_or " + right.name, "op_or", new FuncType([left.ty, right.ty], new BoolType()));
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
        super(left.name + " op_=> " + right.name, "op_=>", new FuncType([left.ty, right.ty], new BoolType()));
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
        super("op_forall " + nameBinder.name + ".l_" + formula.name + "_r", "op_forall", new FuncType([nameBinder.ty, formula.ty], new BoolType()));
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
        super("op_exists " + nameBinder.name + ".l_" + formula.name + "_r", "op_exists", new FuncType([nameBinder.ty, formula.ty], new BoolType()));
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

export { FormulaExpr, PredicateExpr, EqualityExpr, NegExpr, AndExpr, OrExpr, ImplExpr, ForAllExpr, ExistsExpr };
