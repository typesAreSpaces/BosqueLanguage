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
        [">", ">=", "<", "<=", "=", "true", "false"].map(x => [x, true])
    );
    constructor(name: string, symbolName: string, ty: TypeExpr) {
        this.name = name;
        this.symbolName = symbolName;
        this.ty = ty;
    }
    abstract sexpr(): string;
    // Setting optionalGetModel to true
    // will include a (get-model) command
    // to the Z3 file; otherwise it wont    
    toZ3(fd: number, optionalGetModel: boolean): void {
        this.toZ3Declaration(fd);
        FS.writeSync(fd, "(push)\n");
        FS.writeSync(fd, "(assert " + this.sexpr() + ")\n(check-sat)\n");
        if (optionalGetModel) {
            FS.writeSync(fd, "(get-model)\n");
        }
        FS.writeSync(fd, "(pop)\n");
    }
    toZ3DeclarationSort(fd: number): void {
        let thisTypeTemp = this.ty.getType();
        if (this.ty.isUninterpreted && !UninterpretedType.symbolTable.get(thisTypeTemp)) {
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
            FS.writeSync(fd, "(declare-fun " + this.symbolName + " " + this.ty.getType() + ")\n");
            PredicateExpr.symbolTable.set(this.symbolName, true);
        }
    }
}

class EqualityExpr extends FormulaExpr {
    readonly leftHandSide: TermExpr;
    readonly rightHandSide: TermExpr;
    constructor(left: TermExpr, right: TermExpr) {
        super(left.name + "=" + right.name, "=", new FuncType([left.ty, right.ty], new BoolType()));
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
        super("neg " + formula.name, "not", new FuncType([formula.ty], new BoolType()));
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
        super(left.name + " and " + right.name, "and", new FuncType([left.ty, right.ty], new BoolType()));
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
        super(left.name + " or " + right.name, "or", new FuncType([left.ty, right.ty], new BoolType()));
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
        super(left.name + " implies " + right.name, "=>", new FuncType([left.ty, right.ty], new BoolType()));
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
        super("forall " + nameBinder.name + ".l_" + formula.name + "_r", "forall", new FuncType([nameBinder.ty, formula.ty], new BoolType()));
        this.nameBinder = nameBinder;
        this.formula = formula;
    }
    sexpr() {
        return "(" + this.symbolName + " ((" + this.nameBinder.symbolName + " " + this.nameBinder.ty.getType() + ")) " + this.formula.sexpr() + ")";
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
        super("exists " + nameBinder.name + ".l_" + formula.name + "_r", "exists", new FuncType([nameBinder.ty, formula.ty], new BoolType()));
        this.nameBinder = nameBinder;
        this.formula = formula;
    }
    sexpr() {
        return "(" + this.symbolName + " ((" + this.nameBinder.symbolName + " " + this.nameBinder.ty.getType() + ")) " + this.formula.sexpr() + ")";
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        this.formula.toZ3Declaration(fd);
    }
}

export { FormulaExpr, PredicateExpr, EqualityExpr, NegExpr, AndExpr, OrExpr, ImplExpr, ForAllExpr, ExistsExpr };
