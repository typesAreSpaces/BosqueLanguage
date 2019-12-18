//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { TypeExpr, IntType, BoolType, NoneType, TypedStringType, TupleType } from "./type_expr";
import { toFStarSequence } from "./util";

abstract class TermExpr {
    readonly symbolName: string;
    readonly ty: TypeExpr;
    readonly fkey: string;
    
    // TODO: Add more reserved words from FStar
    static readonly binOpToFStar: Map<string, string> = new Map<string, string>([
        ["&&", "op_and"], ["||", "op_or"],
        ["*", "op_mult"], ["-", "op_sub"], ["+", "op_add"], ["%", "op_mod"], ["/", "op_div"],
        ["<=", "op_lessOrEq"], [">", "op_greater"], [">=", "op_greaterOrEq"], ["<", "op_less"],
        ["==", "op_eqTerm"], ["!=", "op_notEqTerm"]
    ]);
    static readonly unaryOpToFStar: Map<string, string> = new Map<string, string>([
        ["!", "op_not"],
        ["-", "op_neg"]
    ]);
    constructor(symbolName: string, ty: TypeExpr, fkey: string) {
        this.symbolName = symbolName;
        this.ty = ty;
        this.fkey = fkey;
    }
    abstract toML(): string;
}

class VarTerm extends TermExpr {
    constructor(symbolName: string, ty: TypeExpr, fkey: string) {
        super(symbolName, ty, fkey);
    }
    toML() {
        return this.symbolName;
    }
}

class ConstTerm extends TermExpr {
    constructor(symbolName: string, ty: TypeExpr, fkey: string) {
        if (ty instanceof NoneType) {
            super("BNone", ty, fkey);
        }
        else if (ty instanceof BoolType) {
            super("(BBool " + symbolName + ")", ty, fkey);
        }
        else if (ty instanceof IntType) {
            super("(BInt " + symbolName + ")", ty, fkey);
        }
        else if (ty instanceof TypedStringType) {
            super("(BTypedString " + symbolName + " " + ty.ty.id + ")", ty, fkey);
        }
        else {
            super(symbolName, ty, fkey);
        }
    }
    toML() {
        return this.symbolName;
    }
}

class FuncTerm extends TermExpr {
    readonly terms: TermExpr[];
    constructor(symbolName: string, terms: TermExpr[], ty: TypeExpr, fkey: string) {
        super(symbolName, ty, fkey);
        this.terms = terms;
    }
    toML() {
        return "(" + this.symbolName
            + " " + this.terms.map(x => x.toML()).join(" ")
            + ")";
    }
}

class TupleTerm extends TermExpr {
    readonly termSequence: TermExpr[];
    constructor(termSequence: TermExpr[], fkey: string) {
        super("BTuple", new TupleType(false, termSequence.map(x => x.ty)), fkey);
        this.termSequence = termSequence;
    }
    toML() {
        return "(BTuple " + this.termSequence.length + " "
            + toFStarSequence(this.termSequence.map(x => x.toML()))
            + ")";
    }
}

class TupleProjExpr extends TermExpr {
    readonly index: number;
    readonly dimension: number;
    readonly tuple: TermExpr; // Actually a term register
    readonly ty: TypeExpr;

    constructor(index: number, dimension: number, tuple: TermExpr, ty: TypeExpr, fkey: string) {
        super("nthTuple", ty, fkey);
        this.index = index;
        this.dimension = dimension;
        this.tuple = tuple;
        this.ty = ty;
    }
    toML() {
        return "(nthTuple " + this.index + " "
            + this.dimension + " " + this.tuple.toML() + ")";
    }
}


export { TermExpr, VarTerm, ConstTerm, FuncTerm, TupleTerm, TupleProjExpr };