//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { TypeExpr, IntType, BoolType, NoneType, TypedStringType, TupleType, RecordType, ListType } from "./type_expr";
import { toFStarSequence, toFStarList } from "./util";

abstract class TermExpr {
    readonly symbol_name: string;
    readonly ty: TypeExpr;
    readonly fkey: string;

    // TOUPDATE: Add more reserved words from FStar
    static readonly bin_op_to_fstar: Map<string, string> = new Map<string, string>([
        ["&&", "op_and"], ["||", "op_or"],
        ["*", "op_mult"], ["-", "op_sub"], ["+", "op_add"], ["%", "op_mod"], ["/", "op_div"],
        ["<=", "op_lessOrEq"], [">", "op_greater"], [">=", "op_greaterOrEq"], ["<", "op_less"],
        ["==", "op_eqTerm"], ["!=", "op_notEqTerm"]
    ]);
    static readonly unary_op_to_fstar: Map<string, string> = new Map<string, string>([
        ["!", "op_not"],
        ["-", "op_neg"]
    ]);
    constructor(symbol_name: string, ty: TypeExpr, fkey: string) {
        this.symbol_name = symbol_name;
        this.ty = ty;
        this.fkey = fkey;
    }
    abstract toML(): string;
}

class VarTerm extends TermExpr {
    constructor(symbol_name: string, ty: TypeExpr, fkey: string) {
        super(symbol_name, ty, fkey);
    }
    toML() {
        return this.symbol_name;
    }
}

class ConstTerm extends TermExpr {
    constructor(symbol_name: string, ty: TypeExpr, fkey: string) {
        if (ty instanceof NoneType) {
            super("BNone", ty, fkey);
        }
        else if (ty instanceof BoolType) {
            super("(BBool " + symbol_name + ")", ty, fkey);
        }
        else if (ty instanceof IntType) {
            super("(BInt " + symbol_name + ")", ty, fkey);
        }
        else if (ty instanceof TypedStringType) {
            super("(BTypedString " + symbol_name + " " + ty.ty.fstar_type_encoding + ")", ty, fkey);
        }
        else {
            super(symbol_name, ty, fkey);
        }
    }
    toML() {
        return this.symbol_name;
    }
}

class FuncTerm extends TermExpr {
    readonly terms: TermExpr[];
    constructor(symbol_name: string, terms: TermExpr[], ty: TypeExpr, fkey: string) {
        super(symbol_name, ty, fkey);
        this.terms = terms;
    }
    toML() {
        return "(" + this.symbol_name
            + " " + this.terms.map(x => x.toML()).join(" ")
            + ")";
    }
}

class TupleTerm extends TermExpr {
    readonly term_sequence: TermExpr[];
    constructor(term_sequence: TermExpr[], fkey: string) {
        super("BTuple", new TupleType(false, term_sequence.map(x => x.ty)), fkey);
        this.term_sequence = term_sequence;
    }
    toML() {
        return "(BTuple " + this.term_sequence.length + " "
            + toFStarSequence(this.term_sequence.map(x => x.toML()))
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

class RecordTerm extends TermExpr {
    readonly string_sequence: string[];
    readonly term_sequence: TermExpr[];
    constructor(string_sequence: string[], term_sequence: TermExpr[], fkey: string) {
        super("BRecord", new RecordType(false, string_sequence, term_sequence.map(x => x.ty)), fkey);
        this.string_sequence = string_sequence.map(x => "\"" + x + "\"");
        this.term_sequence = term_sequence;
    }
    toML() {
        return "(BRecord " + this.term_sequence.length + " "
            + toFStarSequence(this.string_sequence) + " "
            + toFStarSequence(this.term_sequence.map(x => x.toML()))
            + ")";
    }
}

class RecordProjExpr extends TermExpr {
    readonly property: string;
    readonly dimension: number;
    readonly record: TermExpr;
    readonly ty: TypeExpr;

    constructor(property: string, dimension: number, record: TermExpr, ty: TypeExpr, fkey: string) {
        super("nthRecord", ty, fkey);
        this.property = property;
        this.dimension = dimension;
        this.record = record;
        this.ty = ty;
    }
    toML() {
        return "(nthRecord \"" + this.property + "\" "
            + this.dimension + " " + this.record.toML() + ")";
    }
}

class ListTerm extends TermExpr {
    readonly term_list : TermExpr[];
    readonly ty: TypeExpr;
    constructor(term_list: TermExpr[], ty: TypeExpr, fkey: string) {
        super("BList", new ListType(ty), fkey);
        this.term_list = term_list;
        this.ty = ty;
    }
    toML(){
        return `(BList ${this.ty.fstar_type_encoding} ${toFStarList(this.term_list.map(x => x.toML()))})`;
    }

}

export {
    TermExpr, VarTerm, ConstTerm, FuncTerm,
    TupleTerm, TupleProjExpr, 
    RecordTerm, RecordProjExpr,
    ListTerm
};
