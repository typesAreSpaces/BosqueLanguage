"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const type_expr_1 = require("./type_expr");
const util_1 = require("./util");
class TermExpr {
    constructor(symbol_name, ty, fkey) {
        this.symbol_name = symbol_name;
        this.ty = ty;
        this.fkey = fkey;
    }
}
exports.TermExpr = TermExpr;
// TOUPDATE: Add more reserved words from FStar
TermExpr.bin_op_to_fstar = new Map([
    ["&&", "op_and"], ["||", "op_or"],
    ["*", "op_mult"], ["-", "op_sub"], ["+", "op_add"], ["%", "op_mod"], ["/", "op_div"],
    ["<=", "op_lessOrEq"], [">", "op_greater"], [">=", "op_greaterOrEq"], ["<", "op_less"],
    ["==", "op_eqTerm"], ["!=", "op_notEqTerm"]
]);
TermExpr.unary_op_to_fstar = new Map([
    ["!", "op_not"],
    ["-", "op_neg"]
]);
class VarTerm extends TermExpr {
    constructor(symbol_name, ty, fkey) {
        super(symbol_name, ty, fkey);
    }
    toML() {
        return this.symbol_name;
    }
}
exports.VarTerm = VarTerm;
class ConstTerm extends TermExpr {
    constructor(symbol_name, ty, fkey) {
        if (ty instanceof type_expr_1.NoneType) {
            super("BNone", ty, fkey);
        }
        else if (ty instanceof type_expr_1.BoolType) {
            super("(BBool " + symbol_name + ")", ty, fkey);
        }
        else if (ty instanceof type_expr_1.IntType) {
            super("(BInt " + symbol_name + ")", ty, fkey);
        }
        else if (ty instanceof type_expr_1.TypedStringType) {
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
exports.ConstTerm = ConstTerm;
class FuncTerm extends TermExpr {
    constructor(symbol_name, terms, ty, fkey) {
        super(symbol_name, ty, fkey);
        this.terms = terms;
    }
    toML() {
        return "(" + this.symbol_name
            + " " + this.terms.map(x => x.toML()).join(" ")
            + ")";
    }
}
exports.FuncTerm = FuncTerm;
class TupleTerm extends TermExpr {
    constructor(term_sequence, fkey) {
        super("BTuple", new type_expr_1.TupleType(false, term_sequence.map(x => x.ty)), fkey);
        this.term_sequence = term_sequence;
    }
    toML() {
        return "(BTuple " + this.term_sequence.length + " "
            + util_1.toFStarSequence(this.term_sequence.map(x => x.toML()))
            + ")";
    }
}
exports.TupleTerm = TupleTerm;
class TupleProjExpr extends TermExpr {
    constructor(index, dimension, tuple, ty, fkey) {
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
exports.TupleProjExpr = TupleProjExpr;
class RecordTerm extends TermExpr {
    constructor(string_sequence, term_sequence, fkey) {
        super("BRecord", new type_expr_1.RecordType(false, string_sequence, term_sequence.map(x => x.ty)), fkey);
        this.string_sequence = string_sequence.map(x => "\"" + x + "\"");
        this.term_sequence = term_sequence;
    }
    toML() {
        return "(BRecord " + this.term_sequence.length + " "
            + util_1.toFStarSequence(this.string_sequence) + " "
            + util_1.toFStarSequence(this.term_sequence.map(x => x.toML()))
            + ")";
    }
}
exports.RecordTerm = RecordTerm;
class RecordProjExpr extends TermExpr {
    constructor(property, dimension, record, ty, fkey) {
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
exports.RecordProjExpr = RecordProjExpr;
class ListTerm extends TermExpr {
    constructor(term_list, ty, fkey) {
        super("BList", new type_expr_1.ListType(ty), fkey);
        this.term_list = term_list;
        this.ty = ty;
    }
    toML() {
        return `(BList ${this.ty.fstar_type_encoding} ${util_1.toFStarList(this.term_list.map(x => x.toML()))})`;
    }
}
exports.ListTerm = ListTerm;
//# sourceMappingURL=term_expr.js.map