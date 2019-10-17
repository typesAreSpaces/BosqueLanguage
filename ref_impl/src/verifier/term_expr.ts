//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { TypeExpr } from "./type_expr";

abstract class TermExpr {
    readonly symbolName: string;
    readonly ty: TypeExpr;
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
    constructor(symbolName: string, ty: TypeExpr) {
        this.symbolName = symbolName;
        this.ty = ty;
    }
    abstract toML(): string;
}

class VarTerm extends TermExpr {
    constructor(symbolName: string, ty: TypeExpr) {
        super(symbolName, ty);
    }
    toML() {
        return this.symbolName;
    }
}

class ConstTerm extends TermExpr {
    constructor(symbolName: string, ty: TypeExpr) {
        super(symbolName, ty);
    }
    toML() {
        return this.symbolName;
    }
}

class FuncTerm extends TermExpr {
    readonly terms: TermExpr[];
    constructor(symbolName: string, terms: TermExpr[], ty: TypeExpr) {
        super(symbolName, ty);
        this.terms = terms;
    }
    toML() {
        return "(" + this.symbolName
            + " " + this.terms.map(x => x.toML()).join(" ") 
            + ")";
    }
}

export { TermExpr, VarTerm, ConstTerm, FuncTerm };