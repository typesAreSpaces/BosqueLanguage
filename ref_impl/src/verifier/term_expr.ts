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
        ["&&", "op_AmpAmp"], ["||", "op_BarBar"],
        ["*", "op_Multiply"], ["-", "op_Subtraction"], ["+", "op_Addition"], ["%", "op_Modulus"], ["/", "op_Division"],
        ["<=", "op_LessThanOrEqual"], [">", "op_GreaterThan"], [">=", "op_GreaterThanOrEqual"], ["<", "op_LessThan"],
        ["==", "op_Equality"], ["!=", "op_disEquality"]
    ]);
    static readonly unaryOpToFStar: Map<string, string> = new Map<string, string>([
        ["!", "op_Negation"],
        ["-", "op_Minus"]
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