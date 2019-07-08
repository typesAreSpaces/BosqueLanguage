//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

// import * as FS from "fs";
import { TypeExpr } from "./type_expr";

abstract class TermExpr {
    readonly symbolName: string;
    readonly ty: TypeExpr;
    // TODO: Add more reserved words from FStar
    static readonly binOpToFStar: Map<string, string> = new Map<string, string>([["&&", "op_AmpAmp"], ["||", "op_BarBar"],
    ["*", "op_Multiply"], ["-", "op_Subtraction"], ["+", "op_Addition"], ["%", "op_Modulus"], ["/", "op_Division"],
    ["<=", "op_LessThanOrEqual"], [">", "op_GreaterThan"], [">=", "op_GreaterThanOrEqual"], ["<", "op_LessThan"], ["==", "op_Equality"], ["!=", "op_disEquality"]
    ]);
    static readonly unaryOpToFStar: Map<string, string> = new Map<string, string>(
        [["!", "op_Negation"], ["-", "op_Minus"]
        ]);
    static readonly symbolTable: Map<string, boolean> = new Map<string, boolean>(
        ["op_AmpAmp", "op_BarBar", "op_Negation",
            "op_Multiply", "op_Substraction", "op_Addition", "op_Minus", "op_Modulus", "op_Division",
            "op_LessThanOrEqual", "op_GreaterThan", "op_GreaterThanOrEqual", "op_LessThan", "op_Equality", "op_disEquality"
        ].map(x => [x, true])
    );
    constructor(symbolName: string, ty: TypeExpr) {
        this.symbolName = symbolName;
        this.ty = ty;
        if (!TermExpr.symbolTable.has(this.symbolName)) {
            TermExpr.symbolTable.set(this.symbolName, false);
        }
    }
    abstract toFStarDeclaration(fd: number): void;
    abstract toML(): string;
}

class VarTerm extends TermExpr {
    constructor(symbolName: string, ty: TypeExpr) {
        super(symbolName, ty);
    }
    toFStarDeclaration(fd: number) {
        if (!VarTerm.symbolTable.get(this.symbolName)) {
            // let declarationName = this.symbolName;
            // FS.writeSync(fd, "(declare-fun " + declarationName + " () " + this.ty.getAbstractType() + ")\n");
            VarTerm.symbolTable.set(this.symbolName, true);
        }
    }
    toML() {
        return this.symbolName;
    }
}

class ConstTerm extends TermExpr {
    constructor(symbolName: string, ty: TypeExpr) {
        super(symbolName, ty);
    }
    toFStarDeclaration(fd: number) {
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
    toFStarDeclaration(fd: number) {
        // this.toZ3DeclarationSort(fd);]
        // for (let item of this.terms) {
        //     item.toZ3Declaration(fd);
        // }
        if (!FuncTerm.symbolTable.get(this.symbolName)) {
            // FS.writeSync(fd, "(declare-fun " + this.symbolName + " " + this.ty.getAbstractType() + ")\n");
            FuncTerm.symbolTable.set(this.symbolName, true);
        }
    }
    toML() {
        return "(" + this.symbolName + " " + this.terms.map(x => x.toML()).join(" ") + ")";
    }
}

export { TermExpr, VarTerm, ConstTerm, FuncTerm };