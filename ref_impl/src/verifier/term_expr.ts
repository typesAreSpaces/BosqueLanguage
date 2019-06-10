//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import { TypeExpr, FuncType, UninterpretedType } from "./type_expr";
import { PredicateExpr } from "./formula_expr"

abstract class TermExpr {
    readonly symbolName: string;
    readonly ty: TypeExpr;
    // TODO: Add more reserved words from Z3
    static readonly symbolTable: Map<string, boolean> = new Map<string, boolean>(
        ["+", "-", "*", "/", "%", "HasType", 
        "UnboxInt", "UnboxBool", "UnboxString", 
        "BoxInt", "BoxBool", "BoxString"].map(x => [x, true])
    );
    constructor(symbolName: string, ty: TypeExpr) {
        this.symbolName = symbolName;
        this.ty = ty;
        if (!TermExpr.symbolTable.has(this.symbolName)) {
            TermExpr.symbolTable.set(this.symbolName, false);
        }
    }
    toZ3DeclarationSort(fd: number): void {
        let thisTypeTemp = this.ty.getAbstractType();
        if (this.ty.isUninterpreted && !UninterpretedType.symbolTable.get(thisTypeTemp)) {
            FS.writeSync(fd, "(declare-sort " + (this.ty as UninterpretedType).symbolName + ")\n");
            UninterpretedType.symbolTable.set(thisTypeTemp, true);
        }
    }
    abstract toZ3Declaration(fd: number): void;
    abstract sexpr(): string;
}

class VarExpr extends TermExpr {
    constructor(symbolName: string, ty: TypeExpr) {
        super(symbolName, ty);
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        // This also checks predicate symbols because a variable can have boolean type
        if (!VarExpr.symbolTable.get(this.symbolName) && !PredicateExpr.symbolTable.get(this.symbolName)) {
            let declarationName = this.symbolName;
            // FS.writeSync(fd, "(declare-fun " + declarationName + " () " + this.ty.getType() + ")\n");
            FS.writeSync(fd, "(declare-fun " + declarationName + " () " + this.ty.getAbstractType() + ")\n");
            // FS.writeSync(fd, "(HasType " + declarationName + " " + this.ty.getType() + ")\n");
            VarExpr.symbolTable.set(this.symbolName, true);
        }
    }
    sexpr() {
        return this.symbolName;
    }
}

// TODO: FuncExpr might need changes to 
// include the type TermType, it might not
class FuncExpr extends TermExpr {
    readonly terms: TermExpr[];
    constructor(symbolName: string, ty: TypeExpr, terms: TermExpr[]) {
        let collectType = new FuncType(terms.map(x => x.ty), ty);
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
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        for (let item of this.terms) {
            item.toZ3Declaration(fd);
        }
        // This also checks predicate symbols because a function can return a boolean type
        if (!FuncExpr.symbolTable.get(this.symbolName) && !PredicateExpr.symbolTable.get(this.symbolName)) {
            FS.writeSync(fd, "(declare-fun " + this.symbolName + " " + this.ty.getAbstractType() + ")\n");
            // FS.writeSync(fd, "(HasType " + this.symbolName + " " + this.ty.getType() + ")\n");
            FuncExpr.symbolTable.set(this.symbolName, true);
        }
    }
    sexpr() {
        return "(" + this.symbolName + this.terms.reduce((a, b) => a + " " + b.sexpr(), "") + ")";
    }
}

export { TermExpr, VarExpr, FuncExpr };
