//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import { TypeExpr, FuncType, UninterpretedType } from "./type_expr";

abstract class TermExpr {
    readonly name: string;
    readonly symbolName: string;
    readonly ty: TypeExpr;
    // TODO: Add more reserved words from Z3
    static readonly symbolTable: Map<string, boolean> = new Map<string, boolean>(
        ["+", "-", "*", "/", "%"].map(x => [x, true])
    );
    constructor(name: string, symbolName: string, ty: TypeExpr) {
        this.name = name;
        this.symbolName = symbolName;
        this.ty = ty;
        if (!TermExpr.symbolTable.has(this.name)) {
            TermExpr.symbolTable.set(this.name, false);
        }
    }
    toZ3DeclarationSort(fd: number): void {
        let thisTypeTemp = this.ty.getType();
        if (this.ty.isUninterpreted && !UninterpretedType.symbolTable.get(thisTypeTemp)) {
            FS.writeSync(fd, "(declare-sort " + (this.ty as UninterpretedType).name + ")\n");
            UninterpretedType.symbolTable.set(thisTypeTemp, true);
        }
    }
    abstract toZ3Declaration(fd: number): void;
    abstract sexpr(): string;
}

class VarExpr extends TermExpr {
    constructor(name: string, ty: TypeExpr) {
        super(name, name, ty);
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        if (!VarExpr.symbolTable.get(this.symbolName)) {
            FS.writeSync(fd, "(declare-fun " + this.symbolName + " () " + this.ty.getType() + ")\n");
            VarExpr.symbolTable.set(this.symbolName, true);
        }
    }
    sexpr() {
        return this.symbolName;
    }
}

class FuncExpr extends TermExpr {
    readonly terms: TermExpr[];
    constructor(name: string, ty: TypeExpr, terms: TermExpr[]) {
        let collectType = new FuncType(terms.map(x => x.ty), ty);
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
    }
    toZ3Declaration(fd: number) {
        this.toZ3DeclarationSort(fd);
        for (let item of this.terms) {
            item.toZ3Declaration(fd);
        }
        if (!FuncExpr.symbolTable.get(this.symbolName)) {
            FS.writeSync(fd, "(declare-fun " + this.symbolName + " " + this.ty.getType() + ")\n");
            FuncExpr.symbolTable.set(this.symbolName, true);
        }
    }
    sexpr() {
        return "(" + this.symbolName + this.terms.reduce((a, b) => a + " " + b.sexpr(), "") + ")";
    }
}

export { TermExpr, VarExpr, FuncExpr };
