//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";

// TODO: Add more elements to the 
// abstract class TypeExpr once we 
// have formalized the type system
// for Bosque. Actually, it is already
// established on the documentation,
// however, it needs additional formalization
// to deal with some rules and inference
// (Current approach to accomplish the latter: take 
// the grouded ast and build a `table` using

// TODO: Update getType appropriately

abstract class TypeExpr {
    abstract getFStarType(): string;
    abstract getBosqueType(): string;
    static print(fd : number) : void {
        TupleType.isDeclared.forEach((_, index) => {
            TupleType.fstarDeclaration(fd, index);
        });
        RecordType.isDeclared.forEach((_, index) => {
            RecordType.fstarDeclaration(fd, index);
        });
    }
}

class IntType extends TypeExpr {
    getFStarType() {
        return "int";
    }
    getBosqueType(){
        return "NSCore::Int";
    }
}

class BoolType extends TypeExpr {
    getFStarType() {
        return "bool";
    }
    getBosqueType(){
        return "NSCore::Bool";
    }
}

class StringType extends TypeExpr {
    getFStarType() {
        return "string";
    }
    getBosqueType(){
        return "NSCore::String";
    }
}

class NoneType extends TypeExpr {
    getFStarType() {
        return "";
    }
    getBosqueType(){
        return "None";
    }
}

class AnyType extends TypeExpr {
    getFStarType() {
        return "";
    }
    getBosqueType(){
        return "Any";
    }
}

class SomeType extends TypeExpr {
    getFStarType() {
        return "";
    }
    getBosqueType(){
        return "Some";
    }
}

// REMARK: symbolNames cannot include `,`
// or any other symbol that FStar cannot
// parse as a valid char for a symbolNamed expression
class UninterpretedType extends TypeExpr {
    readonly symbolName: string;
    constructor(symbolName: string) {
        super();
        this.symbolName = symbolName;
    }
    getFStarType() {
        return this.symbolName;
    }
    getBosqueType(){
        return this.symbolName;
    }
}

class FuncType extends TypeExpr {
    readonly domain: TypeExpr[];
    readonly image: TypeExpr;
    constructor(domain: TypeExpr[], image: TypeExpr) {
        super();
        this.domain = domain;
        this.image = image;
    }
    getFStarType() {
        return ((this.domain.length == 0) ? "" : this.domain.map(x => x.getFStarType()).join(" -> ") + " -> Tot ")
            + this.image.getFStarType();
    }
    getBosqueType(){
        return "";
    }
}

class UnionType extends TypeExpr {
    readonly elements: Set<TypeExpr> = new Set<TypeExpr>();
    constructor(elements: Set<TypeExpr>) {
        super();
        this.elements = elements;
    }
    getFStarType() {
        return "";
    }
    getBosqueType(){
        if (this.elements.size === 0) {
            return "Empty";
        }
        else {
            return Array.from(this.elements).map(x => x.getBosqueType()).join(" | ");
        }
    }
}

class TupleType extends TypeExpr {
    static readonly isDeclared: Map<number, boolean> = new Map<number, boolean>();
    readonly length: number;
    readonly symbolName: string;
    readonly elements: TypeExpr[];

    constructor(elements : TypeExpr[]) {
        super();
        this.length = elements.length;
        this.symbolName = "tuple__" + this.length;
        this.elements = elements;
        if (TupleType.isDeclared.get(this.length) == undefined) {
            TupleType.isDeclared.set(this.length, false);
        }
    }
    getFStarType() {
        return "(" + this.symbolName + " " + this.elements.map(x => x.getFStarType()).join(" ") + ")";
    }
    getBosqueType(){
        return "";
    }
    static fstarDeclaration(fd: number, length: number): void {
        const symbolName = "tuple__" + length;
        if (TupleType.isDeclared.get(length) == false) {
            FS.writeSync(fd, "type " + symbolName);
            for (let index = 1; index <= length; ++index) {
                FS.writeSync(fd, " (t_" + index + " : Type)");
            }
            FS.writeSync(fd, " =\n");
            FS.writeSync(fd, "| Mk" + symbolName + ":")
            for (let index = 1; index <= length; ++index) {
                FS.writeSync(fd, " _" + index + ":t_" + index + " ->");
            }
            FS.writeSync(fd, " " + symbolName);
            for (let index = 1; index <= length; ++index) {
                FS.writeSync(fd, " t_" + index);
            }
            FS.writeSync(fd, " \n\n");
            TupleType.isDeclared.set(length, true);
        }
    }
}

class RecordType extends TypeExpr {
    static readonly isDeclared: Map<string, boolean> = new Map<string, boolean>();
    readonly signature: string;
    readonly symbolName: string;
    readonly elements: [string, TypeExpr][];
    
    constructor(elements: [string, TypeExpr][]) {
        super()
        this.signature = elements.map(x => x[0]).join("_");
        this.symbolName = "record__" + this.signature;
        this.elements = elements;
        if (RecordType.isDeclared.get(this.signature) == undefined) {
            RecordType.isDeclared.set(this.signature, false);
        }
    }
    getFStarType() {
        return "(" + this.symbolName + " " + this.elements.map(x => x[1].getFStarType()).join(" ") + ")";
    }
    getBosqueType(){
        return "";
    }
    static fstarDeclaration(fd: number, signature: string): void {
        const symbolName = "record__" + signature;
        const keys = signature.split("_");
        const length = keys.length;
        if (RecordType.isDeclared.get(signature) == false) {
            FS.writeSync(fd, "type " + symbolName);
            for (let index = 1; index <= length; ++index) {
                FS.writeSync(fd, " (t_" + index + " : Type)");
            }
            FS.writeSync(fd, " =\n");
            FS.writeSync(fd, "| Mk" + symbolName + ":")
            for (let index = 1; index <= length; ++index) {
                FS.writeSync(fd, " " + keys[index-1] + ":t_" + index + " ->");
            }
            FS.writeSync(fd, " " + symbolName);
            for (let index = 1; index <= length; ++index) {
                FS.writeSync(fd, " t_" + index);
            }
            FS.writeSync(fd, " \n\n");
            TupleType.isDeclared.set(length, true);
        }
    }
}

class ConstructorType extends TypeExpr {
    constructor() {
        super();
    }
    // FIX: THIS IS WRONG. Keep in mind this goes into FStar signatures
    getFStarType() {
        return "";
    }
    getBosqueType(){
        return "";
    }
    fstarDeclaration(fd: number): void {
        FS.writeSync(fd, "");
    }
}

class LambdaType extends TypeExpr {
    readonly args: [string, TypeExpr][];
    readonly result: TypeExpr;
    constructor(args: [string, TypeExpr][], result: TypeExpr) {
        super()
        this.args = args;
        this.result = result;
    }
    
    getFStarType() {
        return "";
        // FIX: THIS IS WRONG. Keep in mind this goes into FStar signatures
        // return "(" + this.args.map(x => x[0] + ":" + x[1].getFStarType()).join(", ") + ")" + " -> " + this.result.getFStarType();
    }
    getBosqueType(){
        return "";
    }
    fstarDeclaration(): string {
        return "";
    }
}

export { TypeExpr, IntType, BoolType, StringType, NoneType, AnyType, SomeType, FuncType, UninterpretedType, UnionType, TupleType, RecordType, ConstructorType, LambdaType };