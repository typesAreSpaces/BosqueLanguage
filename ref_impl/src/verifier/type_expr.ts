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
        PolymorphicTupleType.declaredTuples.forEach((_, index) => {
            PolymorphicTupleType.fstarDeclaration(fd, index);
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
        return "None";
    }
    getBosqueType(){
        return "None";
    }
}

class AnyType extends TypeExpr {
    getFStarType() {
        return "Any";
    }
    getBosqueType(){
        return "Any";
    }
}

class SomeType extends TypeExpr {
    getFStarType() {
        return "Some";
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
        if (this.elements.size === 0) {
            return "Empty";
        }
        else {
            return Array.from(this.elements).map(x => x.getFStarType()).join(" | ");
        }
    }
    getBosqueType(){
        return "";
    }
}

class TupleType extends TypeExpr {
    readonly symbolName: string;
    readonly elements: TypeExpr[];
    constructor(elements: TypeExpr[]) {
        super();
        this.symbolName = "tuple__" + elements.length;
        this.elements = elements;
    }
    getFStarType() {
        return "(" + this.symbolName + " " + this.elements.map(x => x.getFStarType()).join(" ") + ")";
    }
    getBosqueType(){
        return "";
    }
    fstarDeclaration(fd: number): void {
    }
}

class PolymorphicTupleType extends TypeExpr {
    static readonly declaredTuples: Map<number, boolean> = new Map<number, boolean>();
    readonly symbolName: string;
    readonly length: number;
    constructor(length: number) {
        super();
        this.symbolName = "tuple__" + length;
        this.length = length;
        if (PolymorphicTupleType.declaredTuples.get(length) == undefined) {
            PolymorphicTupleType.declaredTuples.set(length, false);
        }
    }
    getFStarType() {
        let type = "";
        for (let index = 1; index <= this.length; ++index) {
            type = type + " (t_" + index + 1 + " : Type)";
        }
        return "(" + this.symbolName + " "
            + type + ")";
    }
    getBosqueType(){
        return "";
    }
    static fstarDeclaration(fd: number, length: number): void {
        let symbolName = "tuple__" + length;
        if (PolymorphicTupleType.declaredTuples.get(length) == false) {
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
            PolymorphicTupleType.declaredTuples.set(length, true);
        }
    }
}

class RecordType extends TypeExpr {
    readonly symbolName: string;
    readonly elements: [string, TypeExpr][];
    constructor(elements: [string, TypeExpr][]) {
        super()
        this.symbolName = "record__" + elements.length;
        this.elements = elements;
    }
    getFStarType() {
        return "(" + this.symbolName + " " + this.elements.map(x => x[1].getFStarType()).join(" ") + ")";
    }
    getBosqueType(){
        return "";
    }
    fstarDeclaration(fd: number): void {
    }
}

class PolymorphicRecordType extends TypeExpr {
    readonly symbolName: string;
    readonly keys: string[];
    constructor(keys: string[]) {
        super()
        this.symbolName = "record__" + keys.length;
        this.keys = keys;
    }
    getFStarType() {
        // FIX: It should be polymorphic
        return "";
        // return "(" + this.symbolName + " " + this.elements.map(x => x[1].getType()).join(" ") + ")";
    }
    getBosqueType(){
        return "";
    }
    fstarDeclaration(fd: number): void {
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
    // FIX: THIS IS WRONG. Keep in mind this goes into FStar signatures
    getFStarType() {
        return "(" + this.args.map(x => x[0] + ":" + x[1].getFStarType()).join(", ") + ")" + " -> " + this.result.getFStarType();
    }
    getBosqueType(){
        return "";
    }
    fstarDeclaration(): string {
        return "";
    }
}

export { TypeExpr, IntType, BoolType, StringType, NoneType, AnyType, SomeType, FuncType, UninterpretedType, UnionType, TupleType, RecordType, PolymorphicTupleType, PolymorphicRecordType, ConstructorType, LambdaType };