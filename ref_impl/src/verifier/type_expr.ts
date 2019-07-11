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
    abstract getType(): string;
}

class IntType extends TypeExpr {
    getType() {
        return "int";
    }
}

class BoolType extends TypeExpr {
    getType() {
        return "bool";
    }
}

class StringType extends TypeExpr {
    getType() {
        return "string";
    }
}

class NoneType extends TypeExpr {
    getType() {
        return "None";
    }
}

class AnyType extends TypeExpr {
    getType() {
        return "Any";
    }
}

class SomeType extends TypeExpr {
    getType() {
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
    getType() {
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
    getType() {
        return ((this.domain.length == 0) ? "" : this.domain.map(x => x.getType()).join(" -> ") + " -> Tot ")
            + this.image.getType();
    }
}

class UnionType extends TypeExpr {
    readonly elements: Set<TypeExpr> = new Set<TypeExpr>();
    constructor(elements: Set<TypeExpr>) {
        super();
        this.elements = elements;
    }
    getType() {
        if (this.elements.size === 0) {
            return "Empty";
        }
        else {
            return Array.from(this.elements).map(x => x.getType()).join(" | ");
        }
    }
}

class TupleType extends TypeExpr {
    static readonly declaredTuples: Map<number, boolean>;
    readonly symbolName: string;
    readonly elements: TypeExpr[];
    constructor(elements: TypeExpr[]) {
        super();
        this.symbolName = "tuple__" + elements.length;
        this.elements = elements;
        if (TupleType.declaredTuples.get(this.elements.length) == undefined) {
            TupleType.declaredTuples.set(this.elements.length, false);
        }
    }
    getType() {
        return "(" + this.symbolName + " " + this.elements.map(x => x.getType()).join(" ") + ")";
    }
    fstarDeclaration(fd: number): void {
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
    getType() {
        return "(" + this.symbolName + " " + this.elements.map(x => x[1].getType()).join(" ") + ")";
    }
    fstarDeclaration(fd: number): void {
    }
}

class PolymorphicTupleType extends TypeExpr {
    static readonly declaredTuples: Map<number, boolean>;
    readonly symbolName: string;
    readonly length : number;
    constructor(length : number) {
        super();
        this.symbolName = "tuple__" + length;
        this.length = length;
        if (TupleType.declaredTuples.get(length) == undefined) {
            TupleType.declaredTuples.set(length, false);
        }
    }
    getType() {
        // FIX: It should be polymorphic
        return this.symbolName + " " + this.elements.map(x => x.getType()).join(" ") + ")";
    }
    fstarDeclaration(fd: number): void {
        if (TupleType.declaredTuples.get(this.length) == false) {
            FS.writeSync(fd, "type " + this.symbolName);
            for(let index = 1; index <= this.length; ++index){
                FS.writeSync(fd, " (t_" + index + 1 + " : Type)");
            }
            FS.writeSync(fd, + " =\n");
            FS.writeSync(fd, "| Mk" + this.symbolName + ":")
            for(let index = 1; index <= this.length; ++index){
                FS.writeSync(fd, " _" + index + ":t_" + index);
            }
            FS.writeSync(fd, + " " + this.symbolName );
            for(let index = 1; index <= this.length; ++index){
                FS.writeSync(fd, " t_" + index + 1);
            }
            FS.writeSync(fd, " \n");
            TupleType.declaredTuples.set(this.length, true);
        }
    }
}

class PolymorphicRecordType extends TypeExpr {
    readonly symbolName: string;
    readonly elements: [string, TypeExpr][];
    constructor(elements: [string, TypeExpr][]) {
        super()
        this.symbolName = "record__" + elements.length;
        this.elements = elements;
    }
    getType() {
        // FIX: It should be polymorphic
        return "(" + this.symbolName + " " + this.elements.map(x => x[1].getType()).join(" ") + ")";
    }
    fstarDeclaration(fd: number): void {
    }
}

class ConstructorType extends TypeExpr {
    constructor() {
        super();
    }
    // FIX: THIS IS WRONG. Keep in mind this goes into FStar signatures
    getType() {
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
    getType() {
        return "(" + this.args.map(x => x[0] + ":" + x[1].getType()).join(", ") + ")" + " -> " + this.result.getType();
    }
    fstarDeclaration(): string {
        return "";
    }
}

export { TypeExpr, IntType, BoolType, StringType, NoneType, AnyType, SomeType, FuncType, UninterpretedType, UnionType, TupleType, RecordType, PolymorphicTupleType, PolymorphicRecordType, ConstructorType, LambdaType };