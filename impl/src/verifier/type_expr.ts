//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

// TODO: Add more elements to the 
// abstract class TypeExpr once we 
// have formalized the type system
// for Bosque. Actually, it is already
// established on the documentation,
// however, it needs additional formalization
// to deal with some rules and inference
// (Current approach to accomplish the latter: take 
// the grouded ast and build a `table' using

abstract class TypeExpr {
    abstract readonly isPrimitiveType: boolean;
    abstract readonly isUninterpreted: boolean;
    abstract readonly isConstructor: boolean;
    abstract getType(): string;
    abstract getBosqueType(): string;
    abstract getAbstractType(): string;
}

class IntType extends TypeExpr {
    isPrimitiveType = true;
    isUninterpreted = false;
    isConstructor = false;
    getType() {
        return "Int";
    }
    getBosqueType() {
        return "BInt"
    }
    getAbstractType() {
        return "Term";
    }
}

class BoolType extends TypeExpr {
    isPrimitiveType = true;
    isUninterpreted = false;
    isConstructor = false;
    getType() {
        return "Bool";
    }
    getBosqueType() {
        return "BBool";
    }
    getAbstractType() {
        return "Term";
    }
}

class StringType extends TypeExpr {
    isPrimitiveType = true;
    isUninterpreted = false;
    isConstructor = false;
    getType() {
        return "String";
    }
    getBosqueType() {
        return "BString";
    }
    getAbstractType() {
        return "Term";
    }
}

class NoneType extends TypeExpr {
    isPrimitiveType = true;
    isUninterpreted = false;
    isConstructor = false;
    getType() {
        return "None";
    }
    getBosqueType() {
        return "BNone";
    }
    getAbstractType() {
        return "Term";
    }
}

class AnyType extends TypeExpr {
    isPrimitiveType = true;
    isUninterpreted = false;
    isConstructor = false;
    getType() {
        return "Any";
    }
    getBosqueType() {
        return "BAny";
    }
    getAbstractType() {
        return "Term";
    }
}

class SomeType extends TypeExpr {
    isPrimitiveType = true;
    isUninterpreted = false;
    isConstructor = false;
    getType() {
        return "Some";
    }
    getBosqueType() {
        return "BSome";
    }
    getAbstractType() {
        return "Term";
    }
}

class FuncType extends TypeExpr {
    isPrimitiveType = false;
    isUninterpreted = false;
    isConstructor = false;
    readonly domain: TypeExpr[];
    readonly image: TypeExpr;
    constructor(domain: TypeExpr[], image: TypeExpr) {
        super();
        this.domain = domain;
        this.image = image;
    }
    getType(): string {
        if (this.domain.length == 0) {
            return "() " + this.image.getType();
        }
        else {
            return "("
                + this.domain.map(x => (x instanceof FuncType) ? (x as FuncType).image.getType() : x.getType()).join(" ")
                + ") " + this.image.getType();
        }
    }
    getBosqueType(): string {
        if (this.domain.length == 0) {
            return "() " + this.image.getBosqueType();
        }
        else {
            return "("
                + this.domain.map(x => (x instanceof FuncType) ? (x as FuncType).image.getBosqueType() : x.getBosqueType()).join(" ")
                + ") " + this.image.getBosqueType();
        }
    }
    getAbstractType(): string {
        if (this.domain.length == 0) {
            return "() " + this.image.getAbstractType();
        }
        else {
            return "("
                + this.domain.map(x => (x instanceof FuncType) ? (x as FuncType).image.getAbstractType() : x.getAbstractType()).join(" ")
                + ") " + this.image.getAbstractType();
        }
    }
}

class UnionType extends TypeExpr {
    isPrimitiveType = false;
    isUninterpreted = false;
    isConstructor = false;
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
    getBosqueType() {
        if (this.elements.size === 0) {
            return "Empty";
        }
        else {
            return Array.from(this.elements).map(x => x.getBosqueType()).join(" | ");
        }
    }
    getAbstractType() {
        return "Term";
    }
}

// REMARK: symbolNames cannot include `,'
// or any other symbol that Z3 cannot
// parse as a valid char for a symbolNamed expression
class UninterpretedType extends TypeExpr {
    isPrimitiveType = true; // ? Yes, for the moment..
    isUninterpreted = true;
    isConstructor = false;
    readonly symbolName: string;
    static readonly symbolTable: Map<string, boolean> = new Map<string, boolean>(
        [["BType", true]]
    );
    constructor(symbolName: string) {
        super();
        this.symbolName = symbolName;
        if (!UninterpretedType.symbolTable.has(this.symbolName)) {
            UninterpretedType.symbolTable.set(this.symbolName, false);
        }
    }
    getType() {
        return this.symbolName;
    }
    getBosqueType() {
        return "B" + this.symbolName;
    }
    getAbstractType() {
        return "Term";
    }
}

class TermType extends TypeExpr {
    isPrimitiveType = true;
    isUninterpreted = false;
    isConstructor = false;
    constructor() {
        super();
    }
    getType() {
        return "Term";
    }
    getBosqueType() {
        return "BTerm";
    }
    getAbstractType() {
        return "Term";
    }
}

class TupleType extends TypeExpr {
    isPrimitiveType = false;
    isUninterpreted = false;
    isConstructor = true;
    readonly elements: TypeExpr[];
    constructor(elements: TypeExpr[]) {
        super();
        this.elements = elements;
    }
    getType() {
        return "[" + this.elements.map(x => x.getType()).join(", ") + "]";
    }
    getBosqueType() {
        return "BTuple";
    }
    getAbstractType() {
        return "Term";
    }
}

class RecordType extends TypeExpr {
    isPrimitiveType = false;
    isUninterpreted = false;
    isConstructor = true;
    readonly elements: [string, TypeExpr][];
    constructor(elements: [string, TypeExpr][]) {
        super()
        this.elements = elements;
    }
    getType() {
        return "{" + this.elements.map(x => x[0] + ":" + x[1].getType()).join(", ") + "}";
    }
    getBosqueType() {
        return "BRecord";
    }
    getAbstractType() {
        return "Term";
    }
}

class RecordPropertyType extends TypeExpr {
    isPrimitiveType = true;
    isUninterpreted = false;
    isConstructor = false;
    getType() {
        return "RecordProperty"
    }
    getBosqueType() {
        return "RecordProperty";
    }
    getAbstractType() {
        return "RecordProperty";
    }
}

class LambdaType extends TypeExpr {
    isPrimitiveType = false;
    isUninterpreted = false;
    isConstructor = true;
    readonly args: [string, TypeExpr][];
    readonly result: TypeExpr;
    constructor(args: [string, TypeExpr][], result: TypeExpr) {
        super()
        this.args = args;
        this.result = result;
    }
    getType() {
        return "(" + this.args.map(x => x[0] + ":" + x[1].getType()).join(", ") + ")" + " -> " + this.result.getType();
    }
    getBosqueType() {
        return "BLambda";
    }
    getAbstractType() {
        return "Term";
    }
}

export { TypeExpr, IntType, BoolType, StringType, NoneType, AnyType, SomeType, FuncType, UninterpretedType, UnionType, TermType, TupleType, RecordType, LambdaType, RecordPropertyType };