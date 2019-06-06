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
    abstract getType(): string;
    abstract getAbstractType() : string;
}

class IntType extends TypeExpr {
    isPrimitiveType = true;
    isUninterpreted = false;
    getType() {
        return "Int";
    }
    getAbstractType() {
        return "Term";
    }
}

class BoolType extends TypeExpr {
    isPrimitiveType = true;
    isUninterpreted = false;
    getType() {
        return "Bool";
    }
    getAbstractType() {
        return "Term";
    }
}

class StringType extends TypeExpr {
    isPrimitiveType = true;
    isUninterpreted = false;
    getType() {
        return "String";
    }
    getAbstractType() {
        return "Term";
    }
}

class FuncType extends TypeExpr {
    isPrimitiveType = false;
    isUninterpreted = false;
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
            return "(" + this.domain.slice(1).reduce((a, b) => a + " " +
                (b.isPrimitiveType ? b.getType() : (b as FuncType).image.getType()),
                this.domain[0].isPrimitiveType ? this.domain[0].getType() : (this.domain[0] as FuncType).image.getType())
                + ") " + this.image.getType();
        }
    }
    getAbstractType() : string{
        if (this.domain.length == 0) {
            return "() " + this.image.getAbstractType();
        }
        else {
            return "(" + this.domain.slice(1).reduce((a, b) => a + " " +
                (b.isPrimitiveType ? b.getAbstractType() : (b as FuncType).image.getAbstractType()),
                this.domain[0].isPrimitiveType ? this.domain[0].getAbstractType() : (this.domain[0] as FuncType).image.getAbstractType())
                + ") " + this.image.getAbstractType();
        }
    }
}

// The getType() of UnionType
// might have a collition name
// problem
// getType() implements idempotency --> Not really.
// TODO: Fix idempotecy using a Set structure
class UnionType extends TypeExpr {
    isPrimitiveType = false;
    isUninterpreted = false;
    readonly lhs : TypeExpr;
    readonly rhs : TypeExpr;
    constructor(lhs : TypeExpr, rhs : TypeExpr){
        super();
        this.lhs = lhs;
        this.rhs = rhs;
    }
    getType() {
        let lhsType = this.lhs.getType();
        let rhsType = this.rhs.getType();
        if(lhsType === rhsType){
            return lhsType;
        }
        else{
            return lhsType + "_" + rhsType;
        }
    }
    getAbstractType() {
        let lhsType = this.lhs.getAbstractType();
        let rhsType = this.rhs.getAbstractType();
        if(lhsType === rhsType){
            return lhsType;
        }
        else{
            return lhsType + "_" + rhsType;
        }
    }
}

// REMARK: Names cannot include `,'
// or any other symbol that Z3 cannot
// parse as a valid char for a named expression
class UninterpretedType extends TypeExpr {
    isPrimitiveType = true; // ? Yes, for the moment..
    isUninterpreted = true;
    readonly name: string;
    static readonly symbolTable: Map<string, boolean> = new Map<string, boolean>();
    constructor(name: string) {
        super();
        this.name = name;
        if (!UninterpretedType.symbolTable.has(this.name)) {
            UninterpretedType.symbolTable.set(this.name, false);
        }
    }
    getType() {
        return this.name;
    }
    getAbstractType() {
        return "Term";
    }
}

export { TypeExpr, IntType, BoolType, StringType, FuncType, UninterpretedType, UnionType };
