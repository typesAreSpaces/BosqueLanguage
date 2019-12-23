//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import { sanitizeName, toFStarSequence } from "./util";

abstract class TypeDecl {
    abstract emit(fd: number): void;
}

class TypedStringTypeDecl extends TypeDecl {
    readonly stringType: string;
    constructor(stringType: string) {
        super();
        this.stringType = stringType;
    }
    emit(fd: number) {
        // Adding bTypedStringType at the beginning here is necessary
        // because TypedStringType.declared only keeps track of the elements
        // of the constructor type
        FS.writeSync(fd, `let bTypedStringType_${this.stringType} = (BTypedStringType ${this.stringType})\n`);
    }
}

class TupleTypeDecl extends TypeDecl {
    readonly stringType: string;
    readonly b: boolean;
    readonly typeArray: TypeExpr[];
    constructor(stringType: string, b: boolean, typeArray: TypeExpr[]) {
        super();
        this.stringType = stringType;
        this.b = b;
        this.typeArray = typeArray;
    }
    emit(fd: number) {
        // Here the index contains the constructor information
        // Hence, the constructor information is not added  
        FS.writeSync(fd, `let ${this.stringType} = BTupleType ${this.b} ${this.typeArray.length} ${TupleType.toFStarTuple(this.typeArray)}\n`);
    }
}

class UnionTypeDecl extends TypeDecl {
    readonly stringType: string;
    readonly typeArray: TypeExpr[];
    constructor(stringType: string, typeArray: TypeExpr[]) {
        super();
        this.stringType = stringType;
        this.typeArray = typeArray;
    }
    emit(fd: number) {
        // Here the index contains the constructor information
        // Hence, the constructor information is not added
        FS.writeSync(fd, `let ${this.stringType} = ${UnionType.toFStarUnion(this.typeArray)}\n`);
    }
}


abstract class TypeExpr {
    // String expression denoting the type 
    // used inside function declaration in FStar
    readonly id: string;
    static declarator = new Set<TypeDecl>();
    constructor(id: string) {
        this.id = id;
    }
    abstract getFStarTerm(): string;
    // String name associated to the type in FStar
    getFStarTypeName(): string {
        return this.id;
    }
    // String name associated to the type in Bosque
    abstract getBosqueType(): string;
    
    static declareTypeNames(fd: number): void {
        TypeExpr.declarator.forEach(x => x.emit(fd));
    }
    equalTo(ty: TypeExpr): boolean {
        return this.id == ty.id;
    }
}

class AnyType extends TypeExpr {
    constructor() {
        super("BAnyType");
    }
    getFStarTerm() {
        return "(bosqueTerm)";
    }
    getBosqueType() {
        return "NSCore::Any";
    }
}

class SomeType extends TypeExpr {
    constructor() {
        super("BSomeType");
    }
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf BSomeType (getType x)})";
    }
    getBosqueType() {
        return "NSCore::Some";
    }
}

// getFStarTerm returns (bosqueTerm). Ideally,
// getFStarTerm should never be called on a TruthyType term
// because there is no such term. 
// Truthy is a concept, i.e. there is no term 
// with type TruthyType
class TruthyType extends TypeExpr {
    constructor() {
        super("BTruthyType");
    }
    getFStarTerm() {
        return "(bosqueTerm)"; // <- Does this need to be changed?
    }
    getBosqueType() {
        return "NSCore::Truthy";
    }
}

class NoneType extends TypeExpr {
    constructor() {
        super("BNoneType");
    }
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf BNoneType (getType x)})";
    }
    getBosqueType() {
        return "NSCore::None";
    }
}

class UnionType extends TypeExpr {
    static declared: Set<string> = new Set<string>();
    readonly elements: Set<TypeExpr> = new Set<TypeExpr>();

    constructor(elements: Set<TypeExpr>) {
        super("bUnionType_" + Array.from(elements).sort().map(x => x.getFStarTypeName()).join("_"));
        this.elements = elements;

        if (!UnionType.declared.has(this.id)) {
            UnionType.declared.add(this.id);
            TypeExpr.declarator.add(new UnionTypeDecl(this.id, Array.from(elements).sort()));
        }
    }
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf " + this.getFStarTypeName() + " (getType x)})";
    }
    getBosqueType() {
        if (this.elements.size <= 2) {
            throw new Error("UnionType expected two or more types");
        }
        else {
            return Array.from(this.elements).map(x => x.getBosqueType()).join(" | ");
        }
    }
    static toFStarUnion(x: TypeExpr[]): string {
        if (x.length == 2) {
            return "(BUnionType "
                + x[0].getFStarTypeName()
                + " " + x[1].getFStarTypeName() + ")"
        }
        else {
            if (x.length < 2) {
                throw new Error("UnionType expected two or more types");
            }
            else {
                const tail = x.slice(1);
                return "(BUnionType " + x[0].getFStarTypeName() + " " + UnionType.toFStarUnion(tail) + ")";
            }
        }
    }
}

class ParsableType extends TypeExpr {
    constructor(){
        super("BParsableType");
    }
    getFStarTerm(){
        return "(x:bosqueTerm{subtypeOf BParsableType (getType x)})";
    }
    getBosqueType(){
        return "NSCore::Parsable";
    }
}

class BoolType extends TypeExpr {
    constructor() {
        super("BBoolType");
    }
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf BBoolType (getType x)})";
    }
    getBosqueType() {
        return "NSCore::Bool";
    }
}

class IntType extends TypeExpr {
    constructor() {
        super("BIntType");
    }
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf BIntType (getType x)})";
    }
    getBosqueType() {
        return "NSCore::Int";
    }
}

class TypedStringType extends TypeExpr {
    static declared: Set<string> = new Set<string>();
    readonly ty: TypeExpr;
    constructor(ty: TypeExpr) {
        const stringType = ty.getFStarTypeName();
        super("bTypedStringType_" + stringType);
        this.ty = ty;
        if (!TypedStringType.declared.has(stringType)) {
            TypedStringType.declared.add(stringType);
            TypeExpr.declarator.add(new TypedStringTypeDecl(stringType));
        }
    }
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf "
            + this.getFStarTypeName()
            + " (getType x)})";
    }
    getBosqueType() {
        return "NSCore::String<T=" + this.ty.getBosqueType() + ">";
    }
}

class GUIDType extends TypeExpr{
    constructor(){
        super("bGUIDType");
    }
    getFStarTerm(){
        return "(x:bosqueTerm{subtypeOf BGUIDType (getType x)})";
    }
    getBosqueType(){
        return "NSCore::GUID";
    }
}

class TupleType extends TypeExpr {
    static declared: Set<string> = new Set<string>();
    readonly isOpen: boolean;
    readonly elements: TypeExpr[];

    constructor(isOpen: boolean, elements: TypeExpr[]) {
        super("bTupleType_" + elements.length + elements.map(x => x.getFStarTypeName()).join("_") + isOpen);
        this.isOpen = isOpen;
        this.elements = elements;
        if (!TupleType.declared.has(this.id)) {
            TupleType.declared.add(this.id);
            TypeExpr.declarator.add(new TupleTypeDecl(this.id, this.isOpen, this.elements))
        }
    }
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf "
            + this.getFStarTypeName()
            + " (getType x)})";
    }
    getBosqueType() {
        return "[" + this.elements.map(x => x.getBosqueType()).join(" | ") + "]";
    }

    static toFStarTuple(types: TypeExpr[]): string {
        // if (types.length == 0) {
        //     return "SNil";
        // }
        // else {
        //     const tail = types.slice(1);
        //     return "(SCons " + types[0].getFStarTypeName() + " "
        //         + (types.length - 1) + " " + this.toFStarTuple(tail) + ")";
        // }
        return toFStarSequence(types.map(x => x.getFStarTypeName()));
    }
}

// TODO: Implement getBosqueType
class RecordType extends TypeExpr {
    readonly elements: [string, TypeExpr][];

    constructor(elements: [string, TypeExpr][]) {
        super("bRecordType_");
        this.elements = elements;
    }
    getFStarTerm() {
        return "";
    }
    getBosqueType() {
        return "";
    }
}

// TODO: Implement getBosqueType 
// TODO: Implement getFStarTypeName, just double check 
class FuncType extends TypeExpr {
    readonly domain: TypeExpr[];
    readonly image: TypeExpr;

    constructor(domain: TypeExpr[], image: TypeExpr) {
        super("bFunctionType_");
        this.domain = domain;
        this.image = image;
    }
    getFStarTerm() {
        return ((this.domain.length == 0) ? "" : this.domain.map(x => x.getFStarTerm()).join(" -> ") + " -> Tot ")
            + this.image.getFStarTerm();
    }
    // getFStarTypeName() {
    //     return ((this.domain.length == 0) ? "" : this.domain.map(x => x.getFStarTypeName()).join(" -> ") + " -> Tot ")
    //         + this.image.getFStarTypeName();
    // }
    getBosqueType() {
        return "";
    }
}

// TODO: Proper mplementation
class ObjectType extends TypeExpr {
    constructor() {
        super("bObjectType_");
    }
    getFStarTerm() {
        return "";
    }
    getBosqueType() {
        return "";
    }
}

// TODO: Proper mplementation
class EnumType extends TypeExpr {
    constructor() {
        super("bEnumType_");
    }
    getFStarTerm() {
        return "";
    }
    getBosqueType() {
        return "";
    }
}

// TODO: Proper mplementation
class CustomKeyType extends TypeExpr {
    constructor() {
        super("bCustomKeyType_");
    }
    getFStarTerm() {
        return "";
    }
    getBosqueType() {
        return "";
    }
}

// TODO: Proper mplementation
class KeyedType extends TypeExpr {
    constructor() {
        super("bKeyedType");
    }
    getFStarTerm() {
        return "";
    }
    getBosqueType() {
        return "";
    }
}

// For the moment
// TODO: Proper implementation
class ConstructorType extends TypeExpr {
    readonly fields: [string, TypeExpr][];
    constructor(constructorName: string, fields: [string, TypeExpr][]) {
        super("B" + constructorName + "Type");
        this.fields = fields;
    }
    getFStarTerm() {
        const missingStuff = "";
        return "(x:bosqueTerm{subtypeOf B"
            + sanitizeName(this.id) + "Type " + missingStuff + "(getType x))";

    }
    getBosqueType() {
        return this.id;
    }
}

export {
    TypeExpr,
    AnyType, SomeType, TruthyType,
    NoneType, UnionType, ParsableType, BoolType,
    IntType, TypedStringType, GUIDType, TupleType,
    RecordType, FuncType, ObjectType,
    EnumType, CustomKeyType, KeyedType,
    ConstructorType
}; 