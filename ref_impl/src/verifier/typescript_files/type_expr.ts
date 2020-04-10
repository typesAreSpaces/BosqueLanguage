//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import { sanitizeName, toFStarSequence } from "./util";

abstract class TypeDecl {
    readonly string_type: string;
    constructor(string_type: string) {
        this.string_type = string_type;
    }
    abstract emit(fd: number): void;
}

class TypedStringTypeDecl extends TypeDecl {
    constructor(string_type: string) {
        super(string_type);
    }
    emit(fd: number) {
        // Adding bTypedStringType at the beginning here is necessary
        // because TypedStringType.declared only keeps track of the elements
        // of the constructor type
        FS.writeSync(fd, `let bTypedStringType_${this.string_type} = (BTypedStringType ${this.string_type})\n`);
    }
}

class TupleTypeDecl extends TypeDecl {
    readonly b: boolean;
    readonly type_array: TypeExpr[];
    constructor(string_type: string, b: boolean, type_array: TypeExpr[]) {
        super(string_type);
        this.b = b;
        this.type_array = type_array;
    }
    emit(fd: number) {
        // Here the index contains the constructor information
        // Hence, the constructor information is not added  
        FS.writeSync(fd, `let ${this.string_type} = BTupleType ${this.b} ${this.type_array.length} ${TupleType.toFStarTuple(this.type_array)}\n`);
    }
}

class RecordTypeDecl extends TypeDecl {
    readonly b: boolean;
    readonly field_names: string[];
    readonly type_array: TypeExpr[];
    constructor(string_type: string, b: boolean, field_names: string[], type_array: TypeExpr[]) {
        super(string_type);
        this.b = b;
        this.field_names = field_names;
        this.type_array = type_array;
    }
    emit(fd: number) {
        FS.writeSync(fd, `let ${this.string_type} = BRecordType ${this.b} ${this.type_array.length} ${RecordType.toFStarRecord(this.field_names, this.type_array)}\n`);
    }
}

class UnionTypeDecl extends TypeDecl {
    readonly type_array: TypeExpr[];
    constructor(string_type: string, type_array: TypeExpr[]) {
        super(string_type);
        this.type_array = type_array;
    }
    emit(fd: number) {
        // Here the index contains the constructor information
        // Hence, the constructor information is not added
        FS.writeSync(fd, `let ${this.string_type} = ${UnionType.toFStarUnion(this.type_array)}\n`);
    }
}

class ListTypeDecl extends TypeDecl {
    constructor(string_type: string) {
        super(string_type);
    }
    emit(fd: number) {
        FS.writeSync(fd, `let bListType_${this.string_type} = (BListType ${this.string_type})\n`);
    }
}

// --------------------------------------------------------

abstract class TypeExpr {
    // id is a string expression denoting the type 
    // used inside function declaration in FStar
    readonly id: string;
    static declarator = new Set<TypeDecl>();
    constructor(id: string) {
        this.id = id;
    }
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf " + this.id + " (getType x)})";
    }
    // String name associated to the type in (MIR) Bosque
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
    getBosqueType() {
        return "NSCore::Any";
    }
}

class SomeType extends TypeExpr {
    constructor() {
        super("BSomeType");
    }
    getBosqueType() {
        return "NSCore::Some";
    }
}

class TruthyType extends TypeExpr {
    constructor() {
        super("BTruthyType");
    }
    getBosqueType() {
        return "NSCore::Truthy";
    }
}

class NoneType extends TypeExpr {
    constructor() {
        super("BNoneType");
    }
    getBosqueType() {
        return "NSCore::None";
    }
}

class UnionType extends TypeExpr {
    static declared: Set<string> = new Set<string>();
    readonly elements: Set<TypeExpr> = new Set<TypeExpr>();

    constructor(elements: Set<TypeExpr>) {
        super("bUnionType_" + Array.from(elements).sort().map(x => x.id).join("_"));
        this.elements = elements;
        // --------------------------------------------------------------------------------
        if (!UnionType.declared.has(this.id)) {
            UnionType.declared.add(this.id);
            TypeExpr.declarator.add(new UnionTypeDecl(this.id, Array.from(elements).sort()));
        }
        // -------------------------------------------------------------------------------- 
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
                + x[0].id
                + " " + x[1].id + ")"
        }
        else {
            if (x.length < 2) {
                throw new Error("UnionType expected two or more types");
            }
            else {
                const tail = x.slice(1);
                return "(BUnionType " + x[0].id + " " + UnionType.toFStarUnion(tail) + ")";
            }
        }
    }
}

class ParsableType extends TypeExpr {
    constructor() {
        super("BParsableType");
    }
    getBosqueType() {
        return "NSCore::Parsable";
    }
}

class BoolType extends TypeExpr {
    constructor() {
        super("BBoolType");
    }
    getBosqueType() {
        return "NSCore::Bool";
    }
}

class IntType extends TypeExpr {
    constructor() {
        super("BIntType");
    }
    getBosqueType() {
        return "NSCore::Int";
    }
}

class TypedStringType extends TypeExpr {
    static declared: Set<string> = new Set<string>();
    readonly ty: TypeExpr;
    constructor(ty: TypeExpr) {
        const string_type = ty.id;
        super("bTypedStringType_" + string_type);
        this.ty = ty;
        // --------------------------------------------------------------------------------
        if (!TypedStringType.declared.has(string_type)) {
            TypedStringType.declared.add(string_type);
            TypeExpr.declarator.add(new TypedStringTypeDecl(string_type));
        }
        // --------------------------------------------------------------------------------
    }
    getBosqueType() {
        return "NSCore::String<T=" + this.ty.getBosqueType() + ">";
    }
}

class GUIDType extends TypeExpr {
    constructor() {
        super("BGUIDType");
    }
    getBosqueType() {
        return "NSCore::GUID";
    }
}

class TupleType extends TypeExpr {
    static declared: Set<string> = new Set<string>();
    readonly is_open: boolean;
    readonly elements: TypeExpr[];

    constructor(is_open: boolean, elements: TypeExpr[]) {
        super("bTupleType_" + elements.length + elements.map(x => x.id).join("_") + is_open);
        this.is_open = is_open;
        this.elements = elements;
        // --------------------------------------------------------------------------------
        if (!TupleType.declared.has(this.id)) {
            TupleType.declared.add(this.id);
            TypeExpr.declarator.add(new TupleTypeDecl(this.id, this.is_open, this.elements));
        }
        // --------------------------------------------------------------------------------
    }
    getBosqueType() {
        return "[" + this.elements.map(x => x.getBosqueType()).join(", ") + "]";
    }

    static toFStarTuple(types: TypeExpr[]): string {
        return toFStarSequence(types.map(x => x.id));
    }
}

class RecordType extends TypeExpr {
    static declared: Set<string> = new Set<string>();
    readonly is_open: boolean;
    readonly field_names: string[];
    readonly elements: TypeExpr[];

    constructor(is_open: boolean, field_names: string[], elements: TypeExpr[]) {
        super("bRecordType_" + elements.length + elements.map((value, index) => field_names[index].slice(1, -1) + value.id).join("_") + is_open);
        this.is_open = is_open
        this.field_names = field_names.map(x => "\"" + x + "\"");
        this.elements = elements;
        // --------------------------------------------------------------------------------
        if (!RecordType.declared.has(this.id)) {
            RecordType.declared.add(this.id);
            TypeExpr.declarator.add(new RecordTypeDecl(this.id, this.is_open, this.field_names, this.elements));
        }
        // --------------------------------------------------------------------------------
    }
    getBosqueType() {
        return "{" + this.field_names.map((value, index) => value + ":" + this.elements[index].getBosqueType()).join(", ") + "}";
    }

    static toFStarRecord(fields: string[], types: TypeExpr[]): string {
        return toFStarSequence(fields) + " " + toFStarSequence(types.map(x => x.id));
    }
}

// TODO: Implement getBosqueType 
class FuncType extends TypeExpr {
    readonly domain: TypeExpr[];
    readonly image: TypeExpr;

    constructor(domain: TypeExpr[], image: TypeExpr) {
        super("BFunctionType");
        this.domain = domain;
        this.image = image;
    }
    valDeclare() {
        return ((this.domain.length == 0) ? "" : this.domain.map(x => x.getFStarTerm()).join(" -> ") + " -> Tot ")
            + this.image.getFStarTerm();
    }
    getBosqueType() {
        return "";
    }
}

class ObjectType extends TypeExpr {
    constructor() {
        super("BObjectType");
    }
    getBosqueType() {
        return "NSCore::Object";
    }
}

// TODO: Implement getBosqueType 
class EnumType extends TypeExpr {
    constructor() {
        super("BEnumType");
    }
    getBosqueType() {
        return "";
    }
}

// TODO: Implement getBosqueType 
class CustomKeyType extends TypeExpr {
    constructor() {
        super("BCustomKeyType");
    }
    getBosqueType() {
        return "";
    }
}

// TODO: Implement getBosqueType 
class KeyedType extends TypeExpr {
    constructor() {
        super("BKeyedType");
    }
    getBosqueType() {
        return "";
    }
}

// TODO: Implement getBosqueType 
class ConstructorType extends TypeExpr {
    readonly fields: [string, TypeExpr][];
    readonly original_name: string;

    constructor(constructorName: string, fields: [string, TypeExpr][]) {
        super("B" + sanitizeName(constructorName) + "Type");
        this.fields = fields;
        this.original_name = constructorName
    }
    getBosqueType() {
        return this.original_name;
    }
}

class ListType extends TypeExpr {
    static declared: Set<string> = new Set<string>();
    readonly ty: TypeExpr;
    constructor(ty: TypeExpr) {
        const string_type = ty.id;
        super("bListType_" + string_type);
        this.ty = ty;
        // --------------------------------------------------------------------------------
        if (!ListType.declared.has(string_type)) {
            ListType.declared.add(string_type);
            ListType.declarator.add(new ListTypeDecl(string_type));
        }
        // --------------------------------------------------------------------------------
    }
    getBosqueType() {
        return "NSCore::List<T=" + this.ty.getBosqueType() + ">";
    }
}

export {
    TypeExpr,
    AnyType, SomeType, TruthyType,
    NoneType, UnionType, ParsableType, BoolType,
    IntType, TypedStringType, GUIDType, TupleType,
    RecordType, FuncType, ObjectType,
    EnumType, CustomKeyType, KeyedType,
    ConstructorType, ListType
}; 
