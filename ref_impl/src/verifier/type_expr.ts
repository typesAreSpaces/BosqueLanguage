//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";

abstract class TypeExpr {
    // String expression denoting the type 
    // used inside function declaration in FStar
    readonly id : string;
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
    static declare_additional_types(fd: number): void {
        TypedStringType.declared.forEach(x => {
            FS.writeSync(fd, `let bTypeStringType_${x} = (BTypedStringType ${x})\n`);
        });
        FS.writeSync(fd, "\n");
        UnionType.declared.forEach(x => {
            FS.writeSync(fd, `let bUnionType_${x} = ${UnionType.toFStarUnion(UnionType.mapDeclared.get(x) as TypeExpr[])}\n`);
        });
        FS.writeSync(fd, "\n");
        TupleType.declared.forEach(x => {
            const [b, typeArray] = TupleType.mapDeclared.get(x) as [boolean, TypeExpr[]];
            const dimension = typeArray.length;
            FS.writeSync(fd, `let bTupleType_${x} = BTupleType ${b} ${dimension} ${TupleType.toFStarTuple(typeArray)}\n`);
        });
        FS.writeSync(fd, "\n");

        FS.writeSync(fd, "\n");
    }
    abstract equalTo(ty: TypeExpr): boolean;
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
    equalTo(ty: TypeExpr) {
        if (ty instanceof AnyType) {
            return true;
        }
        return false;
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
    equalTo(ty: TypeExpr) {
        if (ty instanceof SomeType) {
            return true;
        }
        return false;
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
        return "(bosqueTerm)";
    }
    getBosqueType() {
        return "NSCore::Truthy";
    }
    equalTo(ty: TypeExpr) {
        if (ty instanceof TruthyType) {
            return true;
        }
        return false;
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
    equalTo(ty: TypeExpr) {
        if (ty instanceof NoneType) {
            return true;
        }
        return false;
    }
}

class UnionType extends TypeExpr {
    static declared: Set<string> = new Set<string>();
    static mapDeclared: Map<string, TypeExpr[]> = new Map<string, TypeExpr[]>();
    readonly elements: Set<TypeExpr> = new Set<TypeExpr>();

    constructor(elements: Set<TypeExpr>) {
        super("bUnionType_" + Array.from(elements).sort().map(x => x.getFStarTypeName()).join("_"));
        this.elements = elements;
        if (!UnionType.declared.has(this.id)) {
            UnionType.declared.add(this.id);
            UnionType.mapDeclared.set(this.id, Array.from(elements).sort());
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
    equalTo(ty: TypeExpr): boolean {
        if (ty instanceof UnionType) {
            return this.id == ty.id;
        }
        return false;
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
    equalTo(ty: TypeExpr) {
        if (ty instanceof BoolType) {
            return true;
        }
        return false;
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
    equalTo(ty: TypeExpr) {
        if (ty instanceof IntType) {
            return true;
        }
        return false;
    }
}

class TypedStringType extends TypeExpr {
    static declared: Set<string> = new Set<string>();
    readonly ty: TypeExpr;
    constructor(ty: TypeExpr) {
        super("bTypeStringType_" + ty.getFStarTypeName());
        this.ty = ty;
        const stringType = ty.getFStarTypeName();
        if (!TypedStringType.declared.has(stringType)) {
            TypedStringType.declared.add(stringType);
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
    equalTo(ty: TypeExpr): boolean {
        if (ty instanceof TypedStringType) {
            return this.ty.equalTo(ty.ty);
        }
        return false;
    }
}

class TupleType extends TypeExpr {
    static declared: Set<string> = new Set<string>();
    static mapDeclared: Map<string, [boolean, TypeExpr[]]> = new Map<string, [boolean, TypeExpr[]]>();
    readonly isOpen: boolean;
    readonly elements: TypeExpr[];

    constructor(isOpen: boolean, elements: TypeExpr[]) {
        super("bTupleType_" + elements.length + elements.map(x => x.getFStarTypeName()).join("_") + isOpen);
        this.isOpen = isOpen;
        this.elements = elements;
        if (!TupleType.declared.has(this.id)) {
            TupleType.declared.add(this.id);
            TupleType.mapDeclared.set(this.id,
                [this.isOpen, this.elements]);
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
        if (types.length == 0) {
            return "SNil";
        }
        else {
            const tail = types.slice(1);
            return "(SCons " + types[0].getFStarTypeName() + " " + this.toFStarTuple(tail) + ")";
        }
    }
    equalTo(ty: TypeExpr): boolean {
        if (ty instanceof TupleType) {
            if (this.elements.length != ty.elements.length) {
                return false;
            }
            else {
                for (let index = 0; index < this.elements.length; ++index) {
                    if (!(this.elements[index].equalTo(ty.elements[index]))) {
                        return false;
                    }
                }
                return true;
            }
        }
        return false;
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
    equalTo(ty: TypeExpr): boolean {
        if (ty instanceof RecordType) {
            if (this.elements.length != ty.elements.length) {
                return false;
            }
            else {
                for (let index = 0; index < this.elements.length; ++index) {
                    let src = this.elements[index];
                    const target = ty.elements[index];
                    if (src[0] != target[0] || !(src[1].equalTo(target[1]))) {
                        return false;
                    }
                }
                return true;
            }
        }
        return false;
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
    equalTo(ty: TypeExpr): boolean {
        if (ty instanceof FuncType) {
            if (this.domain.length != ty.domain.length) {
                return false;
            }
            else {
                for (let index = 0; index < this.domain.length; ++index) {
                    if (!(this.domain[index].equalTo(ty.domain[index]))) {
                        return false;
                    }
                }
                return this.image.equalTo(ty.image);
            }
        }
        return false;
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
    equalTo(ty: TypeExpr) {
        if (ty instanceof ObjectType) {
            return true;
        }
        return false;
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
    equalTo(ty: TypeExpr) {
        if (ty instanceof EnumType) {
            return true;
        }
        return false;
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
    equalTo(ty: TypeExpr) {
        if (ty instanceof CustomKeyType) {
            return true;
        }
        return false;
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
    equalTo(ty: TypeExpr) {
        if (ty instanceof KeyedType) {
            return true;
        }
        return false;
    }
}

export {
    TypeExpr,
    AnyType, SomeType, TruthyType,
    NoneType, UnionType, BoolType,
    IntType, TypedStringType, TupleType,
    RecordType, FuncType, ObjectType,
    EnumType, CustomKeyType, KeyedType
}; 