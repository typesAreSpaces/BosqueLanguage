//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";

abstract class TypeExpr {
    // String expression denoting the type 
    // used inside function declaration in FStar
    abstract getFStarTerm(): string;
    // String name associated to the type in FStar
    abstract getFStarType(): string;
    // String name associated to the type in Bosque
    abstract getBosqueType(): string;
    static declare_additional_types(fd: number): void {
        TypedStringType.declared.forEach(x => {
            FS.writeSync(fd, `let bTypeStringType_${x} = \
            (BTypedStringType ${x})\n`);
        });
        UnionType.declared.forEach(x => {
            FS.writeSync(fd, `let bUnionType_${x} = \
            ${UnionType.toFStarUnion(UnionType.mapDeclared.get(x) as TypeExpr[])}\n`);
        });
        FS.writeSync(fd, "\n");
    }
    abstract equalTo(ty: TypeExpr): boolean;
}

class AnyType extends TypeExpr {
    getFStarTerm() {
        return "(bosqueTerm)";
    }
    getFStarType() {
        return "BAnyType";
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
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf BSomeType (getType x)})";
    }
    getFStarType() {
        return "BSomeType";
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
    getFStarTerm() {
        return "(bosqueTerm)";
    }
    getFStarType() {
        return "BTruthyType";
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
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf BNoneType (getType x)})";
    }
    getFStarType() {
        return "BNoneType";
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

// TODO
class UnionType extends TypeExpr {
    static declared: Set<string> = new Set<string>();
    static mapDeclared: Map<string, TypeExpr[]> = new Map<string, TypeExpr[]>();
    readonly elements: Set<TypeExpr> = new Set<TypeExpr>();
    readonly stringTypes: string;

    constructor(elements: Set<TypeExpr>) {
        super();
        this.elements = elements;
        const types = Array.from(elements).sort();
        this.stringTypes = types.map(x => x.getFStarType()).join("_");
        if (!UnionType.declared.has(this.stringTypes)) {
            console.log(this.stringTypes);
            UnionType.declared.add(this.stringTypes);
            UnionType.mapDeclared.set(this.stringTypes, types);
        }
    }
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf " + this.getFStarType() + " (getType x)})";
    }
    getFStarType() {
        // CONTINUE:
        return "bUnionType_" + this.stringTypes;
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
                + x[0].getFStarType()
                + " " + x[1].getFStarType() + ")"
        }
        else {
            if (x.length < 2) {
                throw new Error("UnionType expected two or more types");
            }
            else {
                const tail = x.slice(1);
                return "(BUnionType " + x[0].getFStarType() + " " + UnionType.toFStarUnion(tail) + ")";
            }
        }
    }
    // FIX: This is incorrect
    equalTo(ty: TypeExpr) {
        if (ty instanceof UnionType) {
            return true;
        }
        return false;
    }
}

class BoolType extends TypeExpr {
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf BBoolType (getType x)})";
    }
    getFStarType() {
        return "BBoolType";
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
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf BIntType (getType x)})";

    }
    getFStarType() {
        return "BIntType";
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
        super();
        this.ty = ty;
        const stringType = ty.getFStarType();
        if (!TypedStringType.declared.has(stringType)) {
            TypedStringType.declared.add(stringType);
        }
    }
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf " + this.getFStarType() + " (getType x)})";
    }
    getFStarType() {
        return "bTypeStringType_" + this.ty.getFStarType();
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

// TODO: Needs testing
class TupleType extends TypeExpr {
    readonly isOpen: boolean;
    readonly elements: TypeExpr[];
    readonly types: string;

    constructor(isOpen: boolean, elements: TypeExpr[]) {
        super();
        this.isOpen = isOpen;
        this.elements = elements;
        this.types = TupleType.toFStarTuple(this.elements);
    }
    getFStarTerm() {
        return "(x:bosqueTerm{isTuple "
            + this.isOpen
            + " " + this.elements.length
            + " " + this.types
            + "})";
    }
    // getFStarType() {
    //     return "BTupleType"
    //         + " " + this.isOpen
    //         + " " + this.elements.length
    //         + " " + this.types;
    // }
    getFStarType() {
        return "bTupleType_"
            + this.isOpen + this.elements.length
            + this.types;
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
            return "(SCons " + types[0].getFStarType() + " " + this.toFStarTuple(tail) + ")";
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
        super();
        this.elements = elements;
    }
    getFStarTerm() {
        return "";
    }
    getFStarType() {
        // this.elements.map(x => x[1].getFStarType()).join(" ")
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
// TODO: Implement getFstarType, just double check 
class FuncType extends TypeExpr {
    readonly domain: TypeExpr[];
    readonly image: TypeExpr;

    constructor(domain: TypeExpr[], image: TypeExpr) {
        super();
        this.domain = domain;
        this.image = image;
    }
    getFStarTerm() {
        return ((this.domain.length == 0) ? "" : this.domain.map(x => x.getFStarTerm()).join(" -> ") + " -> Tot ")
            + this.image.getFStarTerm();
    }
    getFStarType() {
        return ((this.domain.length == 0) ? "" : this.domain.map(x => x.getFStarType()).join(" -> ") + " -> Tot ")
            + this.image.getFStarType();
    }
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
    getFStarTerm() {
        return "";
    }
    getFStarType() {
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
    getFStarTerm() {
        return "";
    }
    getFStarType() {
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
    getFStarTerm() {
        return "";
    }
    getFStarType() {
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
class KeyedType {
    getFStarTerm() {
        return "";
    }
    getFStarType() {
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