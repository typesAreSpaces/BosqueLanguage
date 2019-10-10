//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";

abstract class TypeExpr {
    // String expression denoting the type 
    // used inside function declaration in FStar
    readonly id: string;
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
        // ----------------------------
        // This needs to be reorganized

        TypedStringType.declared.forEach(x => {
            // Adding bTypedStringType at the beginning here is necessary
            // because TypedStringType.declared only keeps track of the elements
            // of the constructor type
            FS.writeSync(fd, `let bTypedStringType_${x} = (BTypedStringType ${x})\n`);
        });

        TupleType.mapDeclared.forEach((_, x) => {
            const [b, typeArray] = TupleType.mapDeclared.get(x) as [boolean, TypeExpr[]];
            const dimension = typeArray.length;
            // Here the index contains the constructor information
            // Hence, the constructor information is not added
            FS.writeSync(fd, `let ${x} = BTupleType ${b} ${dimension} ${TupleType.toFStarTuple(typeArray)}\n`);
        });

        UnionType.mapDeclared.forEach((_, x) => {
            // Here the index contains the constructor information
            // Hence, the constructor information is not added
            FS.writeSync(fd, `let ${x} = ${UnionType.toFStarUnion(UnionType.mapDeclared.get(x) as TypeExpr[])}\n`);
        });

        
        // ----------------------------
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
    static mapDeclared: Map<string, TypeExpr[]> = new Map<string, TypeExpr[]>();
    readonly elements: Set<TypeExpr> = new Set<TypeExpr>();

    constructor(elements: Set<TypeExpr>) {
        super("bUnionType_" + Array.from(elements).sort().map(x => x.getFStarTypeName()).join("_"));
        this.elements = elements;
        if (UnionType.mapDeclared.get(this.id) == undefined) {
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
        super("bTypedStringType_" + ty.getFStarTypeName());
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
}

class TupleType extends TypeExpr {
    static mapDeclared: Map<string, [boolean, TypeExpr[]]> = new Map<string, [boolean, TypeExpr[]]>();
    readonly isOpen: boolean;
    readonly elements: TypeExpr[];

    constructor(isOpen: boolean, elements: TypeExpr[]) {
        super("bTupleType_" + elements.length + elements.map(x => x.getFStarTypeName()).join("_") + isOpen);
        this.isOpen = isOpen;
        this.elements = elements;
        if (TupleType.mapDeclared.get(this.id) == undefined) {
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
            return "(SCons " + types[0].getFStarTypeName() + " "
                + (types.length - 1) + " " + this.toFStarTuple(tail) + ")";
        }
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

export {
    TypeExpr,
    AnyType, SomeType, TruthyType,
    NoneType, UnionType, BoolType,
    IntType, TypedStringType, TupleType,
    RecordType, FuncType, ObjectType,
    EnumType, CustomKeyType, KeyedType
}; 