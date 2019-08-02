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
// the grouded ast and build a `table` using
abstract class TypeExpr {
    abstract getFStarTerm(): string;
    abstract getFStarType(): string;
    abstract getBosqueType(): string;
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
}

class SomeType extends TypeExpr {
    getFStarTerm() {
        return "(x:bosqueTerm{isSome x})";
    }
    getFStarType() {
        return "BSomeType";
    }
    getBosqueType() {
        return "NSCore::Some";
    }
}

// TODO: Implement getFStarTerm
class TruthyType extends TypeExpr {
    getFStarTerm() {
        return "";
    }
    getFStarType() {
        return "BTruthyType";
    }
    getBosqueType() {
        return "NSCore::Truthy";
    }
}

class NoneType extends TypeExpr {
    getFStarTerm() {
        return "(x:bosqueTerm{isNone x})";
    }
    getFStarType() {
        return "BNoneType";
    }
    getBosqueType() {
        return "NSCore::None";
    }
}

// TODO: Needs testing
class UnionType extends TypeExpr {
    readonly elements: Set<TypeExpr> = new Set<TypeExpr>();
    readonly types: string;

    constructor(elements: Set<TypeExpr>) {
        super();
        this.elements = elements;
        const canonical_order = Array.from(elements).sort();
        this.types = UnionType.toFStarUnion(canonical_order);
    }
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf " + this.types + " (getType x)})";
    }
    getFStarType() {
        return "BUnionType";

    }
    getBosqueType() {
        if (this.elements.size <= 2) {
            throw new Error("UnionType expected two or more types");
        }
        else {
            return Array.from(this.elements).map(x => x.getBosqueType()).join(" | ");
        }
    }
    static toFStarUnion(x : TypeExpr[]) : string {
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
}

class BoolType extends TypeExpr {
    getFStarTerm() {
        return "(x:bosqueTerm{isBool x})";
    }
    getFStarType() {
        return "BBoolType";
    }
    getBosqueType() {
        return "NSCore::Bool";
    }
}

class IntType extends TypeExpr {
    getFStarTerm() {
        return "(x:bosqueTerm{isInt x})";

    }
    getFStarType() {
        return "BIntType";
    }
    getBosqueType() {
        return "NSCore::Int";
    }
}

class TypedStringType extends TypeExpr {
    readonly ty: TypeExpr;
    constructor(ty: TypeExpr) {
        super();
        this.ty = ty;
    }
    getFStarTerm() {
        return "(x:bosqueTerm{isString " + this.ty.getFStarType() + " x})";
    }
    getFStarType() {
        return "(BTypeStringType " + this.ty.getFStarType() + ")";
    }
    getBosqueType() {
        return "NSCore::String<T=" + this.ty.getBosqueType() + ">";
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
            + this.elements.length
            + " " + this.types
            + "})";
    }
    getFStarType() {
        return "(BTupleType"
            + " " + this.isOpen
            + " " + this.elements.length
            + " " + this.types + ")";
    }
    getBosqueType() {
        return "[" + this.elements.map(x => x.getBosqueType()).join(" | ") + "]";
    }

    static toFStarTuple(types: TypeExpr[]) : string {
        if (types.length == 0){
            return "SNil";
        }
        else{
            const tail = types.slice(1);
            return "(SCons " + types[0].getFStarType() + " " + this.toFStarTuple(tail) + ")";
        }
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
}

// TODO:
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
}

// TODO:
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
}

// TODO:
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
}

// TODO:
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
}


export { TypeExpr,
    AnyType, SomeType, TruthyType,
    NoneType, UnionType, BoolType,
    IntType, TypedStringType, TupleType,
    RecordType, FuncType, ObjectType,
    EnumType, CustomKeyType, KeyedType
}; 