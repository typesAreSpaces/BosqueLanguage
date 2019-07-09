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
    readonly elements: TypeExpr[];
    constructor(elements: TypeExpr[]) {
        super();
        this.elements = elements;
    }
    getType() {
        return "[" + this.elements.map(x => x.getType()).join(", ") + "]";
    }
}

class RecordType extends TypeExpr {
    readonly elements: [string, TypeExpr][];
    constructor(elements: [string, TypeExpr][]) {
        super()
        this.elements = elements;
    }
    getType() {
        return "{" + this.elements.map(x => x[0] + ":" + x[1].getType()).join(", ") + "}";
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
    getType() {
        return "(" + this.args.map(x => x[0] + ":" + x[1].getType()).join(", ") + ")" + " -> " + this.result.getType();
    }
}

export { TypeExpr, IntType, BoolType, StringType, NoneType, AnyType, SomeType, FuncType, UninterpretedType, UnionType, TupleType, RecordType, LambdaType };