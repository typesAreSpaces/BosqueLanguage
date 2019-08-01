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

abstract class TypeExpr {
    abstract getFStarType(): string;
    abstract getBosqueType(): string;
    static print(fd: number): void {
        // TODO: Include more classese that need
        // to be declared in the FStar prelude file
        UnionType.isDeclared.forEach((_, index) => {
            UnionType.fstarDeclaration(fd, index);
        })
        TupleType.isDeclared.forEach((_, index) => {
            TupleType.fstarDeclaration(fd, index);
        });
        RecordType.isDeclared.forEach((_, index) => {
            RecordType.fstarDeclaration(fd, index);
        });
    }
}

class IntType extends TypeExpr {
    getFStarType() {
        return "x:bosqueTerm{isInt x}";
    }
    getBosqueType() {
        return "NSCore::Int";
    }
}

class BoolType extends TypeExpr {
    getFStarType() {
        return "x:bosqueTerm{isBool x}";
    }
    getBosqueType() {
        return "NSCore::Bool";
    }
}

class StringType extends TypeExpr {
    getFStarType() {
        // FIX: This is wrong
        return "x:bosqueTerm{isString x}";
    }
    getBosqueType() {
        return "NSCore::String";
    }
}

class NoneType extends TypeExpr {
    getFStarType() {
        return "singletonBosqueNone";
    }
    getBosqueType() {
        return "None";
    }
}

// TODO: Implement getFStarType
class AnyType extends TypeExpr {
    getFStarType() {
        return "";
    }
    getBosqueType() {
        return "Any";
    }
}

// TODO: Implement getFStarType
class SomeType extends TypeExpr {
    getFStarType() {
        return "";
    }
    getBosqueType() {
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
    getFStarType() {
        return this.symbolName;
    }
    getBosqueType() {
        return this.symbolName;
    }
}

// TODO: Implement getBosqueType 
class FuncType extends TypeExpr {
    readonly domain: TypeExpr[];
    readonly image: TypeExpr;

    constructor(domain: TypeExpr[], image: TypeExpr) {
        super();
        this.domain = domain;
        this.image = image;
    }
    getFStarType() {
        return ((this.domain.length == 0) ? "" : this.domain.map(x => x.getFStarType()).join(" -> ") + " -> Tot ")
            + this.image.getFStarType();
    }
    getBosqueType() {
        return "";
    }
}

class UnionType extends TypeExpr {
    static readonly isDeclared: Set<string> = new Set<string>();
    readonly signature: string;
    readonly symbolName: string;
    readonly elements: Set<TypeExpr> = new Set<TypeExpr>();

    constructor(elements: Set<TypeExpr>) {
        super();
        this.signature = Array.from(elements).map(x => x.getFStarType()).join("0");
        this.symbolName = "union__" + this.signature;
        this.elements = elements;
        UnionType.isDeclared.add(this.signature);
    }
    getFStarType() {
        return "(" + this.symbolName
            + " " + Array.from(this.elements).map(x => x.getFStarType()).join(" ")
            + ")";
    }
    getBosqueType() {
        if (this.elements.size === 0) {
            return "Empty";
        }
        else {
            return Array.from(this.elements).map(x => x.getBosqueType()).join(" | ");
        }
    }
    static fstarDeclaration(fd: number, signature: string): void {
        const symbolName = "union__" + signature;
        const stringTypes = signature.split("0");
        const length = stringTypes.length;
        const actualStringType = symbolName + " " + stringTypes.join(" ");
        // * Type Definition
        // ** Type name ---------------------------------
        FS.writeSync(fd, "type " + symbolName + ":");
        for (let index = 0; index < length; ++index) {
            FS.writeSync(fd, " Type ->");
        }
        FS.writeSync(fd, "Type =\n");
        // ----------------------------------------------
        // ** Injections --------------------------------
        const injectionDeclaration = (stringType: string) => {
            return "| Inject" + stringType + "from" + signature + ": x : " + stringType + " -> " + actualStringType + "\n";
        }
        stringTypes.map(x => FS.writeSync(fd, injectionDeclaration(x)));
        FS.writeSync(fd, "\n");
        // ----------------------------------------------
        // ** Projections
        const projectionDeclaration = (stringType: string) => {
            const projectionName = "project" + stringType + "from" + signature;
            const injectionName = "Inject" + stringType + "from" + signature;
            const valPart = "val " + projectionName + " : (" + actualStringType + ") -> bosqueOption " + stringType;
            const letPart = "let " + projectionName + " x = match x with\n| " + injectionName + " x -> BosqueSome x\n| _ -> BosqueNone";
            return valPart + "\n" + letPart + "\n\n";
        };
        stringTypes.map(x => FS.writeSync(fd, projectionDeclaration(x)));
        // ----------------------------------------------
    }
}

// TODO: Implement getBosqueType
class TupleType extends TypeExpr {
    static readonly isDeclared: Set<number> = new Set<number>();
    readonly length: number;
    readonly symbolName: string;
    readonly elements: TypeExpr[];

    constructor(elements: TypeExpr[]) {
        super();
        this.length = elements.length;
        this.symbolName = "tuple__" + this.length;
        this.elements = elements;
        TupleType.isDeclared.add(this.length);
    }
    getFStarType() {
        return "(" + this.symbolName
            + " " + this.elements.map(x => x.getFStarType()).join(" ")
            + ")";
    }
    getBosqueType() {
        return "";
    }
    static fstarDeclaration(fd: number, length: number): void {
        const symbolName = "tuple__" + length;
        FS.writeSync(fd, "type " + symbolName);
        for (let index = 1; index <= length; ++index) {
            FS.writeSync(fd, " (t_" + index + " : Type)");
        }
        FS.writeSync(fd, " =\n");
        FS.writeSync(fd, "| Mk" + symbolName + ":")
        for (let index = 1; index <= length; ++index) {
            FS.writeSync(fd, " _" + index + ":t_" + index + " ->");
        }
        FS.writeSync(fd, " " + symbolName);
        for (let index = 1; index <= length; ++index) {
            FS.writeSync(fd, " t_" + index);
        }
        FS.writeSync(fd, " \n\n");
    }
}

// TODO: Implement getBosqueType
class RecordType extends TypeExpr {
    static readonly isDeclared: Set<string> = new Set<string>();
    readonly signature: string;
    readonly symbolName: string;
    readonly elements: [string, TypeExpr][];

    constructor(elements: [string, TypeExpr][]) {
        super()
        this.signature = elements.map(x => x[0]).join("_");
        this.symbolName = "record__" + this.signature;
        this.elements = elements;
        RecordType.isDeclared.add(this.signature);
    }
    getFStarType() {
        return "(" + this.symbolName
            + " " + this.elements.map(x => x[1].getFStarType()).join(" ")
            + ")";
    }
    getBosqueType() {
        return "";
    }
    static fstarDeclaration(fd: number, signature: string): void {
        const symbolName = "record__" + signature;
        const keys = signature.split("_");
        const length = keys.length;
        FS.writeSync(fd, "type " + symbolName);
        for (let index = 1; index <= length; ++index) {
            FS.writeSync(fd, " (t_" + index + " : Type)");
        }
        FS.writeSync(fd, " =\n");
        FS.writeSync(fd, "| Mk" + symbolName + ":")
        for (let index = 1; index <= length; ++index) {
            FS.writeSync(fd, " " + keys[index - 1] + ":t_" + index + " ->");
        }
        FS.writeSync(fd, " " + symbolName);
        for (let index = 1; index <= length; ++index) {
            FS.writeSync(fd, " t_" + index);
        }
        FS.writeSync(fd, " \n\n");
    }
}

// TODO: Implement getFStarType
// TODO: Implement getBosqueType
// TODO: Implement fstarDeclaration
class ConstructorType extends TypeExpr {
    constructor() {
        super();
    }
    getFStarType() {
        return "";
    }
    getBosqueType() {
        return "";
    }
    static fstarDeclaration(fd: number): void {
        FS.writeSync(fd, "");
    }
}

// TODO: Implement getFStarType
// TODO: Implement getBosqueType
// TODO: Implement fstarDeclaration
class LambdaType extends TypeExpr {
    readonly args: [string, TypeExpr][];
    readonly result: TypeExpr;

    constructor(args: [string, TypeExpr][], result: TypeExpr) {
        super()
        this.args = args;
        this.result = result;
    }
    getFStarType() {
        return "";
        // return "(" + this.args.map(x => x[0] + ":" + x[1].getFStarType()).join(", ") + ")" + " -> " + this.result.getFStarType();
    }
    getBosqueType() {
        return "";
    }
    static fstarDeclaration(): string {
        return "";
    }
}

class OptionalType extends TypeExpr {
    readonly ty : TypeExpr;

    constructor(ty : TypeExpr){
        super();
        this.ty = ty;
    }
    getFStarType(){
        return "";
    }
    getBosqueType(){
        return "";
    }
}
export { TypeExpr, IntType, BoolType, StringType, NoneType, AnyType, SomeType, FuncType, UninterpretedType, UnionType, TupleType, RecordType, ConstructorType, LambdaType, OptionalType };