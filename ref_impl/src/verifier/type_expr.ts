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
    abstract readonly isPrimitiveType : boolean;
    abstract getType() : string;
}

class IntType extends TypeExpr {
    isPrimitiveType = true;
    getType() {
        return "Int";
    }
}

class BoolType extends TypeExpr {
    isPrimitiveType = true;
    getType(){
        return "Bool";
    }
}

class StringType extends TypeExpr {
    isPrimitiveType = true;
    getType() {
        return "String";
    }
}

class FuncType extends TypeExpr {
    isPrimitiveType = false;
    readonly domain : TypeExpr[];
    readonly image : TypeExpr;
    constructor(domain : TypeExpr[], image  : TypeExpr){
        super();
        this.domain = domain;
        this.image = image;
    }
    getType(){
        if(this.domain.length == 0){
            return "() " + this.image.getType();
        }
        else{
            return "(" + this.domain.slice(1).reduce((a, b) => a + " " + 
            (b.isPrimitiveType ? b.getType() : (b as FuncType).image.getType()), 
            this.domain[0].isPrimitiveType ? this.domain[0].getType() : (this.domain[0] as FuncType).image.getType())
            + ") " + this.image.getType();
        }
    }
}

export { TypeExpr, IntType, BoolType, StringType, FuncType };