"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const util_1 = require("./util");
const type_decl_1 = require("./type_decl");
// --------------------------------------------------------
class TypeExpr {
    constructor(fstar_type_encoding) {
        this.fstar_type_encoding = fstar_type_encoding;
    }
    // getFStarTerm emits the refinement type in FStar
    // The latter is used for the FStar typing system
    getFStarTerm() {
        return "(x:bosqueTerm{subtypeOf " + this.fstar_type_encoding + " (getType x)})";
    }
    static declareTypeNames(fd) {
        TypeExpr.declarator.forEach(x => x.emit(fd));
    }
    equalTo(ty) {
        return this.fstar_type_encoding == ty.fstar_type_encoding;
    }
}
exports.TypeExpr = TypeExpr;
TypeExpr.declarator = new Set();
class AnyType extends TypeExpr {
    constructor() {
        super("BAnyType");
    }
    getBosqueType() {
        return "NSCore::Any";
    }
}
exports.AnyType = AnyType;
class SomeType extends TypeExpr {
    constructor() {
        super("BSomeType");
    }
    getBosqueType() {
        return "NSCore::Some";
    }
}
exports.SomeType = SomeType;
class TruthyType extends TypeExpr {
    constructor() {
        super("BTruthyType");
    }
    getBosqueType() {
        return "NSCore::Truthy";
    }
}
exports.TruthyType = TruthyType;
class NoneType extends TypeExpr {
    constructor() {
        super("BNoneType");
    }
    getBosqueType() {
        return "NSCore::None";
    }
}
exports.NoneType = NoneType;
class UnionType extends TypeExpr {
    constructor(elements) {
        super("bUnionType_" + Array.from(elements).sort().map(x => x.fstar_type_encoding).join("_"));
        this.elements = new Set();
        this.elements = elements;
        // --------------------------------------------------------------------------------
        if (!UnionType.declared.has(this.fstar_type_encoding)) {
            UnionType.declared.add(this.fstar_type_encoding);
            TypeExpr.declarator.add(new type_decl_1.UnionTypeDecl(this.fstar_type_encoding, Array.from(elements).sort()));
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
}
exports.UnionType = UnionType;
UnionType.declared = new Set();
class ParsableType extends TypeExpr {
    constructor() {
        super("BParsableType");
    }
    getBosqueType() {
        return "NSCore::Parsable";
    }
}
exports.ParsableType = ParsableType;
class BoolType extends TypeExpr {
    constructor() {
        super("BBoolType");
    }
    getBosqueType() {
        return "NSCore::Bool";
    }
}
exports.BoolType = BoolType;
class IntType extends TypeExpr {
    constructor() {
        super("BIntType");
    }
    getBosqueType() {
        return "NSCore::Int";
    }
}
exports.IntType = IntType;
class TypedStringType extends TypeExpr {
    constructor(ty) {
        const type_string_encoding = ty.fstar_type_encoding;
        super("bTypedStringType_" + type_string_encoding);
        this.ty = ty;
        // --------------------------------------------------------------------------------
        if (!TypedStringType.declared.has(type_string_encoding)) {
            TypedStringType.declared.add(type_string_encoding);
            TypeExpr.declarator.add(new type_decl_1.TypedStringTypeDecl(type_string_encoding));
        }
        // --------------------------------------------------------------------------------
    }
    getBosqueType() {
        return "NSCore::String<T=" + this.ty.getBosqueType() + ">";
    }
}
exports.TypedStringType = TypedStringType;
TypedStringType.declared = new Set();
class GUIDType extends TypeExpr {
    constructor() {
        super("BGUIDType");
    }
    getBosqueType() {
        return "NSCore::GUID";
    }
}
exports.GUIDType = GUIDType;
class TupleType extends TypeExpr {
    constructor(is_open, elements) {
        super("bTupleType_" + elements.length + elements.map(x => x.fstar_type_encoding).join("_") + is_open);
        this.is_open = is_open;
        this.elements = elements;
        // --------------------------------------------------------------------------------
        if (!TupleType.declared.has(this.fstar_type_encoding)) {
            TupleType.declared.add(this.fstar_type_encoding);
            TypeExpr.declarator.add(new type_decl_1.TupleTypeDecl(this.fstar_type_encoding, this.is_open, this.elements));
        }
        // --------------------------------------------------------------------------------
    }
    getBosqueType() {
        return "[" + this.elements.map(x => x.getBosqueType()).join(", ") + "]";
    }
}
exports.TupleType = TupleType;
TupleType.declared = new Set();
class RecordType extends TypeExpr {
    constructor(is_open, field_names, elements) {
        super("bRecordType_" + elements.length + elements.map((value, index) => field_names[index].slice(1, -1) + value.fstar_type_encoding).join("_") + is_open);
        this.is_open = is_open;
        this.field_names = field_names.map(x => "\"" + x + "\"");
        this.elements = elements;
        // --------------------------------------------------------------------------------
        if (!RecordType.declared.has(this.fstar_type_encoding)) {
            RecordType.declared.add(this.fstar_type_encoding);
            TypeExpr.declarator.add(new type_decl_1.RecordTypeDecl(this.fstar_type_encoding, this.is_open, this.field_names, this.elements));
        }
        // --------------------------------------------------------------------------------
    }
    getBosqueType() {
        return "{" + this.field_names.map((value, index) => value + ":" + this.elements[index].getBosqueType()).join(", ") + "}";
    }
}
exports.RecordType = RecordType;
RecordType.declared = new Set();
class FuncType extends TypeExpr {
    constructor(domain, image) {
        super("BFunctionType");
        this.domain = domain;
        this.image = image;
    }
    valDeclare() {
        return ((this.domain.length == 0) ? "" : this.domain.map(x => x.getFStarTerm()).join(" -> ") + " -> Tot ")
            + this.image.getFStarTerm();
    }
    getBosqueType() {
        console.log("FuncType doesn't have a proper bosque Type since the compiler defunctionalize func terms");
        return "";
    }
}
exports.FuncType = FuncType;
class ObjectType extends TypeExpr {
    constructor() {
        super("BObjectType");
    }
    getBosqueType() {
        return "NSCore::Object";
    }
}
exports.ObjectType = ObjectType;
class EnumType extends TypeExpr {
    constructor() {
        super("BEnumType");
    }
    getBosqueType() {
        return "NSCore::Enum";
    }
}
exports.EnumType = EnumType;
class CustomKeyType extends TypeExpr {
    constructor() {
        super("BCustomKeyType");
    }
    getBosqueType() {
        return "NSCore::CustomKeyType";
    }
}
exports.CustomKeyType = CustomKeyType;
class KeyedType extends TypeExpr {
    constructor() {
        super("BKeyedType");
    }
    getBosqueType() {
        return "NSCore::KeyedType";
    }
}
exports.KeyedType = KeyedType;
class ConstructorType extends TypeExpr {
    constructor(constructorName, fields) {
        super("B" + util_1.sanitizeName(constructorName) + "Type");
        this.fields = fields;
        this.original_name = constructorName;
    }
    getBosqueType() {
        return this.original_name;
    }
}
exports.ConstructorType = ConstructorType;
class ListType extends TypeExpr {
    constructor(ty) {
        const type_string_encoding = ty.fstar_type_encoding;
        super("bListType_" + type_string_encoding);
        this.ty = ty;
        // --------------------------------------------------------------------------------
        if (!ListType.declared.has(type_string_encoding)) {
            ListType.declared.add(type_string_encoding);
            ListType.declarator.add(new type_decl_1.ListTypeDecl(type_string_encoding));
        }
        // --------------------------------------------------------------------------------
    }
    getBosqueType() {
        return "NSCore::List<T=" + this.ty.getBosqueType() + ">";
    }
}
exports.ListType = ListType;
ListType.declared = new Set();
//# sourceMappingURL=type_expr.js.map