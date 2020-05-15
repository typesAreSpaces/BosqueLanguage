//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { sanitizeName } from "./util";
import { TypeDecl, UnionTypeDecl, TypedStringTypeDecl, TupleTypeDecl, RecordTypeDecl, ListTypeDecl } from "./type_decl"

// --------------------------------------------------------

abstract class TypeExpr {
  // fstar_type_encoding is a string denoting the type 
  // used in the FStar encoding 
  readonly fstar_type_encoding: string;
  static declarator = new Set<TypeDecl>();

  constructor(fstar_type_encoding: string) {
    this.fstar_type_encoding = fstar_type_encoding;
  }
  // getFStarTerm emits the refinement type in FStar
  // The latter is used for the FStar typing system
  getFStarTerm() {
    return "(x:bosqueTerm{subtypeOf " + this.fstar_type_encoding + " (getType x)})";
  }
  // getBosqueType emits the (MIR) Bosque type
  abstract getBosqueType(): string;

  static declareTypeNames(fd: number): void {
    TypeExpr.declarator.forEach(x => x.emit(fd));
  }
  equalTo(ty: TypeExpr): boolean {
    return this.fstar_type_encoding == ty.fstar_type_encoding;
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
    super("bUnionType_" + Array.from(elements).sort().map(x => x.fstar_type_encoding).join("_"));
    this.elements = elements;
    // --------------------------------------------------------------------------------
    if (!UnionType.declared.has(this.fstar_type_encoding)) {
      UnionType.declared.add(this.fstar_type_encoding);
      TypeExpr.declarator.add(new UnionTypeDecl(this.fstar_type_encoding, Array.from(elements).sort()));
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
    const type_string_encoding = ty.fstar_type_encoding;
    super("bTypedStringType_" + type_string_encoding);
    this.ty = ty;
    // --------------------------------------------------------------------------------
    if (!TypedStringType.declared.has(type_string_encoding)) {
      TypedStringType.declared.add(type_string_encoding);
      TypeExpr.declarator.add(new TypedStringTypeDecl(type_string_encoding));
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
    super("bTupleType_" + elements.length + elements.map(x => x.fstar_type_encoding).join("_") + is_open);
    this.is_open = is_open;
    this.elements = elements;
    // --------------------------------------------------------------------------------
    if (!TupleType.declared.has(this.fstar_type_encoding)) {
      TupleType.declared.add(this.fstar_type_encoding);
      TypeExpr.declarator.add(new TupleTypeDecl(this.fstar_type_encoding, this.is_open, this.elements));
    }
    // --------------------------------------------------------------------------------
  }
  getBosqueType() {
    return "[" + this.elements.map(x => x.getBosqueType()).join(", ") + "]";
  }
}

class RecordType extends TypeExpr {
  static declared: Set<string> = new Set<string>();
  readonly is_open: boolean;
  readonly field_names: string[];
  readonly elements: TypeExpr[];

  constructor(is_open: boolean, field_names: string[], elements: TypeExpr[]) {
    super("bRecordType_" + elements.length + elements.map((value, index) => field_names[index].slice(1, -1) + value.fstar_type_encoding).join("_") + is_open);
    this.is_open = is_open
    this.field_names = field_names.map(x => "\"" + x + "\"");
    this.elements = elements;
    // --------------------------------------------------------------------------------
    if (!RecordType.declared.has(this.fstar_type_encoding)) {
      RecordType.declared.add(this.fstar_type_encoding);
      TypeExpr.declarator.add(new RecordTypeDecl(this.fstar_type_encoding, this.is_open, this.field_names, this.elements));
    }
    // --------------------------------------------------------------------------------
  }
  getBosqueType() {
    return "{" + this.field_names.map((value, index) => value + ":" + this.elements[index].getBosqueType()).join(", ") + "}";
  }
}

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
    console.log("FuncType doesn't have a proper bosque Type since the compiler defunctionalize func terms");
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

class EnumType extends TypeExpr {
  constructor() {
    super("BEnumType");
  }
  getBosqueType() {
    return "NSCore::Enum";
  }
}

class CustomKeyType extends TypeExpr {
  constructor() {
    super("BCustomKeyType");
  }
  getBosqueType() {
    return "NSCore::CustomKeyType";
  }
}

class KeyedType extends TypeExpr {
  constructor() {
    super("BKeyedType");
  }
  getBosqueType() {
    return "NSCore::KeyedType";
  }
}

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
    const type_string_encoding = ty.fstar_type_encoding;
    super("bListType_" + type_string_encoding);
    this.ty = ty;
    // --------------------------------------------------------------------------------
    if (!ListType.declared.has(type_string_encoding)) {
      ListType.declared.add(type_string_encoding);
      ListType.declarator.add(new ListTypeDecl(type_string_encoding));
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
