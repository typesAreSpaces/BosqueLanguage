//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
//

import * as FS from "fs";
import { toFStarSequence } from "./util"
import { TypeExpr } from "./type_expr"

export abstract class TypeDecl {
  readonly type_string_encoding: string;
  constructor(type_string_encoding: string) {
    this.type_string_encoding = type_string_encoding;
  }
  abstract emit(fd: number): void;
}

export class TypedStringTypeDecl extends TypeDecl {
  constructor(type_string_encoding: string) {
    super(type_string_encoding);
  }
  emit(fd: number) {
    // Adding bTypedStringType at the beginning here is necessary
    // because TypedStringType.declared only keeps track of the elements
    // of the constructor type
    FS.writeSync(fd, `let bTypedStringType_${this.type_string_encoding} = (BTypedStringType ${this.type_string_encoding})\n`);
  }
}

export class TupleTypeDecl extends TypeDecl {
  readonly is_open_tuple: boolean;
  readonly array_of_types: TypeExpr[];
  constructor(type_string_encoding: string, is_open_tuple: boolean, array_of_types: TypeExpr[]) {
    super(type_string_encoding);
    this.is_open_tuple = is_open_tuple;
    this.array_of_types = array_of_types;
  }

  toFStarTuple(types: TypeExpr[]): string {
    return toFStarSequence(types.map(x => x.fstar_type_encoding));
  }

  emit(fd: number) {
    // Here the index contains the constructor information
    // Hence, the constructor information is not added  
    FS.writeSync(fd, `let ${this.type_string_encoding} = BTupleType ${this.is_open_tuple} ${this.array_of_types.length} ${this.toFStarTuple(this.array_of_types)}\n`);
  }
}

export class RecordTypeDecl extends TypeDecl {
  readonly is_open_record: boolean;
  readonly field_names: string[];
  readonly array_of_types: TypeExpr[];
  constructor(type_string_encoding: string, is_open_record: boolean, field_names: string[], array_of_types: TypeExpr[]) {
    super(type_string_encoding);
    this.is_open_record = is_open_record;
    this.field_names = field_names;
    this.array_of_types = array_of_types;
  }

  toFStarRecord(fields: string[], types: TypeExpr[]): string {
    return toFStarSequence(fields) + " " + toFStarSequence(types.map(x => x.fstar_type_encoding));
  }

  emit(fd: number) {
    FS.writeSync(fd, `let ${this.type_string_encoding} = BRecordType ${this.is_open_record} ${this.array_of_types.length} ${this.toFStarRecord(this.field_names, this.array_of_types)}\n`);
  }
}

export class UnionTypeDecl extends TypeDecl {
  readonly array_of_types: TypeExpr[];
  constructor(type_string_encoding: string, array_of_types: TypeExpr[]) {
    super(type_string_encoding);
    this.array_of_types = array_of_types;
  }

  toFStarUnion(x: TypeExpr[]): string {
    if (x.length == 2) {
      return "(BUnionType "
        + x[0].fstar_type_encoding
        + " " + x[1].fstar_type_encoding + ")"
    }
    else {
      if (x.length < 2) {
        throw new Error("UnionType expected two or more types");
      }
      else {
        const tail = x.slice(1);
        return "(BUnionType " + x[0].fstar_type_encoding + " " + this.toFStarUnion(tail) + ")";
      }
    }
  }

  emit(fd: number) {
    // Here the index contains the constructor information
    // Hence, the constructor information is not added
    FS.writeSync(fd, `let ${this.type_string_encoding} = ${this.toFStarUnion(this.array_of_types)}\n`);
  }
}

export class ListTypeDecl extends TypeDecl {
  constructor(type_string_encoding: string) {
    super(type_string_encoding);
  }
  emit(fd: number) {
    FS.writeSync(fd, `let bListType_${this.type_string_encoding} = (BListType ${this.type_string_encoding})\n`);
  }
}


