"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
//
Object.defineProperty(exports, "__esModule", { value: true });
const FS = require("fs");
const util_1 = require("./util");
class TypeDecl {
    constructor(type_string_encoding) {
        this.type_string_encoding = type_string_encoding;
    }
}
exports.TypeDecl = TypeDecl;
class TypedStringTypeDecl extends TypeDecl {
    constructor(type_string_encoding) {
        super(type_string_encoding);
    }
    emit(fd) {
        // Adding bTypedStringType at the beginning here is necessary
        // because TypedStringType.declared only keeps track of the elements
        // of the constructor type
        FS.writeSync(fd, `let bTypedStringType_${this.type_string_encoding} = (BTypedStringType ${this.type_string_encoding})\n`);
    }
}
exports.TypedStringTypeDecl = TypedStringTypeDecl;
class TupleTypeDecl extends TypeDecl {
    constructor(type_string_encoding, is_open_tuple, array_of_types) {
        super(type_string_encoding);
        this.is_open_tuple = is_open_tuple;
        this.array_of_types = array_of_types;
    }
    toFStarTuple(types) {
        return util_1.toFStarSequence(types.map(x => x.fstar_type_encoding));
    }
    emit(fd) {
        // Here the index contains the constructor information
        // Hence, the constructor information is not added  
        FS.writeSync(fd, `let ${this.type_string_encoding} = BTupleType ${this.is_open_tuple} ${this.array_of_types.length} ${this.toFStarTuple(this.array_of_types)}\n`);
    }
}
exports.TupleTypeDecl = TupleTypeDecl;
class RecordTypeDecl extends TypeDecl {
    constructor(type_string_encoding, is_open_record, field_names, array_of_types) {
        super(type_string_encoding);
        this.is_open_record = is_open_record;
        this.field_names = field_names;
        this.array_of_types = array_of_types;
    }
    toFStarRecord(fields, types) {
        return util_1.toFStarSequence(fields) + " " + util_1.toFStarSequence(types.map(x => x.fstar_type_encoding));
    }
    emit(fd) {
        FS.writeSync(fd, `let ${this.type_string_encoding} = BRecordType ${this.is_open_record} ${this.array_of_types.length} ${this.toFStarRecord(this.field_names, this.array_of_types)}\n`);
    }
}
exports.RecordTypeDecl = RecordTypeDecl;
class UnionTypeDecl extends TypeDecl {
    constructor(type_string_encoding, array_of_types) {
        super(type_string_encoding);
        this.array_of_types = array_of_types;
    }
    toFStarUnion(x) {
        if (x.length == 2) {
            return "(BUnionType "
                + x[0].fstar_type_encoding
                + " " + x[1].fstar_type_encoding + ")";
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
    emit(fd) {
        // Here the index contains the constructor information
        // Hence, the constructor information is not added
        FS.writeSync(fd, `let ${this.type_string_encoding} = ${this.toFStarUnion(this.array_of_types)}\n`);
    }
}
exports.UnionTypeDecl = UnionTypeDecl;
class ListTypeDecl extends TypeDecl {
    constructor(type_string_encoding) {
        super(type_string_encoding);
    }
    emit(fd) {
        FS.writeSync(fd, `let bListType_${this.type_string_encoding} = (BListType ${this.type_string_encoding})\n`);
    }
}
exports.ListTypeDecl = ListTypeDecl;
//# sourceMappingURL=type_decl.js.map