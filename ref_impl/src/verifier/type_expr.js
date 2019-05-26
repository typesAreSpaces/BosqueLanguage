"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
var __extends = (this && this.__extends) || (function () {
    var extendStatics = function (d, b) {
        extendStatics = Object.setPrototypeOf ||
            ({ __proto__: [] } instanceof Array && function (d, b) { d.__proto__ = b; }) ||
            function (d, b) { for (var p in b) if (b.hasOwnProperty(p)) d[p] = b[p]; };
        return extendStatics(d, b);
    };
    return function (d, b) {
        extendStatics(d, b);
        function __() { this.constructor = d; }
        d.prototype = b === null ? Object.create(b) : (__.prototype = b.prototype, new __());
    };
})();
exports.__esModule = true;
// TODO: Add more elements to the 
// abstract class TypeExpr once we 
// have formalized the type system
// for Bosque. Actually, it is already
// established on the documentation,
// however, it needs additional formalization
// to deal with some rules and inference
// (Current approach to accomplish the latter: take 
// the grouded ast and build a `table' using
var TypeExpr = /** @class */ (function () {
    function TypeExpr() {
    }
    return TypeExpr;
}());
exports.TypeExpr = TypeExpr;
var IntType = /** @class */ (function (_super) {
    __extends(IntType, _super);
    function IntType() {
        var _this = _super !== null && _super.apply(this, arguments) || this;
        _this.isPrimitiveType = true;
        _this.isUninterpreted = false;
        return _this;
    }
    IntType.prototype.getType = function () {
        return "Int";
    };
    return IntType;
}(TypeExpr));
exports.IntType = IntType;
var BoolType = /** @class */ (function (_super) {
    __extends(BoolType, _super);
    function BoolType() {
        var _this = _super !== null && _super.apply(this, arguments) || this;
        _this.isPrimitiveType = true;
        _this.isUninterpreted = false;
        return _this;
    }
    BoolType.prototype.getType = function () {
        return "Bool";
    };
    return BoolType;
}(TypeExpr));
exports.BoolType = BoolType;
var StringType = /** @class */ (function (_super) {
    __extends(StringType, _super);
    function StringType() {
        var _this = _super !== null && _super.apply(this, arguments) || this;
        _this.isPrimitiveType = true;
        _this.isUninterpreted = false;
        return _this;
    }
    StringType.prototype.getType = function () {
        return "String";
    };
    return StringType;
}(TypeExpr));
exports.StringType = StringType;
var FuncType = /** @class */ (function (_super) {
    __extends(FuncType, _super);
    function FuncType(domain, image) {
        var _this = _super.call(this) || this;
        _this.isPrimitiveType = false;
        _this.isUninterpreted = false;
        _this.domain = domain;
        _this.image = image;
        return _this;
    }
    FuncType.prototype.getType = function () {
        if (this.domain.length == 0) {
            return "() " + this.image.getType();
        }
        else {
            return "(" + this.domain.slice(1).reduce(function (a, b) { return a + " " +
                (b.isPrimitiveType ? b.getType() : b.image.getType()); }, this.domain[0].isPrimitiveType ? this.domain[0].getType() : this.domain[0].image.getType())
                + ") " + this.image.getType();
        }
    };
    return FuncType;
}(TypeExpr));
exports.FuncType = FuncType;
// REMARK: Names cannot include `,'
// or any other symbol that Z3 cannot
// parse as a valid char for a named expression
var UninterpretedType = /** @class */ (function (_super) {
    __extends(UninterpretedType, _super);
    function UninterpretedType(name) {
        var _this = _super.call(this) || this;
        _this.isPrimitiveType = true; // ? Yes, for the moment..
        _this.isUninterpreted = true;
        _this.name = name;
        if (!UninterpretedType.symbolTable.has(_this.name)) {
            UninterpretedType.symbolTable.set(_this.name, false);
        }
        return _this;
    }
    UninterpretedType.prototype.getType = function () {
        return this.name;
    };
    UninterpretedType.symbolTable = new Map();
    return UninterpretedType;
}(TypeExpr));
exports.UninterpretedType = UninterpretedType;
