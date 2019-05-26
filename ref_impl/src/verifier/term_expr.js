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
var fs = require("fs");
var type_expr_1 = require("./type_expr");
var TermExpr = /** @class */ (function () {
    function TermExpr(name, symbolName, ty) {
        this.name = name;
        this.symbolName = symbolName;
        this.ty = ty;
        if (!TermExpr.symbolTable.has(this.name)) {
            TermExpr.symbolTable.set(this.name, false);
        }
    }
    TermExpr.prototype.toZ3DeclarationSort = function (fd) {
        var thisTypeTemp = this.ty.getType();
        if (this.ty.isUninterpreted && !type_expr_1.UninterpretedType.symbolTable.get(thisTypeTemp)) {
            fs.writeSync(fd, "(declare-sort " + this.ty.name + ")\n");
            type_expr_1.UninterpretedType.symbolTable.set(thisTypeTemp, true);
        }
    };
    TermExpr.symbolTable = new Map();
    return TermExpr;
}());
exports.TermExpr = TermExpr;
var VarExpr = /** @class */ (function (_super) {
    __extends(VarExpr, _super);
    function VarExpr(name, ty) {
        return _super.call(this, name, name, ty) || this;
    }
    VarExpr.prototype.toZ3Declaration = function (fd) {
        this.toZ3DeclarationSort(fd);
        if (!VarExpr.symbolTable.get(this.symbolName)) {
            fs.writeSync(fd, "(declare-fun " + this.symbolName + " () " + this.ty.getType() + ")\n");
            VarExpr.symbolTable.set(this.symbolName, true);
        }
    };
    VarExpr.prototype.sexpr = function () {
        return this.symbolName;
    };
    return VarExpr;
}(TermExpr));
exports.VarExpr = VarExpr;
var FuncExpr = /** @class */ (function (_super) {
    __extends(FuncExpr, _super);
    function FuncExpr(name, ty, terms) {
        var _this = this;
        var collectType = new type_expr_1.FuncType(terms.map(function (x) { return x.ty; }), ty);
        switch (terms.length) {
            case 0: {
                _this = _super.call(this, name + "l__r", name, collectType) || this;
                break;
            }
            case 1: {
                _this = _super.call(this, name + "l_" + terms[0].name + "_r", name, collectType) || this;
                break;
            }
            default: {
                _this = _super.call(this, name + "l_" + terms.slice(1).reduce(function (a, b) { return a + "_" + b.name; }, terms[0].name) + "_r", name, collectType) || this;
                break;
            }
        }
        _this.terms = terms;
        return _this;
    }
    FuncExpr.prototype.toZ3Declaration = function (fd) {
        this.toZ3DeclarationSort(fd);
        for (var _i = 0, _a = this.terms; _i < _a.length; _i++) {
            var item = _a[_i];
            item.toZ3Declaration(fd);
        }
        if (!FuncExpr.symbolTable.get(this.symbolName)) {
            fs.writeSync(fd, "(declare-fun " + this.symbolName + " " + this.ty.getType() + ")\n");
            FuncExpr.symbolTable.set(this.symbolName, true);
        }
    };
    FuncExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + this.terms.reduce(function (a, b) { return a + " " + b.sexpr(); }, "") + ")";
    };
    return FuncExpr;
}(TermExpr));
exports.FuncExpr = FuncExpr;
