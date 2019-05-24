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
// import * as deepEqual from "deep-equal"
var fs = require("fs");
var TypeExpr = /** @class */ (function () {
    function TypeExpr() {
    }
    return TypeExpr;
}());
var IntType = /** @class */ (function (_super) {
    __extends(IntType, _super);
    function IntType() {
        var _this = _super !== null && _super.apply(this, arguments) || this;
        _this.isPrimitiveType = true;
        return _this;
    }
    IntType.prototype.getType = function () {
        return "Int";
    };
    return IntType;
}(TypeExpr));
var BoolType = /** @class */ (function (_super) {
    __extends(BoolType, _super);
    function BoolType() {
        var _this = _super !== null && _super.apply(this, arguments) || this;
        _this.isPrimitiveType = true;
        return _this;
    }
    BoolType.prototype.getType = function () {
        return "Bool";
    };
    return BoolType;
}(TypeExpr));
var StringType = /** @class */ (function (_super) {
    __extends(StringType, _super);
    function StringType() {
        var _this = _super !== null && _super.apply(this, arguments) || this;
        _this.isPrimitiveType = true;
        return _this;
    }
    StringType.prototype.getType = function () {
        return "String";
    };
    return StringType;
}(TypeExpr));
var FuncType = /** @class */ (function (_super) {
    __extends(FuncType, _super);
    function FuncType(domain, image) {
        var _this = _super.call(this) || this;
        _this.isPrimitiveType = false;
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
// TODO: Add more elements to the 
// abstract class TypeExpr once we 
// have formalized the type system
// for Bosque. Actually, it is already
// established on the documentation,
// however, it needs additional formalization
// to deal with some rules and inference
// (Current approach to accomplish the latter: take 
// the grouded ast and build a `table' using
var TermExpr = /** @class */ (function () {
    function TermExpr(name, symbolName, ty) {
        this.name = name;
        this.symbolName = symbolName;
        this.ty = ty;
    }
    TermExpr.symbolTable = new Map();
    return TermExpr;
}());
var VarExpr = /** @class */ (function (_super) {
    __extends(VarExpr, _super);
    function VarExpr(name, ty) {
        var _this = _super.call(this, name, name, ty) || this;
        VarExpr.symbolTable.set(_this.name, false);
        return _this;
    }
    VarExpr.prototype.toZ3Declaration = function (fd) {
        if (!VarExpr.symbolTable.get(this.name)) {
            fs.writeSync(fd, "(declare-fun " + this.symbolName + " () " + this.ty.getType() + ")\n");
            VarExpr.symbolTable.set(this.name, true);
        }
    };
    VarExpr.prototype.sexpr = function () {
        return this.symbolName;
    };
    return VarExpr;
}(TermExpr));
var FuncExpr = /** @class */ (function (_super) {
    __extends(FuncExpr, _super);
    function FuncExpr(name, ty, terms) {
        var _this = this;
        var collectType = new FuncType(terms.map(function (x) { return x.ty; }), ty);
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
        FuncExpr.symbolTable.set(_this.name, false);
        return _this;
    }
    FuncExpr.prototype.toZ3Declaration = function (fd) {
        for (var _i = 0, _a = this.terms; _i < _a.length; _i++) {
            var item = _a[_i];
            item.toZ3Declaration(fd);
        }
        if (!FuncExpr.symbolTable.get(this.name)) {
            fs.writeSync(fd, "(declare-fun " + this.symbolName + " " + this.ty.getType() + ")\n");
            FuncExpr.symbolTable.set(this.name, true);
        }
    };
    FuncExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + this.terms.reduce(function (a, b) { return a + " " + b.sexpr(); }, "") + ")";
    };
    return FuncExpr;
}(TermExpr));
var FormulaExpr = /** @class */ (function () {
    function FormulaExpr(name, symbolName, ty) {
        this.name = name;
        this.symbolName = symbolName;
        this.ty = ty;
    }
    FormulaExpr.prototype.toZ3 = function (fd) {
        this.toZ3Declaration(fd);
        fs.writeSync(fd, "(assert " + this.sexpr() + ")\n");
    };
    FormulaExpr.symbolTable = new Map();
    return FormulaExpr;
}());
// PredicateExpr always takes a BoolType
// since we won't encode PARAMETRIZED 
// logical formulas
var PredicateExpr = /** @class */ (function (_super) {
    __extends(PredicateExpr, _super);
    function PredicateExpr(name, terms) {
        var _this = this;
        switch (terms.length) {
            case 0: {
                _this = _super.call(this, name + "l__r", name, new BoolType()) || this;
                break;
            }
            case 1: {
                _this = _super.call(this, name + "l_" + terms[0].name + "_r", name, new BoolType()) || this;
                break;
            }
            default: {
                _this = _super.call(this, name + "l_" + terms.slice(1).reduce(function (a, b) { return a + "_" + b.name; }, terms[0].name) + "_r", name, new BoolType()) || this;
                break;
            }
        }
        _this.terms = terms;
        PredicateExpr.symbolTable.set(_this.name, false);
        return _this;
    }
    PredicateExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + this.terms.reduce(function (a, b) { return a + " " + b.sexpr(); }, "") + ")";
    };
    PredicateExpr.prototype.toZ3Declaration = function (fd) {
        for (var _i = 0, _a = this.terms; _i < _a.length; _i++) {
            var item = _a[_i];
            item.toZ3Declaration(fd);
        }
        if (!PredicateExpr.symbolTable.get(this.name)) {
            fs.writeSync(fd, "(declare-fun " + this.symbolName + " () " + this.ty.getType() + ")\n");
            PredicateExpr.symbolTable.set(this.name, true);
        }
    };
    return PredicateExpr;
}(FormulaExpr));
var EqualityExpr = /** @class */ (function (_super) {
    __extends(EqualityExpr, _super);
    function EqualityExpr(left, right) {
        var _this = _super.call(this, left.name + "=" + right.name, "=", new BoolType()) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        return _this;
    }
    EqualityExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    };
    EqualityExpr.prototype.toZ3Declaration = function (fd) {
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    };
    return EqualityExpr;
}(FormulaExpr));
var NegExpr = /** @class */ (function (_super) {
    __extends(NegExpr, _super);
    function NegExpr(formula) {
        var _this = _super.call(this, "neg " + formula.name, "not", new BoolType()) || this;
        _this.formula = formula;
        return _this;
    }
    NegExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + this.formula.sexpr() + ")";
    };
    NegExpr.prototype.toZ3Declaration = function (fd) {
        this.formula.toZ3Declaration(fd);
    };
    return NegExpr;
}(FormulaExpr));
var AndExpr = /** @class */ (function (_super) {
    __extends(AndExpr, _super);
    function AndExpr(left, right) {
        var _this = _super.call(this, left.name + " and " + right.name, "and", new BoolType()) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        return _this;
    }
    AndExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    };
    AndExpr.prototype.toZ3Declaration = function (fd) {
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    };
    return AndExpr;
}(FormulaExpr));
var OrExpr = /** @class */ (function (_super) {
    __extends(OrExpr, _super);
    function OrExpr(left, right) {
        var _this = _super.call(this, left.name + " or " + right.name, "or", new BoolType()) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        return _this;
    }
    OrExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    };
    OrExpr.prototype.toZ3Declaration = function (fd) {
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    };
    return OrExpr;
}(FormulaExpr));
var ImplExpr = /** @class */ (function (_super) {
    __extends(ImplExpr, _super);
    function ImplExpr(left, right) {
        var _this = _super.call(this, left.name + " implies " + right.name, "=>", new BoolType()) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        return _this;
    }
    ImplExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    };
    ImplExpr.prototype.toZ3Declaration = function (fd) {
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    };
    return ImplExpr;
}(FormulaExpr));
var ForAllExpr = /** @class */ (function (_super) {
    __extends(ForAllExpr, _super);
    function ForAllExpr(nameBinder, formula) {
        var _this = _super.call(this, "forall " + nameBinder.name + ".l_" + formula.name + "_r", "forall", new BoolType()) || this;
        _this.nameBinder = nameBinder;
        _this.formula = formula;
        return _this;
    }
    ForAllExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " " + this.formula.sexpr() + ")";
    };
    ForAllExpr.prototype.toZ3Declaration = function (fd) {
        this.formula.toZ3Declaration(fd);
    };
    return ForAllExpr;
}(FormulaExpr));
var ExistsExpr = /** @class */ (function (_super) {
    __extends(ExistsExpr, _super);
    function ExistsExpr(nameBinder, formula) {
        var _this = _super.call(this, "exists " + nameBinder.name + ".l_" + formula.name + "_r", "exists", new BoolType()) || this;
        _this.nameBinder = nameBinder;
        _this.formula = formula;
        return _this;
    }
    ExistsExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " " + this.formula.sexpr() + ")";
    };
    ExistsExpr.prototype.toZ3Declaration = function (fd) {
        this.formula.toZ3Declaration(fd);
    };
    return ExistsExpr;
}(FormulaExpr));
// IMPORTANT: Names cannot include `,'
// or any other symbol that Z3 cannot
// parse as a valid char for a name expression
// Testing
var x = new VarExpr("x", new IntType());
var y = new VarExpr("y", new IntType());
var pxy = new PredicateExpr("p", [x, y]);
var fxy = new FuncExpr("f", new StringType(), [x, y]);
var extraLong = new ForAllExpr(x, new AndExpr(pxy, new ForAllExpr(y, new PredicateExpr("p", [fxy, x, x, y, fxy, x]))));
var fd = fs.openSync('file.z3', 'w');
// (new FuncExpr("g", new IntType(), [fxy, fxy])).toZ3Declaration(fd);
// (new FuncExpr("h", new IntType(), [])).toZ3Declaration(fd);
// (new FuncExpr("k", new IntType(), [fxy])).toZ3Declaration(fd);
extraLong.toZ3(fd);
pxy.toZ3(fd);
fs.closeSync(fd);
