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
            return "(" + this.domain.slice(1).reduce(function (a, b) {
                return a + " " + (b.isPrimitiveType ? b.getType() : b.image.getType());
            }, this.domain[0].isPrimitiveType ? this.domain[0].getType() : this.domain[0].image.getType())
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
    function TermExpr(name, ty) {
        this.name = name;
        this.ty = ty;
    }
    TermExpr.symbolTable = new Map();
    return TermExpr;
}());
var VarExpr = /** @class */ (function (_super) {
    __extends(VarExpr, _super);
    function VarExpr(name, ty) {
        var _this = _super.call(this, name, ty) || this;
        VarExpr.symbolTable.set(_this.name, false);
        return _this;
    }
    VarExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    VarExpr.prototype.toZ3Declarations = function (fd) {
        if (!VarExpr.symbolTable.get(this.name)) {
            fs.writeSync(fd, "(declare-fun " + this.name + " () " + this.ty.getType() + ")\n");
            VarExpr.symbolTable.set(this.name, true);
        }
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
                _this = _super.call(this, name + "l__r", collectType) || this;
                break;
            }
            case 1: {
                _this = _super.call(this, name + "l_" + terms[0].name + "_r", collectType) || this;
                break;
            }
            default: {
                _this = _super.call(this, name + "l_" + terms.slice(1).reduce(function (a, b) { return a + "," + b.name; }, terms[0].name) + "_r", collectType) || this;
                break;
            }
        }
        _this.terms = terms;
        FuncExpr.symbolTable.set(_this.name, false);
        return _this;
    }
    FuncExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    FuncExpr.prototype.toZ3Declarations = function (fd) {
        for (var _i = 0, _a = this.terms; _i < _a.length; _i++) {
            var item = _a[_i];
            item.toZ3Declarations(fd);
        }
        if (!FuncExpr.symbolTable.get(this.name)) {
            fs.writeSync(fd, "(declare-fun " + this.name + " " + this.ty.getType() + ")\n");
            FuncExpr.symbolTable.set(this.name, true);
        }
    };
    return FuncExpr;
}(TermExpr));
var FormulaExpr = /** @class */ (function () {
    function FormulaExpr(name, ty) {
        this.name = name;
        this.ty = ty;
    }
    FormulaExpr.symbolTable = new Map();
    return FormulaExpr;
}());
var PredicateExpr = /** @class */ (function (_super) {
    __extends(PredicateExpr, _super);
    function PredicateExpr(name, terms) {
        var _this = this;
        switch (terms.length) {
            case 0: {
                _this = _super.call(this, name + "l__r", new BoolType()) || this;
                break;
            }
            case 1: {
                _this = _super.call(this, name + "l_" + terms[0].name + "_r", new BoolType()) || this;
                break;
            }
            default: {
                _this = _super.call(this, name + "l_" + terms.slice(1).reduce(function (a, b) { return a + "," + b.name; }, terms[0].name) + "_r", new BoolType()) || this;
                break;
            }
        }
        _this.terms = terms;
        FormulaExpr.symbolTable.set(_this.name, new BoolType());
        return _this;
    }
    PredicateExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    return PredicateExpr;
}(FormulaExpr));
var EqualityExpr = /** @class */ (function (_super) {
    __extends(EqualityExpr, _super);
    function EqualityExpr(left, right) {
        var _this = _super.call(this, left.name + "=" + right.name, new BoolType()) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        EqualityExpr.symbolTable.set(_this.name, new BoolType());
        return _this;
    }
    EqualityExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    return EqualityExpr;
}(FormulaExpr));
var NegExpr = /** @class */ (function (_super) {
    __extends(NegExpr, _super);
    function NegExpr(formula) {
        var _this = _super.call(this, "neg " + formula.name, new BoolType()) || this;
        _this.formula = formula;
        NegExpr.symbolTable.set(_this.name, new BoolType());
        return _this;
    }
    NegExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    return NegExpr;
}(FormulaExpr));
var AndExpr = /** @class */ (function (_super) {
    __extends(AndExpr, _super);
    function AndExpr(left, right) {
        var _this = _super.call(this, left.name + " and " + right.name, new BoolType()) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        AndExpr.symbolTable.set(_this.name, new BoolType());
        return _this;
    }
    AndExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    return AndExpr;
}(FormulaExpr));
var OrExpr = /** @class */ (function (_super) {
    __extends(OrExpr, _super);
    function OrExpr(left, right) {
        var _this = _super.call(this, left.name + " or " + right.name, new BoolType()) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        OrExpr.symbolTable.set(_this.name, new BoolType());
        return _this;
    }
    OrExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    return OrExpr;
}(FormulaExpr));
var ImplExpr = /** @class */ (function (_super) {
    __extends(ImplExpr, _super);
    function ImplExpr(left, right) {
        var _this = _super.call(this, left.name + " implies " + right.name, new BoolType()) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        ImplExpr.symbolTable.set(_this.name, new BoolType());
        return _this;
    }
    ImplExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    return ImplExpr;
}(FormulaExpr));
var ForAllExpr = /** @class */ (function (_super) {
    __extends(ForAllExpr, _super);
    function ForAllExpr(nameBinder, formula) {
        var _this = _super.call(this, "forall " + nameBinder.name + ".l_" + formula.name + "_r", new BoolType()) || this;
        _this.nameBinder = nameBinder;
        _this.formula = formula;
        ForAllExpr.symbolTable.set(_this.name, new BoolType());
        return _this;
    }
    ForAllExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    return ForAllExpr;
}(FormulaExpr));
var ExistsExpr = /** @class */ (function (_super) {
    __extends(ExistsExpr, _super);
    function ExistsExpr(nameBinder, formula) {
        var _this = _super.call(this, "exists " + nameBinder.name + ".l_" + formula.name + "_r", new BoolType()) || this;
        _this.nameBinder = nameBinder;
        _this.formula = formula;
        ExistsExpr.symbolTable.set(_this.name, new BoolType());
        return _this;
    }
    ExistsExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    return ExistsExpr;
}(FormulaExpr));
// Testing
var x = new VarExpr("x", new IntType());
var y = new VarExpr("y", new IntType());
var pxy = new PredicateExpr("p", [x, y]);
var fxy = new FuncExpr("f", new StringType(), [x, y]);
var extraLong = new ForAllExpr(x, new AndExpr(pxy, new ForAllExpr(y, new PredicateExpr("p", [fxy, x, x, y, fxy, x]))));
//console.log(extraLong);
// // Writing on a file
// // So we can use Z3 
// console.log('Testing writing on file');
// let fd = fs.openSync('file.z3', 'w');
// extraLong.toZ3(fd);
// fs.closeSync(fd);
// // Passed!
// console.log(FormulaExpr.symbolTable)
// console.log(TermExpr.symbolTable)
var fd = fs.openSync('file.z3', 'w');
(new FuncExpr("g", new IntType(), [fxy, fxy])).toZ3Declarations(fd);
(new FuncExpr("h", new IntType(), [])).toZ3Declarations(fd);
(new FuncExpr("k", new IntType(), [fxy])).toZ3Declarations(fd);
fs.closeSync(fd);
