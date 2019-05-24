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
        return _super !== null && _super.apply(this, arguments) || this;
    }
    return IntType;
}(TypeExpr));
var BoolType = /** @class */ (function (_super) {
    __extends(BoolType, _super);
    function BoolType() {
        return _super !== null && _super.apply(this, arguments) || this;
    }
    return BoolType;
}(TypeExpr));
var StringType = /** @class */ (function (_super) {
    __extends(StringType, _super);
    function StringType() {
        return _super !== null && _super.apply(this, arguments) || this;
    }
    return StringType;
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
    function TermExpr(name) {
        this.name = name;
    }
    return TermExpr;
}());
var VarExpr = /** @class */ (function (_super) {
    __extends(VarExpr, _super);
    function VarExpr(name) {
        return _super.call(this, name) || this;
    }
    VarExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    return VarExpr;
}(TermExpr));
var FuncExpr = /** @class */ (function (_super) {
    __extends(FuncExpr, _super);
    function FuncExpr(name, terms) {
        var _this = this;
        switch (terms.length) {
            case 0: {
                _this = _super.call(this, name + "()") || this;
                break;
            }
            case 1: {
                _this = _super.call(this, name + "(" + terms[0].name + ")") || this;
                break;
            }
            default: {
                _this = _super.call(this, name + "(" + terms.slice(1).reduce(function (a, b) { return a + "," + b.name; }, terms[0].name) + ")") || this;
                break;
            }
        }
        _this.terms = terms;
        return _this;
    }
    FuncExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    return FuncExpr;
}(TermExpr));
var FormulaExpr = /** @class */ (function () {
    function FormulaExpr(name) {
        this.name = name;
    }
    FormulaExpr.fsFormula = require('fs');
    return FormulaExpr;
}());
var PredicateExpr = /** @class */ (function (_super) {
    __extends(PredicateExpr, _super);
    function PredicateExpr(name, terms) {
        var _this = this;
        switch (terms.length) {
            case 0: {
                _this = _super.call(this, name + "()") || this;
                break;
            }
            case 1: {
                _this = _super.call(this, name + "(" + terms[0].name + ")") || this;
                break;
            }
            default: {
                _this = _super.call(this, name + "(" + terms.slice(1).reduce(function (a, b) { return a + "," + b.name; }, terms[0].name) + ")") || this;
                break;
            }
        }
        _this.terms = terms;
        _this.terms = terms;
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
        var _this = _super.call(this, left.name + "=" + right.name) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
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
        var _this = _super.call(this, "neg " + formula.name) || this;
        _this.formula = formula;
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
        var _this = _super.call(this, left.name + " and " + right.name) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
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
        var _this = _super.call(this, left.name + " or " + right.name) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
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
        var _this = _super.call(this, left.name + " implies " + right.name) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
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
        var _this = _super.call(this, "forall " + nameBinder.name + ".(" + formula.name + ")") || this;
        _this.nameBinder = nameBinder;
        _this.formula = formula;
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
        var _this = _super.call(this, "exists " + nameBinder.name + ".(" + formula.name + ")") || this;
        _this.nameBinder = nameBinder;
        _this.formula = formula;
        return _this;
    }
    ExistsExpr.prototype.toZ3 = function (fd) {
        fs.writeSync(fd, this.name + '\n');
    };
    return ExistsExpr;
}(FormulaExpr));
// Testing
var x = new VarExpr("x");
var x2 = new VarExpr("x");
var y = new VarExpr("y");
var p = new PredicateExpr("p", [x, y]);
var not_p = new NegExpr(p);
var fxy = new FuncExpr("f", [x, y]);
var extraLong = new ForAllExpr(x, new ForAllExpr(y, new PredicateExpr("p", [fxy, x, x, y, fxy, x])));
// console.log("Examples---");
// console.log(x);
// console.log(p);
// console.log(not_p);
// console.log(fxy);
// console.log(new FuncExpr("g", [x, y, x, x, x]));
// console.log(new FuncExpr("g", [x]));
// console.log(new FuncExpr("g", []));
// console.log(new ForAllExpr(x, p));
// console.log("Ok---");
// // Testing equality
// console.log("is x equal to x2?");
// console.log(deepEqual(x, x2));
// console.log("is forall x . p equal to forall x2 . p");
// console.log(deepEqual(new ForAllExpr(x, p), new ForAllExpr(x2, p)));
// // Writing on a file
// // So we can use Z3 
// console.log('Testing writing on file');
// let fd = fs.openSync('file.z3', 'w');
// extraLong.toZ3(fd);
// fs.closeSync(fd);
// // Passed tests!
