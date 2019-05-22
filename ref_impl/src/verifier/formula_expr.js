"use strict";
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
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
var TypeExpr = /** @class */ (function () {
    function TypeExpr() {
    }
    return TypeExpr;
}());
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
    return FuncExpr;
}(TermExpr));
var FormulaExpr = /** @class */ (function () {
    function FormulaExpr(name) {
        this.name = name;
    }
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
    return PredicateExpr;
}(FormulaExpr));
var EqualityExpr = /** @class */ (function (_super) {
    __extends(EqualityExpr, _super);
    function EqualityExpr(name, left, right) {
        var _this = _super.call(this, name) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        return _this;
    }
    return EqualityExpr;
}(FormulaExpr));
var NegExpr = /** @class */ (function (_super) {
    __extends(NegExpr, _super);
    function NegExpr(formula) {
        var _this = _super.call(this, "neg " + formula.name) || this;
        _this.formula = formula;
        return _this;
    }
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
    return ImplExpr;
}(FormulaExpr));
var ForAllExpr = /** @class */ (function (_super) {
    __extends(ForAllExpr, _super);
    function ForAllExpr(nameBinder, formula) {
        var _this = _super.call(this, "forall " + nameBinder.name + "." + formula.name) || this;
        _this.nameBinder = nameBinder;
        _this.formula = formula;
        return _this;
    }
    return ForAllExpr;
}(FormulaExpr));
var ExistsExpr = /** @class */ (function (_super) {
    __extends(ExistsExpr, _super);
    function ExistsExpr(nameBinder, formula) {
        var _this = _super.call(this, "exists " + nameBinder.name + "." + formula.name) || this;
        _this.nameBinder = nameBinder;
        _this.formula = formula;
        return _this;
    }
    return ExistsExpr;
}(FormulaExpr));
// Testing
var x = new VarExpr("x");
var y = new VarExpr("y");
var predicate = new PredicateExpr("p", [x, y]);
var p = new NegExpr(predicate);
var p2 = new NegExpr(new PredicateExpr("p", [x, y]));
var fxy = new FuncExpr("f", [x, y]);
console.log(x);
console.log(predicate);
console.log(p);
console.log(p2);
console.log(fxy);
console.log(new FuncExpr("g", [x, y, x, x, x]));
console.log(new FuncExpr("g", [x]));
console.log(new FuncExpr("g", []));
console.log("Ok");
