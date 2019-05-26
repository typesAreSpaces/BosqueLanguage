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
var type_expr_1 = require("./type_expr");
var fs = require("fs");
// REMARK: Names cannot include `,'
// or any other symbol that Z3 cannot
// parse as a valid char for a named expression
var FormulaExpr = /** @class */ (function () {
    function FormulaExpr(name, symbolName, ty) {
        this.name = name;
        this.symbolName = symbolName;
        this.ty = ty;
    }
    // Setting optionalGetModel to true
    // will include a (get-model) command
    // to the Z3 file; otherwise it wont    
    FormulaExpr.prototype.toZ3 = function (fd, optionalGetModel) {
        this.toZ3Declaration(fd);
        fs.writeSync(fd, "(push)\n");
        fs.writeSync(fd, "(assert " + this.sexpr() + ")\n(check-sat)\n");
        if (optionalGetModel) {
            fs.writeSync(fd, "(get-model)\n");
        }
        fs.writeSync(fd, "(pop)\n");
    };
    FormulaExpr.prototype.toZ3DeclarationSort = function (fd) {
        var thisTypeTemp = this.ty.getType();
        if (this.ty.isUninterpreted && !type_expr_1.UninterpretedType.symbolTable.get(thisTypeTemp)) {
            fs.writeSync(fd, "(declare-sort " + this.ty.name + ")\n");
            type_expr_1.UninterpretedType.symbolTable.set(thisTypeTemp, true);
        }
    };
    FormulaExpr.fd = fs.openSync('file.z3', 'w');
    FormulaExpr.symbolTable = new Map();
    return FormulaExpr;
}());
exports.FormulaExpr = FormulaExpr;
var PredicateExpr = /** @class */ (function (_super) {
    __extends(PredicateExpr, _super);
    function PredicateExpr(name, terms) {
        var _this = this;
        var collectType = new type_expr_1.FuncType(terms.map(function (x) { return x.ty; }), new type_expr_1.BoolType());
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
        if (!PredicateExpr.symbolTable.has(_this.symbolName)) {
            PredicateExpr.symbolTable.set(_this.symbolName, false);
        }
        return _this;
    }
    PredicateExpr.prototype.sexpr = function () {
        switch (this.terms.length) {
            case 0: {
                return this.symbolName;
            }
            default: {
                return "(" + this.symbolName + this.terms.reduce(function (a, b) { return a + " " + b.sexpr(); }, "") + ")";
            }
        }
    };
    PredicateExpr.prototype.toZ3Declaration = function (fd) {
        this.toZ3DeclarationSort(fd);
        for (var _i = 0, _a = this.terms; _i < _a.length; _i++) {
            var item = _a[_i];
            item.toZ3Declaration(fd);
        }
        if (!PredicateExpr.symbolTable.get(this.symbolName)) {
            fs.writeSync(fd, "(declare-fun " + this.symbolName + " " + this.ty.getType() + ")\n");
            PredicateExpr.symbolTable.set(this.symbolName, true);
        }
    };
    return PredicateExpr;
}(FormulaExpr));
exports.PredicateExpr = PredicateExpr;
var EqualityExpr = /** @class */ (function (_super) {
    __extends(EqualityExpr, _super);
    function EqualityExpr(left, right) {
        var _this = _super.call(this, left.name + "=" + right.name, "=", new type_expr_1.FuncType([left.ty, right.ty], new type_expr_1.BoolType())) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        return _this;
    }
    EqualityExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    };
    EqualityExpr.prototype.toZ3Declaration = function (fd) {
        this.toZ3DeclarationSort(fd);
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    };
    return EqualityExpr;
}(FormulaExpr));
exports.EqualityExpr = EqualityExpr;
var NegExpr = /** @class */ (function (_super) {
    __extends(NegExpr, _super);
    function NegExpr(formula) {
        var _this = _super.call(this, "neg " + formula.name, "not", new type_expr_1.FuncType([formula.ty], new type_expr_1.BoolType())) || this;
        _this.formula = formula;
        return _this;
    }
    NegExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " " + this.formula.sexpr() + ")";
    };
    NegExpr.prototype.toZ3Declaration = function (fd) {
        this.toZ3DeclarationSort(fd);
        this.formula.toZ3Declaration(fd);
    };
    return NegExpr;
}(FormulaExpr));
exports.NegExpr = NegExpr;
var AndExpr = /** @class */ (function (_super) {
    __extends(AndExpr, _super);
    function AndExpr(left, right) {
        var _this = _super.call(this, left.name + " and " + right.name, "and", new type_expr_1.FuncType([left.ty, right.ty], new type_expr_1.BoolType())) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        return _this;
    }
    AndExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    };
    AndExpr.prototype.toZ3Declaration = function (fd) {
        this.toZ3DeclarationSort(fd);
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    };
    return AndExpr;
}(FormulaExpr));
exports.AndExpr = AndExpr;
var OrExpr = /** @class */ (function (_super) {
    __extends(OrExpr, _super);
    function OrExpr(left, right) {
        var _this = _super.call(this, left.name + " or " + right.name, "or", new type_expr_1.FuncType([left.ty, right.ty], new type_expr_1.BoolType())) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        return _this;
    }
    OrExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    };
    OrExpr.prototype.toZ3Declaration = function (fd) {
        this.toZ3DeclarationSort(fd);
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    };
    return OrExpr;
}(FormulaExpr));
exports.OrExpr = OrExpr;
var ImplExpr = /** @class */ (function (_super) {
    __extends(ImplExpr, _super);
    function ImplExpr(left, right) {
        var _this = _super.call(this, left.name + " implies " + right.name, "=>", new type_expr_1.FuncType([left.ty, right.ty], new type_expr_1.BoolType())) || this;
        _this.leftHandSide = left;
        _this.rightHandSide = right;
        return _this;
    }
    ImplExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " " + this.leftHandSide.sexpr() + " " + this.rightHandSide.sexpr() + ")";
    };
    ImplExpr.prototype.toZ3Declaration = function (fd) {
        this.toZ3DeclarationSort(fd);
        this.leftHandSide.toZ3Declaration(fd);
        this.rightHandSide.toZ3Declaration(fd);
    };
    return ImplExpr;
}(FormulaExpr));
exports.ImplExpr = ImplExpr;
var ForAllExpr = /** @class */ (function (_super) {
    __extends(ForAllExpr, _super);
    function ForAllExpr(nameBinder, formula) {
        var _this = _super.call(this, "forall " + nameBinder.name + ".l_" + formula.name + "_r", "forall", new type_expr_1.FuncType([nameBinder.ty, formula.ty], new type_expr_1.BoolType())) || this;
        _this.nameBinder = nameBinder;
        _this.formula = formula;
        return _this;
    }
    ForAllExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " ((" + this.nameBinder.symbolName + " " + this.nameBinder.ty.getType() + ")) " + this.formula.sexpr() + ")";
    };
    ForAllExpr.prototype.toZ3Declaration = function (fd) {
        this.toZ3DeclarationSort(fd);
        this.formula.toZ3Declaration(fd);
    };
    return ForAllExpr;
}(FormulaExpr));
exports.ForAllExpr = ForAllExpr;
var ExistsExpr = /** @class */ (function (_super) {
    __extends(ExistsExpr, _super);
    function ExistsExpr(nameBinder, formula) {
        var _this = _super.call(this, "exists " + nameBinder.name + ".l_" + formula.name + "_r", "exists", new type_expr_1.FuncType([nameBinder.ty, formula.ty], new type_expr_1.BoolType())) || this;
        _this.nameBinder = nameBinder;
        _this.formula = formula;
        return _this;
    }
    ExistsExpr.prototype.sexpr = function () {
        return "(" + this.symbolName + " ((" + this.nameBinder.symbolName + " " + this.nameBinder.ty.getType() + ")) " + this.formula.sexpr() + ")";
    };
    ExistsExpr.prototype.toZ3Declaration = function (fd) {
        this.toZ3DeclarationSort(fd);
        this.formula.toZ3Declaration(fd);
    };
    return ExistsExpr;
}(FormulaExpr));
exports.ExistsExpr = ExistsExpr;
