"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
exports.__esModule = true;
var type_expr_1 = require("./type_expr");
var term_expr_1 = require("./term_expr");
var formula_expr_1 = require("./formula_expr");
var fs = require("fs");
var fd = fs.openSync('file.z3', 'w');
// Testing
var x = new term_expr_1.VarExpr("x", new type_expr_1.IntType());
var y = new term_expr_1.VarExpr("y", new type_expr_1.IntType());
var a = new formula_expr_1.PredicateExpr("a", []);
var b = new formula_expr_1.PredicateExpr("b", []);
var pxy = new formula_expr_1.PredicateExpr("p", [x, y, x, y, x, y]);
var fxy = new term_expr_1.FuncExpr("f", new type_expr_1.IntType(), [x, y]);
var extraLong = new formula_expr_1.ForAllExpr(x, new formula_expr_1.AndExpr(pxy, new formula_expr_1.ForAllExpr(y, new formula_expr_1.PredicateExpr("p", [fxy, x, x, y, fxy, x]))));
// Repeating the same formula
// wont produce repeated declarations
pxy.toZ3(fd, false);
pxy.toZ3(fd, true);
extraLong.toZ3(fd, true);
// Encoding DeMorgan's law
new formula_expr_1.NegExpr(new formula_expr_1.EqualityExpr(new formula_expr_1.AndExpr(a, b), new formula_expr_1.NegExpr(new formula_expr_1.OrExpr(new formula_expr_1.NegExpr(a), new formula_expr_1.NegExpr(b))))).toZ3(fd, false);
// Testing a predicate
new formula_expr_1.PredicateExpr("narda", [pxy, x]).toZ3(fd, false);
new formula_expr_1.PredicateExpr("g", [new term_expr_1.VarExpr("z", new type_expr_1.UninterpretedType("List_Int_"))]).toZ3(fd, true);
new formula_expr_1.PredicateExpr("g", [new term_expr_1.VarExpr("z", new type_expr_1.UninterpretedType("List_Int_"))]).toZ3(fd, true);
new formula_expr_1.PredicateExpr("p", [x, y, x, y, x, y]).toZ3(fd, true);
var p1 = new formula_expr_1.PredicateExpr("p", [x, x, x, x, x, x]);
p1.toZ3(fd, false);
var p2 = new formula_expr_1.PredicateExpr("p", [x, x, x, x, x, y]);
p2.toZ3(fd, false);
var p3 = new formula_expr_1.PredicateExpr("p", [x, x, x, x, y, x]);
p3.toZ3(fd, false);
var p4 = new formula_expr_1.PredicateExpr("p", [x, x, x, y, x, x]);
p4.toZ3(fd, false);
(new term_expr_1.FuncExpr("f", new type_expr_1.IntType(), [x, x])).toZ3Declaration(fd);
(new term_expr_1.FuncExpr("f", new type_expr_1.IntType(), [x, y])).toZ3Declaration(fd);
(new term_expr_1.FuncExpr("f", new type_expr_1.IntType(), [y, x])).toZ3Declaration(fd);
(new term_expr_1.FuncExpr("f", new type_expr_1.IntType(), [y, y])).toZ3Declaration(fd);
fs.closeSync(fd);
