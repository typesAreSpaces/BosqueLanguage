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
// Testing
var x = new term_expr_1.VarExpr("x", new type_expr_1.IntType());
var y = new term_expr_1.VarExpr("y", new type_expr_1.IntType());
var pxy = new formula_expr_1.PredicateExpr("p", [x, y, x, y, x, y]);
var fxy = new term_expr_1.FuncExpr("f", new type_expr_1.IntType(), [x, y]);
var extraLong = new formula_expr_1.ForAllExpr(x, new formula_expr_1.AndExpr(pxy, new formula_expr_1.ForAllExpr(y, new formula_expr_1.PredicateExpr("p", [fxy, x, x, y, fxy, x]))));
var fd = fs.openSync('file.z3', 'w');
// (new FuncExpr("g", new IntType(), [fxy, fxy])).toZ3Declaration(fd);
// (new FuncExpr("h", new IntType(), [])).toZ3Declaration(fd);
// (new FuncExpr("k", new IntType(), [fxy])).toZ3Declaration(fd);
extraLong.toZ3(fd);
pxy.toZ3(fd);
fs.closeSync(fd);
