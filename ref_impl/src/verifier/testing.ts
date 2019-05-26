//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { IntType, BoolType } from "./type_expr";
import { VarExpr, FuncExpr } from "./term_expr"
import { PredicateExpr, ForAllExpr, AndExpr, NegExpr, OrExpr, EqualityExpr } from "./formula_expr"
import * as fs from "fs";

// Testing
let x = new VarExpr("x", new IntType());
let y = new VarExpr("y", new IntType());
let a = new PredicateExpr("a", []);
let b = new PredicateExpr("b", []);
let pxy = new PredicateExpr("p", [x, y, x, y, x, y]);
let fxy = new FuncExpr("f", new IntType(), [x, y]);
let extraLong = new ForAllExpr(x, 
    new AndExpr( 
        pxy, 
        new ForAllExpr(y, new PredicateExpr("p", [fxy, x, x, y, fxy, x]))
    ));

let fd = fs.openSync('file.z3', 'w');
// Setting optionalGetModel to true
// will include a (get-model) command
// to the Z3 file; otherwise it wont
pxy.toZ3(fd, false);
pxy.toZ3(fd, true);
// Encoding DeMorgan's law
(new NegExpr(new EqualityExpr(new AndExpr(a, b), new NegExpr(new OrExpr(new NegExpr(a), new NegExpr(b)))))).toZ3(fd, false);
// Testing a predicate
(new PredicateExpr("narda", [pxy, x])).toZ3(fd, false); 
fs.closeSync(fd);