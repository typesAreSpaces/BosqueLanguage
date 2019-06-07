//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { IntType, UninterpretedType } from "../type_expr";
import { VarExpr, FuncExpr } from "../term_expr"
import { PredicateExpr, AndExpr, NegExpr, OrExpr, EqualityExpr } from "../formula_expr"
import * as fs from "fs";

let fd = fs.openSync('file.z3', 'w');

// Testing
let x = new VarExpr("x", new IntType());
let y = new VarExpr("y", new IntType());
let a = new PredicateExpr("a", []);
let b = new PredicateExpr("b", []);
let pxy = new PredicateExpr("p", [x, y, x, y, x, y]);
// let fxy = new FuncExpr("f", new IntType(), [x, y]);
// let extraLong = new ForAllExpr(x, 
//     new AndExpr( 
//         pxy, 
//         new ForAllExpr(y, new PredicateExpr("p", [fxy, x, x, y, fxy, x]))
//     ));

// Repeating the same formula
// wont produce repeated declarations
pxy.toZ3(fd);
pxy.toZ3(fd);
// extraLong.toZ3(fd);

// Encoding DeMorgan's law
new NegExpr(new EqualityExpr(new AndExpr(a, b), new NegExpr(new OrExpr(new NegExpr(a), new NegExpr(b))))).toZ3(fd);

// Testing a predicate
new PredicateExpr("narda", [pxy, x]).toZ3(fd);
new PredicateExpr("g", [new VarExpr("z", new UninterpretedType("List_Int_"))]).toZ3(fd);
new PredicateExpr("g", [new VarExpr("z", new UninterpretedType("List_Int_"))]).toZ3(fd);
new PredicateExpr("p", [x, y, x, y, x, y]).toZ3(fd);

let p1 = new PredicateExpr("p", [x, x, x, x, x, x])
p1.toZ3(fd);
let p2 = new PredicateExpr("p", [x, x, x, x, x, y])
p2.toZ3(fd);
let p3 = new PredicateExpr("p", [x, x, x, x, y, x])
p3.toZ3(fd);
let p4 = new PredicateExpr("p", [x, x, x, y, x, x])
p4.toZ3(fd);

(new FuncExpr("f", new IntType(), [x, x])).toZ3Declaration(fd);
(new FuncExpr("f", new IntType(), [x, y])).toZ3Declaration(fd);
(new FuncExpr("f", new IntType(), [y, x])).toZ3Declaration(fd);
(new FuncExpr("f", new IntType(), [y, y])).toZ3Declaration(fd);

let newOne = new AndExpr(pxy, pxy);
newOne.toZ3(fd);

let secondRound = new VarExpr("sdffafd", new UninterpretedType("List_Int"));
(new EqualityExpr(secondRound, secondRound)).toZ3(fd);

fs.closeSync(fd);
