//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { IntType } from "./type_expr";
import { VarExpr, FuncExpr } from "./term_expr"
import { PredicateExpr, ForAllExpr, AndExpr } from "./formula_expr"
import * as fs from "fs";

// Testing
let x = new VarExpr("x", new IntType());
let y = new VarExpr("y", new IntType());
let pxy = new PredicateExpr("p", [x, y, x, y, x, y]);
let fxy = new FuncExpr("f", new IntType(), [x, y]);
let extraLong = new ForAllExpr(x, 
    new AndExpr( 
        pxy, 
        new ForAllExpr(y, new PredicateExpr("p", [fxy, x, x, y, fxy, x]))
    ));

let fd = fs.openSync('file.z3', 'w');
extraLong.toZ3(fd);
pxy.toZ3(fd);

fs.closeSync(fd);