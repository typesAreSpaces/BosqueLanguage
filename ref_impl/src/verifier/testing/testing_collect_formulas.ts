//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import { bosqueToIRBody } from "../util"
import { collectFormula } from "../collect_formula";
import { FormulaExpr } from "../formula_expr"

setImmediate(() => {
    // Mac Machine
    // let directory = "/Users/joseabelcastellanosjoo/BosqueLanguage/ref_impl/src/test/apps"
    // Windows Machine
    let directory = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/max/";
    
    let fileName = "main.bsq";
    let section = "NSMain::main";
    
    let fd = FS.openSync("_" + (section.split(":").join("") + "_" + fileName).replace("bsq", "z3"), 'w');
    
    let [ir_body, sectionName] = bosqueToIRBody({directory: directory, fileName: fileName, section: section});
    let formula = collectFormula(ir_body, {directory: directory, fileName: fileName, section: sectionName});

    FormulaExpr.initialDeclarationZ3(fd);
    formula.toZ3(fd);
    FormulaExpr.checkSatZ3(fd);
    
    FS.closeSync(fd);
});
