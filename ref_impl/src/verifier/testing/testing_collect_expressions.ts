//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import * as FS from "fs";
import { bosqueToIRBody } from "../util"
// import { MIRBasicBlock } from "../../compiler/mir_ops";
import { collectExpr } from "../collect_expression";

setImmediate(() => {
    // Mac Machine
    // let directory = "/Users/joseabelcastellanosjoo/BosqueLanguage/ref_impl/src/test/apps/max/"
    // Windows Machine
    let directory = "/Users/t-jocast/code/BosqueLanguage/ref_impl/src/test/apps/max/";
    
    let fileName = "main.bsq";
    let section = "NSMain::max0";
    
    let fd = FS.openSync("_" + (section.split(":").join("") + "_" + fileName).replace("bsq", "fst"), 'w');
    fd;

    let [ir_body, sectionName] = bosqueToIRBody({directory: directory, fileName: fileName, section: section});
    let fstarProgram = collectExpr(ir_body, {directory: directory, fileName: fileName, section: sectionName});
    console.log(fstarProgram.toML());
    // FormulaExpr.initialDeclarationZ3(fd);
    // formula.toZ3(fd);
    // FormulaExpr.checkSatZ3(fd);
    
    // FS.closeSync(fd);
});