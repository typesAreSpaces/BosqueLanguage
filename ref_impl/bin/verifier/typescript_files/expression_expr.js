"use strict";
//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------
Object.defineProperty(exports, "__esModule", { value: true });
const term_expr_1 = require("./term_expr");
// import { ConstructorType } from "./type_expr";
class ExprExpr {
    constructor() {
        this.tab_symbols = "  ";
    }
}
exports.ExprExpr = ExprExpr;
class ReturnExpr extends ExprExpr {
    constructor(return_expr) {
        super();
        this.return_expr = return_expr;
    }
    toML(indentation_level) {
        return this.tab_symbols.repeat(indentation_level) + this.return_expr.toML();
    }
}
exports.ReturnExpr = ReturnExpr;
class AssignmentExpr extends ExprExpr {
    constructor(lhs, rhs, continuation) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
        this.continuation = continuation;
    }
    toML(indentation_level, offset) {
        // Add assertion_norm statemenet to the arguments of a function call
        // to make sure FStar has enough information to infere the right information 
        if (this.rhs instanceof term_expr_1.TupleProjExpr) {
            const arg = this.rhs.tuple;
            if (!AssignmentExpr.assert_norm_flag.has(arg.fkey + arg.symbol_name)) {
                AssignmentExpr.assert_norm_flag.add(arg.fkey + arg.symbol_name);
                const assertion_norm = this.tab_symbols.repeat(indentation_level)
                    + "let _ = assert_norm(subtypeOf "
                    + arg.ty.fstar_type_encoding
                    + " (getType " + arg.toML() + ")) in\n";
                return assertion_norm
                    + this.tab_symbols.repeat(indentation_level)
                    + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in\n"
                    + this.continuation.toML(indentation_level, offset);
            }
            else {
                return this.tab_symbols.repeat(indentation_level)
                    + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in\n"
                    + this.continuation.toML(indentation_level, offset);
            }
        }
        if (this.rhs instanceof term_expr_1.RecordProjExpr) {
            const arg = this.rhs.record;
            if (!AssignmentExpr.assert_norm_flag.has(arg.fkey + arg.symbol_name)) {
                AssignmentExpr.assert_norm_flag.add(arg.fkey + arg.symbol_name);
                const assertion_norm = this.tab_symbols.repeat(indentation_level)
                    + "let _ = assert_norm(subtypeOf "
                    + arg.ty.fstar_type_encoding
                    + " (getType " + arg.toML() + ")) in\n";
                return assertion_norm
                    + this.tab_symbols.repeat(indentation_level)
                    + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in\n"
                    + this.continuation.toML(indentation_level, offset);
            }
            else {
                return this.tab_symbols.repeat(indentation_level)
                    + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in\n"
                    + this.continuation.toML(indentation_level, offset);
            }
        }
        if (this.rhs instanceof term_expr_1.FuncTerm) {
            const args = this.rhs.terms;
            const assertion_norm = args.reduce((accum, current_expr) => {
                if (!AssignmentExpr.assert_norm_flag.has(current_expr.fkey + current_expr.symbol_name)) {
                    AssignmentExpr.assert_norm_flag.add(current_expr.fkey + current_expr.symbol_name);
                    const local_assertion_norm = "let _ = assert_norm(subtypeOf " + current_expr.ty.fstar_type_encoding
                        + " (getType " + current_expr.toML() + ")) in";
                    return this.tab_symbols.repeat(indentation_level) + local_assertion_norm + "\n" + accum;
                }
                else {
                    return accum;
                }
            }, "");
            return assertion_norm
                + this.tab_symbols.repeat(indentation_level)
                + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in\n"
                + this.continuation.toML(indentation_level, offset);
        }
        else {
            return this.tab_symbols.repeat(indentation_level)
                + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in\n"
                + this.continuation.toML(indentation_level, offset);
        }
    }
}
exports.AssignmentExpr = AssignmentExpr;
AssignmentExpr.assert_norm_flag = new Set();
class ConditionalExpr extends ExprExpr {
    constructor(condition, if_branch, else_branch) {
        super();
        this.condition = condition;
        this.if_branch = if_branch;
        this.else_branch = else_branch;
    }
    toML(indentation_level, offset) {
        return this.tab_symbols.repeat(indentation_level)
            + "if (extractBool " + this.condition.toML() + ") then \n"
            + this.if_branch.toML(indentation_level + offset, offset) + "\n"
            + this.tab_symbols.repeat(indentation_level) + "else \n"
            + this.else_branch.toML(indentation_level + offset, offset);
    }
}
exports.ConditionalExpr = ConditionalExpr;
//# sourceMappingURL=expression_expr.js.map