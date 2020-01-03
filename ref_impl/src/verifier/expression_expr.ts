//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { VarTerm, TermExpr, TupleProjExpr, FuncTerm, RecordProjExpr } from "./term_expr";
// import { ConstructorType } from "./type_expr";

abstract class ExprExpr {
    readonly tabSymbol = "  ";
    abstract toML(indentatioLevel: number, offset: number): string;
}

class ReturnExpr extends ExprExpr {
    readonly returnExpr: TermExpr;

    constructor(returnExpr: TermExpr) {
        super();
        this.returnExpr = returnExpr;
    }
    toML(indentatioLevel: number) {
        return this.tabSymbol.repeat(indentatioLevel) + this.returnExpr.toML();
    }
}

class AssignmentExpr extends ExprExpr {
    readonly lhs: VarTerm;
    readonly rhs: TermExpr;
    readonly continuation: ExprExpr;
    static assert_norm_flag: Set<string> = new Set<string>();

    constructor(lhs: VarTerm, rhs: TermExpr, continuation: ExprExpr) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
        this.continuation = continuation;
    }
    toML(indentatioLevel: number, offset: number) {
        // Add assertion_norm statemenet to the arguments of a function call
        // to make sure FStar has enough information to infere the right information 

        if (this.rhs instanceof TupleProjExpr) {
            const arg = this.rhs.tuple;

            if (!AssignmentExpr.assert_norm_flag.has(arg.fkey + arg.symbolName)) {
                AssignmentExpr.assert_norm_flag.add(arg.fkey + arg.symbolName);

                const assertion_norm = this.tabSymbol.repeat(indentatioLevel)
                    + "let _ = assert_norm(subtypeOf "
                    + arg.ty.id
                    + " (getType " + arg.toML() + ")) in\n";

                return assertion_norm
                    + this.tabSymbol.repeat(indentatioLevel)
                    + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in\n"
                    + this.continuation.toML(indentatioLevel, offset);
            }
            else {
                return this.tabSymbol.repeat(indentatioLevel)
                    + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in\n"
                    + this.continuation.toML(indentatioLevel, offset);
            }
        }

        if(this.rhs instanceof RecordProjExpr){
            const arg = this.rhs.record;

            if (!AssignmentExpr.assert_norm_flag.has(arg.fkey + arg.symbolName)) {
                AssignmentExpr.assert_norm_flag.add(arg.fkey + arg.symbolName);

                const assertion_norm = this.tabSymbol.repeat(indentatioLevel)
                    + "let _ = assert_norm(subtypeOf "
                    + arg.ty.id
                    + " (getType " + arg.toML() + ")) in\n";

                return assertion_norm
                    + this.tabSymbol.repeat(indentatioLevel)
                    + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in\n"
                    + this.continuation.toML(indentatioLevel, offset);
            }
            else {
                return this.tabSymbol.repeat(indentatioLevel)
                    + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in\n"
                    + this.continuation.toML(indentatioLevel, offset);
            }
        }

        if (this.rhs instanceof FuncTerm) {
            const args = this.rhs.terms;
            const assertion_norm = args.reduce((accum, current_expr) => {
                if (!AssignmentExpr.assert_norm_flag.has(current_expr.fkey + current_expr.symbolName)) {
                    AssignmentExpr.assert_norm_flag.add(current_expr.fkey + current_expr.symbolName);

                    const local_assertion_norm = "let _ = assert_norm(subtypeOf " + current_expr.ty.id
                        + " (getType " + current_expr.toML() + ")) in";
                    return this.tabSymbol.repeat(indentatioLevel) + local_assertion_norm + "\n" + accum;
                }
                else {
                    return accum;
                }
            }, "");

            return assertion_norm
                + this.tabSymbol.repeat(indentatioLevel)
                + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in\n"
                + this.continuation.toML(indentatioLevel, offset);
        }

        else {
            return this.tabSymbol.repeat(indentatioLevel)
                + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in\n"
                + this.continuation.toML(indentatioLevel, offset);
        }
    }
}

class ConditionalExpr extends ExprExpr {
    readonly condition: TermExpr;
    readonly ifBranch: ExprExpr;
    readonly elseBranch: ExprExpr;

    constructor(condition: TermExpr, ifBranch: ExprExpr, elseBranch: ExprExpr) {
        super();
        this.condition = condition;
        this.ifBranch = ifBranch;
        this.elseBranch = elseBranch;
    }
    toML(indentatioLevel: number, offset: number) {
        return this.tabSymbol.repeat(indentatioLevel)
            + "if " + this.condition.toML() + " then \n"
            + this.ifBranch.toML(indentatioLevel + offset, offset) + "\n"
            + this.tabSymbol.repeat(indentatioLevel) + "else \n"
            + this.elseBranch.toML(indentatioLevel + offset, offset);
    }
}

export { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr }