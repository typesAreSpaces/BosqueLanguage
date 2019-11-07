//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { VarTerm, TermExpr } from "./term_expr";

abstract class ExprExpr {
    readonly tabSymbol = " ";
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
    constructor(lhs: VarTerm, rhs: TermExpr, continuation: ExprExpr) {
        super();
        this.lhs = lhs;
        this.rhs = rhs;
        this.continuation = continuation;
    }
    toML(indentatioLevel: number, offset: number) {
        return this.tabSymbol.repeat(indentatioLevel)
            + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in \n"
            + this.continuation.toML(indentatioLevel + offset, offset);
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
    toML(indentatioLevel: number, offset : number) {
        return this.tabSymbol.repeat(indentatioLevel)
            + "if " + this.condition.toML() + " then \n"
            + this.ifBranch.toML(indentatioLevel + offset, offset) + "\n"
            + this.tabSymbol.repeat(indentatioLevel) + "else \n"
            + this.elseBranch.toML(indentatioLevel + offset, offset);
    } 
}

export { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr }