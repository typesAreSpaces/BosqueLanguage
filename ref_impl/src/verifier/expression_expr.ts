//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { VarTerm, TermExpr } from "./term_expr";

abstract class ExprExpr {
    abstract toML(indentatioLevel : number): string;
}

class ReturnExpr extends ExprExpr {
    readonly returnExpr : TermExpr;
    constructor(returnExpr : TermExpr){
        super();
        this.returnExpr = returnExpr;
    }
    toML(indentatioLevel : number){
        return "\t".repeat(indentatioLevel) + this.returnExpr.toML();
    }
}

class AssignmentExpr extends ExprExpr {
    readonly lhs : VarTerm;
    readonly rhs : TermExpr;
    readonly continuation : ExprExpr;
    constructor(lhs : VarTerm, rhs : TermExpr, continuation : ExprExpr){
        super();
        this.lhs = lhs;
        this.rhs = rhs;
        this.continuation = continuation;
    }
    toML(indentatioLevel : number){
        return "\t".repeat(indentatioLevel) + "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in \n" 
        + this.continuation.toML(indentatioLevel + 1);
    }
}

class ConditionalExpr extends ExprExpr {
    readonly condition : TermExpr;
    readonly ifBranch : ExprExpr;
    readonly elseBranch : ExprExpr;
    constructor(condition : TermExpr, ifBranch : ExprExpr, elseBranch : ExprExpr){
        super();
        this.condition = condition;
        this.ifBranch = ifBranch;
        this.elseBranch = elseBranch;
    }
    toML(indentatioLevel : number){
        return "\t".repeat(indentatioLevel) + "if " + this.condition.toML() + " then \n" 
        + this.ifBranch.toML(indentatioLevel + 1) + "\n" 
        + "\t".repeat(indentatioLevel) + "else \n" 
        + this.elseBranch.toML(indentatioLevel + 1);
    }
}

export { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr }