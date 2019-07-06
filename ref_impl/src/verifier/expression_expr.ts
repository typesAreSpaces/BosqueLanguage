import { VarTerm, TermExpr } from "./term_expr";

//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

abstract class ExprExpr {
    abstract toFStarDeclaration(fd: number): void;
    abstract toML(): string;
}

class ReturnExpr extends ExprExpr {
    readonly returnExpr : TermExpr;
    constructor(returnExpr : TermExpr){
        super();
        this.returnExpr = returnExpr;
    }
    toFStarDeclaration(fd : number){

    }
    toML(){
        return this.returnExpr.toML();
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
    toFStarDeclaration(fd: number){
        
    }
    toML(){
        return "let " + this.lhs.toML() + " = " + this.rhs.toML() + " in " + this.continuation.toML();
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
    toFStarDeclaration(fd: number){
        
    }
    toML(){
        return "if " + this.condition.toML() + " then " + this.ifBranch.toML() + " else " + this.elseBranch.toML();
    }
}

export { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr }