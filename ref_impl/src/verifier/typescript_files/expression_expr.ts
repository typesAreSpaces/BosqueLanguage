//-------------------------------------------------------------------------------------------------------
// Copyright (C) Microsoft. All rights reserved.
// Licensed under the MIT license. See LICENSE.txt file in the project root for full license information.
//-------------------------------------------------------------------------------------------------------

import { VarTerm, TermExpr, TupleProjExpr, FuncTerm, RecordProjExpr } from "./term_expr";
// import { ConstructorType } from "./type_expr";

abstract class ExprExpr {
  readonly tab_symbols = "  ";
  abstract toML(indentation_level: number, offset: number): string;
}

class ReturnExpr extends ExprExpr {
  readonly return_expr: TermExpr;

  constructor(return_expr: TermExpr) {
    super();
    this.return_expr = return_expr;
  }
  toML(indentation_level: number) {
    return this.tab_symbols.repeat(indentation_level) + this.return_expr.toML();
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
  toML(indentation_level: number, offset: number) {
    // Add assertion_norm statemenet to the arguments of a function call
    // to make sure FStar has enough information to infere the right information 

    if (this.rhs instanceof TupleProjExpr) {
      const arg = this.rhs.tuple;

      if (!AssignmentExpr.assert_norm_flag.has(arg.fkey + arg.symbol_name)) {
        AssignmentExpr.assert_norm_flag.add(arg.fkey + arg.symbol_name);

        const assertion_norm = this.tab_symbols.repeat(indentation_level)
          + "let _ = assert_norm(subtypeOf "
          + arg.ty.id
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

    if(this.rhs instanceof RecordProjExpr){
      const arg = this.rhs.record;

      if (!AssignmentExpr.assert_norm_flag.has(arg.fkey + arg.symbol_name)) {
        AssignmentExpr.assert_norm_flag.add(arg.fkey + arg.symbol_name);

        const assertion_norm = this.tab_symbols.repeat(indentation_level)
          + "let _ = assert_norm(subtypeOf "
          + arg.ty.id
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

    if (this.rhs instanceof FuncTerm) {
      const args = this.rhs.terms;
      const assertion_norm = args.reduce((accum, current_expr) => {
        if (!AssignmentExpr.assert_norm_flag.has(current_expr.fkey + current_expr.symbol_name)) {
          AssignmentExpr.assert_norm_flag.add(current_expr.fkey + current_expr.symbol_name);

          const local_assertion_norm = "let _ = assert_norm(subtypeOf " + current_expr.ty.id
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

class ConditionalExpr extends ExprExpr {
  readonly condition: TermExpr;
  readonly if_branch: ExprExpr;
  readonly else_branch: ExprExpr;

  constructor(condition: TermExpr, if_branch: ExprExpr, else_branch: ExprExpr) {
    super();
    this.condition = condition;
    this.if_branch = if_branch;
    this.else_branch = else_branch;
  }
  toML(indentation_level: number, offset: number) {
    return this.tab_symbols.repeat(indentation_level)
      + "if (extractBool " + this.condition.toML() + ") then \n"
      + this.if_branch.toML(indentation_level + offset, offset) + "\n"
      + this.tab_symbols.repeat(indentation_level) + "else \n"
      + this.else_branch.toML(indentation_level + offset, offset);
  }
}

export { ExprExpr, ReturnExpr, AssignmentExpr, ConditionalExpr }
