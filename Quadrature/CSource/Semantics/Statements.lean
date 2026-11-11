/-
Derived from CompCert 3.17 cfrontend/Csyntax.v.
CompCert distributes that file under the INRIA Non-Commercial License Agreement or the
GNU LGPL 2.1 or later; NOTICE gives the terms.
Copyright (c) 2026 simple_cfem-lean Team for our changes.
-/
import Quadrature.CSource.Semantics.Syntax

/-!
# C statement and function syntax

`Stmt`, `LabeledStatements` and `Function` follow CompCert's C syntax constructor for
constructor and field for field. `Sfor` keeps its initializer, condition, increment and body,
and `Sdo` keeps an expression statement with its side effects. `ExecStmt` of
`Quadrature.CSource.Semantics.Strategy` and the machine of
`Quadrature.CSource.Semantics.SmallStep` both execute these statements.

## References

* CompCert 3.17,
  [`cfrontend/Csyntax.v`](https://github.com/AbsInt/CompCert/blob/7b1f02b09954b9b916eb2a91d283c9b5355bf172/cfrontend/Csyntax.v):
  `statement`, `labeled_statements` and `function`.
-/

namespace Quadrature.CSource.C

open CC

mutual
/-- C statements. `Sdo a` evaluates `a` for its effects, `Sfor init test incr body` is the
three-clause loop, and `Sswitch` carries its labeled cases. -/
inductive Stmt where
  | Sskip
  | Sdo (value : Expr)
  | Ssequence (first second : Stmt)
  | Sifthenelse (test : Expr) (yes no : Stmt)
  | Swhile (test : Expr) (body : Stmt)
  | Sdowhile (test : Expr) (body : Stmt)
  | Sfor (initial : Stmt) (test : Expr) (increment body : Stmt)
  | Sbreak
  | Scontinue
  | Sreturn (value : Option Expr)
  | Sswitch (value : Expr) (cases : LabeledStatements)
  | Slabel (name : Ident) (body : Stmt)
  | Sgoto (name : Ident)

/-- The cases of a `switch`: each carries an optional integer label (`none` for `default`) and a
body. -/
inductive LabeledStatements where
  | LSnil
  | LScons (value : Option Int) (body : Stmt) (rest : LabeledStatements)
end

/-- A C function: return type, calling convention, parameters, local variables and body. There is
no temporary list, since every local lives in memory. -/
structure Function where
  fn_return : Ty
  fn_callconv : CallConv
  fn_params : List (Ident × Ty)
  fn_vars : List (Ident × Ty)
  fn_body : Stmt

end Quadrature.CSource.C
