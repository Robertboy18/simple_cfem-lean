/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Quadrature.CSource.Semantics.Statements

/-!
# Decidable equality for typed C syntax

Derived `DecidableEq` instances for `IncrOrDecr`, `Expr`, `Exprlist`, `Stmt`,
`LabeledStatements` and `Function`, so that `decide +kernel` can compare an
elaborated function with the expected one in `Quadrature.CSource.Frontend.TypedFunctions`.
-/

namespace Quadrature.CSource.C

deriving instance DecidableEq for IncrOrDecr
deriving instance DecidableEq for Expr, Exprlist
deriving instance DecidableEq for Stmt, LabeledStatements
deriving instance DecidableEq for Function

end Quadrature.CSource.C
