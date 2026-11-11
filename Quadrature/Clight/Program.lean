/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Quadrature.Clight.Execution
import Quadrature.Clight.Source
import Quadrature.Clight.TableData
import Quadrature.Examples.PolynomialCosine

/-!
# A Clight library context for the polynomial quadrature applications

`polynomialLibrary` is a CLean `Program` holding the two tables and five
function bodies imported from the original C program, plus the internal
polynomial `polynomialFunction` at the `cos` symbol. This follows the
companion Rocq proofs in `rocq/clight/InternalCosine.v`, which put the same
polynomial in place of the library cosine. `initialMemory`
is the program's initialized global memory, and `testfunBlock` is the block of
the callback. `LibraryCallbackContract` is what the integrator theorems
ask of the callback in any surrounding program. Vocabulary: see
`Quadrature.Clight.Execution`.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`src/quadrules.c`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/src/quadrules.c):
  `gauss_point`, `gauss_weight`, `integrate`, `testfun` and `integrate_testfun`, with the tables
  `gauss_pts` and `gauss_wts`.
-/

namespace Quadrature.Binary64.Clight

open FloatLib.Floats.Formats.BinaryInterchange
open ClightSource

/-- A read-only, nonvolatile global array of 55 `double`s initialized from the 64-bit encodings
`bits`, the shape of the two C tables. -/
def tableGlobal (bits : List Nat) : CC.GlobVar CC.Ty where
  gvar_info := CC.tarray CC.tdouble 55
  gvar_init := bits.map fun n => .Init_float64 (Model.ofNatBits n)
  gvar_readonly := true
  gvar_volatile := false

/-- The parameter identifier of `polynomialFunction`. -/
def polynomialArgument : CC.Ident := CC.Positive.ofNat 4000
/-- The temporary of `polynomialFunction` holding the squared argument. -/
def polynomialSquare : CC.Ident := CC.Positive.ofNat 4001

/-- The Clight expression for Horner evaluation of the coefficients `cs` at the temporary
`polynomialSquare`, `c₀ + z * (c₁ + z * (... + z * 0))`, with every multiplication and addition a
separate rounded `double` operation, as in `Polynomial.horner`. -/
def hornerExpression : List Value → CC.Expr
  | [] => .Econst_float zero CC.tdouble
  | c :: cs =>
    .Ebinop .Oadd (.Econst_float c CC.tdouble)
      (.Ebinop .Omul (.Etempvar polynomialSquare CC.tdouble)
        (hornerExpression cs) CC.tdouble) CC.tdouble

/-- The Clight function placed at the `cos` symbol: it squares its argument and evaluates the
polynomial `Polynomial.coefficients` (degree fourteen in `x`, eight coefficients in `x²`) by
Horner's rule, computing `Polynomial.cosine`. -/
def polynomialFunction : CC.Function where
  fn_return := CC.tdouble
  fn_callconv := CC.cc_default
  fn_params := [(polynomialArgument, CC.tdouble)]
  fn_vars := []
  fn_temps := [(polynomialSquare, CC.tdouble)]
  fn_body :=
    .Ssequence
      (.Sset polynomialSquare
        (.Ebinop .Omul (.Etempvar polynomialArgument CC.tdouble)
          (.Etempvar polynomialArgument CC.tdouble) CC.tdouble))
      (.Sreturn (some (hornerExpression Polynomial.coefficients)))

/-- The CLean program with the two tables, the five imported functions and `polynomialFunction`
at `cos`, in that order, so the blocks are 1 to 8. Its main symbol is `integrate_testfun`, and
globals of the original file that these functions do not reference are omitted. -/
def polynomialLibrary : CC.Program :=
  CC.mkprogram []
    [(_gauss_pts, .Gvar (tableGlobal ClightTableData.nodeBits)),
     (_gauss_wts, .Gvar (tableGlobal ClightTableData.weightBits)),
     (_gauss_point, .Gfun (.Internal f_gauss_point)),
     (_gauss_weight, .Gfun (.Internal f_gauss_weight)),
     (_integrate, .Gfun (.Internal f_integrate)),
     (_testfun, .Gfun (.Internal f_testfun)),
     (_integrate_testfun, .Gfun (.Internal f_integrate_testfun)),
     (_cos, .Gfun (.Internal polynomialFunction))]
    [] _integrate_testfun

/-- The initialized global memory of `polynomialLibrary`. The `getD` fallback never applies, by
`polynomialLibrary_initialized`. -/
def initialMemory : CC.Mem := polynomialLibrary.initMem.getD CC.Mem.empty

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- Compute the global initialization of the eight definitions, including the 110 table words.
/-- Global initialization of `polynomialLibrary` succeeds, by kernel evaluation. -/
theorem polynomialLibrary_initializes :
    polynomialLibrary.initMem.isSome = true := by
  decide +kernel

/-- The initialized memory of `polynomialLibrary` is `initialMemory`. -/
theorem polynomialLibrary_initialized :
    polynomialLibrary.initMem = some initialMemory := by
  have h := polynomialLibrary_initializes
  unfold initialMemory
  cases hm : polynomialLibrary.initMem <;> simp_all

/-- The block of the `testfun` symbol, the sixth global definition of `polynomialLibrary`. -/
def testfunBlock : CC.Block := CC.Positive.ofNat 6

/-- `LibraryCallbackContract ge memory ptr fd f`: `ptr` resolves to `fd`, `fd` has type
`double (double)`, and calling `fd` on `Vfloat x` from `memory` under any call continuation `k`
returns `Vfloat (f x)` silently with `memory` unchanged. Nothing is assumed about the enclosing
integrator. Discharged by `polynomial_callback_contract_in_context` for the original callback. -/
structure LibraryCallbackContract [CC.ExternalCalls] (ge : CC.CGenv) (memory : CC.Mem)
    (ptr : CC.Val) (fd : CC.FunDef) (f : Value → Value) : Prop where
  function_eq : CC.Genv.findFunct ge.genv_genv ptr = some fd
  type_eq : CC.typeOfFundef fd = .Tfunction [CC.tdouble] CC.tdouble CC.cc_default
  execution : ∀ (x : Value) (k : CC.Cont), CC.isCallCont k = true →
    CC.StarE0 (CC.Step2 ge) (.Callstate fd [.Vfloat x] k memory)
      (.Returnstate (.Vfloat (f x)) k memory)

end Quadrature.Binary64.Clight
