/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Quadrature.Clight.Loop

/-!
# Execution with all ten stored rules

`callbackLibrary fd` is `polynomialLibrary` with the `testfun` definition replaced by an arbitrary
`fd`; the two initialized tables, the wrapper and the internal cosine polynomial are unchanged.
`CallbackContract fd f` asks that `fd` return `Vfloat (f x)` silently, with memory unchanged, on
every binary64 input, and `polynomial_callback_contract` discharges it for the original callback
with the internal polynomial at `cos`. `polynomial_callback_contract_in_context` does the same in
any program where `cos` resolves to that polynomial.

The two 55-entry tables of the original C program hold the rules with one
through ten nodes. `storedTerms n` selects the contiguous triangular slice of
the `n`-node rule as (weight, node) pairs, keeping every binary64 encoding.
`stored_table_cells` shows that the initialized memory of `polynomialLibrary`
holds those cells, `storedContext` packages the symbol and memory conditions
of `stored_library_execution`, and the polynomial callback supplies the call
contract. The zero-node case returns positive zero without reading the tables.
These results establish execution and bit-for-bit return values. The integral
error bounds for the ten polynomial applications are in
`Quadrature.Clight.StoredAccuracy`.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`src/quadrules.c`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/src/quadrules.c):
  `testfun` and the tables `gauss_pts` and `gauss_wts`.
-/

namespace Quadrature.Binary64.Clight
open FloatLib.Floats.Formats.BinaryInterchange
open ClightSource

/-- `polynomialLibrary` with the definition at the `testfun` symbol replaced by `fd`. Every other
global, and hence every block number, is the same. -/
def callbackLibrary (fd : CC.FunDef) : CC.Program :=
  CC.mkprogram []
    [(_gauss_pts, .Gvar (tableGlobal ClightTableData.nodeBits)),
     (_gauss_wts, .Gvar (tableGlobal ClightTableData.weightBits)),
     (_gauss_point, .Gfun (.Internal f_gauss_point)),
     (_gauss_weight, .Gfun (.Internal f_gauss_weight)),
     (_integrate, .Gfun (.Internal f_integrate)),
     (_testfun, .Gfun fd),
     (_integrate_testfun, .Gfun (.Internal f_integrate_testfun)),
     (_cos, .Gfun (.Internal polynomialFunction))]
    [] _integrate_testfun

/-- `CallbackContract fd f`: `fd` has type `double (double)` and, in `callbackLibrary fd` from
`initialMemory`, calling it on `Vfloat x` under any call continuation returns `Vfloat (f x)`
silently with memory unchanged. Only the callback is constrained. Discharged for the original
callback by `polynomial_callback_contract`. -/
structure CallbackContract [CC.ExternalCalls] (fd : CC.FunDef) (f : Value → Value) : Prop where
  type_eq : CC.typeOfFundef fd = .Tfunction [CC.tdouble] CC.tdouble CC.cc_default
  execution : ∀ (x : Value) (k : CC.Cont), CC.isCallCont k = true →
    CC.StarE0 (CC.Step2 (callbackLibrary fd).globalenv)
      (.Callstate fd [.Vfloat x] k initialMemory)
      (.Returnstate (.Vfloat (f x)) k initialMemory)

/-- A `CallbackContract` yields the `LibraryCallbackContract` for the pointer to `testfunBlock` in
`callbackLibrary fd`. -/
theorem CallbackContract.library_contract [CC.ExternalCalls]
    {fd : CC.FunDef} {f : Value → Value} (contract : CallbackContract fd f) :
    LibraryCallbackContract (callbackLibrary fd).globalenv initialMemory
      (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) fd f :=
  ⟨by rfl, contract.type_eq, contract.execution⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
-- Step through `f_testfun`, resolving the `cos` call to `polynomialFunction` and unfolding it.
/-- In any global environment where `cos` resolves to `polynomialFunction`, calling `f_testfun`
on `Vfloat x` returns `Vfloat (testfun_f Polynomial.cosine x)` silently with memory unchanged. -/
theorem polynomial_callback_execution_in_context [CC.ExternalCalls]
    (ge : CC.CGenv) (m : CC.Mem) (cosBlock : CC.Block)
    (hsymbol : CC.Genv.findSymbol ge.genv_genv _cos = some cosBlock)
    (hfunction : CC.Genv.findFunct ge.genv_genv (.Vptr cosBlock CC.Integers.Ptrofs.zero) =
      some (.Internal polynomialFunction)) (x : Value) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 ge) (.Callstate (.Internal f_testfun) [.Vfloat x] k m)
      (.Returnstate (.Vfloat (testfun_f Polynomial.cosine x)) (CC.callCont k) m) := by
  repeat'
    first
    | (guard_target =~ CC.StarE0 _ (.Returnstate _ (CC.callCont k) _) _
       exact CC.StarE0.refl _)
    | refine CC.StarE0.step _ _ _ (CC.doStep_sound _ _ _ _ (by rfl)) ?_
    | refine CC.StarE0.step _ _ _ (call_step (by rfl)
        (global_reference _ _ _ _ _ _ (by rfl) hsymbol) (by rfl) hfunction (by rfl)) ?_

/-- When `ptr` resolves to `f_testfun` and `cos` to `polynomialFunction`, the original callback
satisfies `LibraryCallbackContract` with `f = testfun_f Polynomial.cosine`. -/
theorem polynomial_callback_contract_in_context [CC.ExternalCalls]
    (ge : CC.CGenv) (m : CC.Mem) (ptr : CC.Val) (cosBlock : CC.Block)
    (hcallback : CC.Genv.findFunct ge.genv_genv ptr = some (.Internal f_testfun))
    (hsymbol : CC.Genv.findSymbol ge.genv_genv _cos = some cosBlock)
    (hfunction : CC.Genv.findFunct ge.genv_genv (.Vptr cosBlock CC.Integers.Ptrofs.zero) =
      some (.Internal polynomialFunction)) :
    LibraryCallbackContract ge m ptr (.Internal f_testfun) (testfun_f Polynomial.cosine) := by
  refine ⟨hcallback, rfl, ?_⟩
  intro x k hk
  simpa only [callCont_eq_self hk] using
    polynomial_callback_execution_in_context ge m cosBlock hsymbol hfunction x k

/-- In `polynomialLibrary`, calling the original `f_testfun` on `Vfloat x` returns
`Vfloat (testfun_f Polynomial.cosine x)` silently with memory unchanged, for every binary64 `x`. -/
theorem polynomial_callback_execution [CC.ExternalCalls] (x : Value) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 (callbackLibrary (.Internal f_testfun)).globalenv)
      (.Callstate (.Internal f_testfun) [.Vfloat x] k initialMemory)
      (.Returnstate (.Vfloat (testfun_f Polynomial.cosine x)) (CC.callCont k) initialMemory) :=
  polynomial_callback_execution_in_context _ initialMemory (CC.Positive.ofNat 8)
    (by rfl) (by rfl) x k

/-- The original callback `f_testfun` satisfies `CallbackContract` with
`f = testfun_f Polynomial.cosine`. -/
theorem polynomial_callback_contract [CC.ExternalCalls] :
    CallbackContract (.Internal f_testfun) (testfun_f Polynomial.cosine) := by
  refine ⟨rfl, ?_⟩
  intro x k hk
  simpa only [callCont_eq_self hk] using polynomial_callback_execution x k

/-- The (weight, node) pairs of the stored `n`-node rule: table entries `n(n-1)/2` through
`n(n-1)/2 + n - 1` of `weightBits` and `nodeBits`, decoded with `Model.ofNatBits`. -/
def storedTerms (n : Nat) : List (Value × Value) :=
  (((ClightTableData.weightBits.zip ClightTableData.nodeBits).drop (n * (n - 1) / 2)).take
    n).map fun term => (Model.ofNatBits term.1, Model.ofNatBits term.2)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
-- Evaluate the slice of the 55-entry tables for each `n ≤ 10` and count it.
/-- For `n ≤ 10`, `storedTerms n` has exactly `n` pairs. -/
theorem stored_terms_length (n : Nat) (hn : n ≤ 10) :
    (storedTerms n).length = n := by
  interval_cases n <;> rfl

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
-- Read the 110 table cells of the ten rules from the initialized memory and compare them.
/-- For `n ≤ 10`, `initialMemory` holds the cells of `storedTerms n` in the node block 1 and the
weight block 2 at their C offsets. -/
theorem stored_table_cells (n : Nat) (hn : n ≤ 10) :
    TableCells initialMemory (CC.Positive.ofNat 1) (CC.Positive.ofNat 2)
      n 0 (storedTerms n) := by
  interval_cases n <;>
    dsimp [storedTerms, ClightTableData.weightBits, ClightTableData.nodeBits,
      List.zip, List.drop, List.take, List.map, TableCells] <;>
    (repeat' constructor)

/-- The initialized `callbackLibrary fd` satisfies `StoredLibraryContext` for `storedTerms n`,
with the tables at blocks 1 and 2 and the accessors at blocks 3 and 4. -/
def storedContext (fd : CC.FunDef) (n : Nat) (hn : n ≤ 10) :
    StoredLibraryContext (callbackLibrary fd).globalenv initialMemory (storedTerms n) where
  nodes := CC.Positive.ofNat 1
  weights := CC.Positive.ofNat 2
  point := CC.Positive.ofNat 3
  weight := CC.Positive.ofNat 4
  nodes_symbol := by rfl
  weights_symbol := by rfl
  point_symbol := by rfl
  weight_symbol := by rfl
  point_function := by rfl
  weight_function := by rfl
  count_bound := by rw [stored_terms_length n hn]; exact hn
  cells := by rw [stored_terms_length n hn]; exact stored_table_cells n hn

/-- Given `CallbackContract fd f`, the call of `integrate` with `n ≤ 10` nodes in
`callbackLibrary fd` runs silently to
`Returnstate (Vfloat (integrate_model_f f (storedTerms n)))` with `initialMemory` unchanged. -/
theorem stored_callback_execution [CC.ExternalCalls] (fd : CC.FunDef) (f : Value → Value)
    (contract : CallbackContract fd f) (n : Nat) (hn : n ≤ 10) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 (callbackLibrary fd).globalenv)
      (storedLibraryCall (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) n k initialMemory)
      (.Returnstate (.Vfloat (integrate_model_f f (storedTerms n))) (CC.callCont k)
        initialMemory) := by
  simpa only [stored_terms_length n hn] using
    stored_library_execution _ initialMemory (storedTerms n) (storedContext fd n hn) fd f
      (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) contract.library_contract k

/-- With deterministic external calls, every finished run of the `n`-node call in
`callbackLibrary fd` ends in the stated return state. -/
theorem stored_callback_return_state [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls]
    (fd : CC.FunDef) (f : Value → Value) (contract : CallbackContract fd f)
    (n : Nat) (hn : n ≤ 10) (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 (callbackLibrary fd).globalenv)
      (storedLibraryCall (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) n .Kstop initialMemory)
      trace (.Returnstate value .Kstop memory)) :
    CC.State.Returnstate value .Kstop memory =
      .Returnstate (.Vfloat (integrate_model_f f (storedTerms n))) .Kstop initialMemory :=
  stored_library_return_state (callbackLibrary fd) initialMemory (storedTerms n)
    (storedContext fd n hn) fd f
    (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) contract.library_contract
    value memory trace (by simpa only [stored_terms_length n hn] using h)

/-- In `polynomialLibrary`, the `n`-node call with the original callback runs silently to
`Returnstate (Vfloat (integrate_model_f (testfun_f Polynomial.cosine) (storedTerms n)))`, for
`n ≤ 10`, with no assumption on a cosine implementation. -/
theorem stored_polynomial_execution [CC.ExternalCalls]
    (n : Nat) (hn : n ≤ 10) (k : CC.Cont) :
    CC.StarE0 (CC.Step2 polynomialLibrary.globalenv)
      (storedLibraryCall (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) n k initialMemory)
      (.Returnstate (.Vfloat (integrate_model_f (testfun_f Polynomial.cosine) (storedTerms n)))
        (CC.callCont k) initialMemory) :=
  stored_callback_execution (.Internal f_testfun) (testfun_f Polynomial.cosine)
    polynomial_callback_contract n hn k

/-- Every value returned by the `n`-node polynomial call is
`Vfloat (integrate_model_f (testfun_f Polynomial.cosine) (storedTerms n))` bit for bit. -/
theorem stored_polynomial_return_eq [calls : CC.ExternalCalls]
    [CC.ExternalCallsDeterministic calls]
    (n : Nat) (hn : n ≤ 10) (value : CC.Val) (memory : CC.Mem) (trace : CC.Trace)
    (h : CC.Star (CC.Step2 polynomialLibrary.globalenv)
      (storedLibraryCall (.Vptr testfunBlock (CC.Integers.Ptrofs.repr 0)) n .Kstop initialMemory)
      trace (.Returnstate value .Kstop memory)) :
    value = .Vfloat (integrate_model_f (testfun_f Polynomial.cosine) (storedTerms n)) :=
  (CC.State.Returnstate.inj
    (stored_callback_return_state (.Internal f_testfun) (testfun_f Polynomial.cosine)
      polynomial_callback_contract n hn value memory trace h)).1

end Quadrature.Binary64.Clight
