/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Quadrature.CSource.Library.Initialization
import Quadrature.CSource.Wrapper.Total
import Quadrature.Clight.StoredAccuracy

/-!
# Total correctness and accuracy of the initialized C library

`parsed_wrapper_total_accuracy` starts from the text of the original C program and of `cosine.c`.
It shows that every execution of the original two-point wrapper, in every C evaluation order,
terminates with the binary64 value of bits `0x3fead02c771c35ed`, which is finite and within
`0.00356` of the integral. `integral_total_accuracy` gives the same guarantee for the integrator
at each of the ten stored orders, with that order's error bound. No callback, table or cosine
premise remains.

## Main results

* `integrate_call_correct`, `wrapper_call_correct`: from the initial memory, every execution of
  a call of the integrator with `n ≤ 10` nodes, or of the wrapper, returns
  `Clight.StoredPolynomial.result n` (with `n = 2` for the wrapper) and preserves the caller's
  memory.
* `initialized_integrate_correct`, `initialized_wrapper_correct`: the same for the functions
  found by initialization and symbol lookup.
* `integral_total_accuracy`, `parsed_wrapper_total_accuracy`: in addition, the returned values
  are finite and within the proved error bounds.

## How it works

The chain has four links. The frontend reads the two source files and elaborates the five
one-dimensional functions and the cosine, and `from_sources` identifies the result with
`polynomialLibrary`. Initialization allocates the eight globals and writes both tables, whose
entries are the source decimals rounded once (`Quadrature.CSource.Tables.Literals`); this
discharges the symbol and table premises. Each function is then proved totally correct in the
small-step machine: the accessors, the callback with its nested call of the cosine, the
integrator by induction on the remaining table cells, and the wrapper. Most of the work goes into
totality. C leaves the order of operands unspecified, so at every state the proofs handle each
step the machine permits, and they show that every nested call preserves its caller's memory
(`CallMemory`). Last, the returned value is `Clight.StoredPolynomial.result n`, and
`Clight.StoredPolynomial.integral_accuracy` bounds it: we compute its bits by kernel evaluation,
decode them exactly and compare with an enclosure of `sin 1`, the exact integral.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`src/quadrules.c`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/src/quadrules.c):
  `gauss_point`, `gauss_weight`, `integrate`, `testfun` and `integrate_testfun`.
-/

namespace Quadrature.CSource.C.Library

open CC

variable [ExternalCalls]

/-- Initialization and symbol lookup select a function whose every C execution returns `value`
and preserves the memory established by initialization. -/
def InitializedCallCorrect (library : C.Library) (name : Ident)
    (args : List Val) (value : Val) : Prop :=
  ∃ memory block function,
    library.initMem = some memory ∧
    Genv.findSymbol library.globalEnv.globals name = some block ∧
    Genv.findFunct library.globalEnv.globals (.Vptr block Integers.Ptrofs.zero) = some function ∧
    SmallStep.CallCorrect library.globalEnv memory function args value

end Quadrature.CSource.C.Library

namespace Quadrature.CSource.Library

open CC Binary64 Binary64.ClightSource FloatLib.Floats.Formats.BinaryInterchange
open C.SmallStep

variable [ExternalCalls]

/-- The initialized callback uses the internal C cosine and terminates in every operand order. -/
theorem callback_correct :
    C.CallbackCorrect globalEnv (.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero)
      (.Internal Typed.testfun) (testfun_f Polynomial.cosine) :=
  C.polynomial_callback_correct globalEnv _ _ (wrapperFunctions _).callback_function
    (cosine_symbol _) (cosine_function _)

/-- Every call of the initialized integrator returns its stored binary64 result.
The empty rule returns positive zero, and orders one to ten use the initialized tables. -/
theorem integrate_call_correct (n : Nat) (hn : n ≤ 10) :
    CallCorrect globalEnv initialMemory (.Internal Typed.integrate)
      [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
      (.Vfloat (Clight.StoredPolynomial.result n)) := by
  have hnodes : (tableFunctions (.Internal Cosine.function)).nodes < initialMemory.nextblock := by
    rw [initial_nextblock]
    decide
  have hweights :
      (tableFunctions (.Internal Cosine.function)).weights < initialMemory.nextblock := by
    rw [initial_nextblock]
    decide
  have cells : Clight.TableCells initialMemory
      (tableFunctions (.Internal Cosine.function)).nodes
      (tableFunctions (.Internal Cosine.function)).weights
      (Clight.storedTerms n).length 0 (Clight.storedTerms n) := by
    rw [Clight.stored_terms_length n hn]
    exact table_cells (.Internal Cosine.function) n hn
  simpa only [Clight.stored_terms_length n hn, Clight.StoredPolynomial.result] using
    C.integrator_call_correct globalEnv initialMemory (tableFunctions (.Internal Cosine.function))
      (Positive.ofNat 6) (.Internal Typed.testfun) (testfun_f Polynomial.cosine)
      (Clight.storedTerms n) (by rw [Clight.stored_terms_length n hn]; exact hn)
      hnodes hweights callback_correct cells

/-- Every initialized two-point wrapper call returns its certified binary64 result. -/
theorem wrapper_call_correct :
    CallCorrect globalEnv initialMemory (.Internal Typed.integrateTestfun) []
      (.Vfloat (Clight.StoredPolynomial.result 2)) :=
  C.wrapper_call_correct globalEnv initialMemory (tableFunctions (.Internal Cosine.function))
    (wrapperFunctions (.Internal Cosine.function)) (testfun_f Polynomial.cosine) callback_correct
    (table_cells (.Internal Cosine.function) 2 (by decide))

/-- Initialization and lookup discharge every premise of the complete integrator call proof. -/
theorem initialized_integrate_correct (n : Nat) (hn : n ≤ 10) :
    polynomialLibrary.InitializedCallCorrect _integrate
      [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
      (.Vfloat (Clight.StoredPolynomial.result n)) :=
  ⟨initialMemory, Positive.ofNat 5, .Internal Typed.integrate,
    initialized _, rfl, (wrapperFunctions _).integrator_function, integrate_call_correct n hn⟩

/-- Initialization and lookup discharge every premise of the complete wrapper call proof. -/
theorem initialized_wrapper_correct :
    polynomialLibrary.InitializedCallCorrect _integrate_testfun []
      (.Vfloat (Clight.StoredPolynomial.result 2)) :=
  ⟨initialMemory, Positive.ofNat 7, .Internal Typed.integrateTestfun,
    initialized _, rfl, wrapper_function _, wrapper_call_correct⟩

/-- All ten initialized C integrator calls terminate correctly in every evaluation order.
Their returned binary64 values are finite and satisfy the certified integral-error bounds. -/
theorem integral_total_accuracy (n : Nat) (hlo : 1 ≤ n) (hhi : n ≤ 10) :
    polynomialLibrary.InitializedCallCorrect _integrate
      [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
      (.Vfloat (Clight.StoredPolynomial.result n)) ∧
    Model.isFinite (Clight.StoredPolynomial.result n) = true ∧
    |Model.toReal (Clight.StoredPolynomial.result n) -
      ∫ x in (-1 : ℝ)..1, Example.testfun_r x| ≤ Clight.StoredPolynomial.errorBound n :=
  ⟨initialized_integrate_correct n hhi, Clight.StoredPolynomial.integral_accuracy n hlo hhi⟩

/-- The parsed and initialized original wrapper, with the shipped C polynomial, returns
finite bits `0x3fead02c771c35ed` within `0.00356` of the real integral in every C evaluation
order. All calls terminate, and no cosine or table contract remains as a hypothesis. -/
theorem parsed_wrapper_total_accuracy :
    ∃ library value,
      fromSources CSourceData.source Cosine.source = some library ∧
      library.InitializedCallCorrect _integrate_testfun [] (.Vfloat value) ∧
      value = Model.ofNatBits 0x3fead02c771c35ed ∧
      Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.testfun_r x| ≤
        (356 : ℝ) / 100000 :=
  ⟨polynomialLibrary, Clight.StoredPolynomial.result 2, from_sources,
    initialized_wrapper_correct,
    Clight.StoredPolynomial.result_value 2 (by decide) (by decide),
    Clight.StoredPolynomial.integral_accuracy 2 (by decide) (by decide)⟩

end Quadrature.CSource.Library
