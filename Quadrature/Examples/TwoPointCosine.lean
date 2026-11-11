/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import CAS.IntegrationTactic
import FloatLib.Numerics.Automation.Interval
import Quadrature.Legendre.Rules

/-!
# The cosine example: exact errors of the one- and two-point rules

This module restates the error bounds of the cosine example in simple_cfem's
`proof/quadrature2.v`. For `testfun_r x = (1 - x) cos x / 2` on `[-1, 1]` the integral is
`sin 1 ≈ 0.84147`. The
one-point rule gives `1` and the two-point rule `cos (1/√3) ≈ 0.83791`, so their errors are
about `0.1585` and `0.00356`. We prove the upper bounds `0.159` and `0.00356`, and that the
two-point error is not bounded by any multiple of a bound on the sixth derivative: the remainder
of the two-node rule involves the fourth.

## Main results

* `error_1_0_1'`: the one-point error is at most `0.159`, the bound of the Rocq lemma of that
  name.
* `two_point_bound`: the two-point error is at most `0.00356`.
* `sixth_derivative_bound_impossible`: `x ^ 4` has two-point error `8/45` while its sixth
  derivative vanishes.

## How it works

We compute both sides exactly instead of bounding a derivative. The odd part `-x cos x / 2` of
`testfun_r` integrates to zero and cancels in both symmetric rules, so the integral is `sin 1`
(by SymLean's `cas` tactic) and the two-point rule gives `cos (1/√3)`. FloatLib's `interval`
tactic proves rational bounds on `sin 1` and `cos (1/√3)`, to seven digits where the bound
`0.00356` needs them, and `linarith` combines them. For the sixth derivative `x ^ 4` suffices:
two nodes integrate cubics exactly but not quartics.

## Implementation notes

These are statements about the exact real rules. Rounding is handled in
`Quadrature.Rules.Accuracy`, and the C programs in the `Quadrature.CSource` and
`Quadrature.Clight` modules.

Compared with `quadrature2.v`: we prove the one-point bound `159/1000` of `error_1_0_1'`, and
for two points the bound `356/100000`, which the comment at `error_1_0_2` gives as the true bound;
`error_1_0_2` proves `424/100000` through `quadrature_error_bound`.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/quadrature2.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/quadrature2.v):
  `error_1_0_1'` and `error_1_0_2`.
-/

open MeasureTheory

namespace Quadrature.Example

noncomputable section

/-- The integrand of the cosine example, `(1 - x) cos x / 2`. -/
def testfun_r (x : ℝ) : ℝ := (1 / 2) * (1 - x) * Real.cos x

/-- `∫_{-1}^1 testfun_r = sin 1`. The odd part `-x cos x / 2` integrates to zero, leaving
`∫_{-1}^1 cos x / 2`. -/
theorem integral_eq :
    (∫ x in (-1 : ℝ)..1, testfun_r x) = Real.sin 1 := by
  unfold testfun_r
  cas

/-- The one-point rule on `[-1, 1]` gives `2 * testfun_r 0 = 1`. -/
theorem one_point_eq : 2 * testfun_r 0 = 1 := by
  norm_num [testfun_r]

/-- The two-point rule gives `cos (1/√3)`, the odd part cancelling by symmetry. -/
theorem two_point_eq :
    testfun_r (-(1 / Real.sqrt 3)) + testfun_r (1 / Real.sqrt 3) =
      Real.cos (1 / Real.sqrt 3) := by
  simp only [testfun_r, Real.cos_neg]
  ring

private theorem gauss_node_sq : (1 / Real.sqrt (3 : ℝ)) ^ 2 = 1 / 3 := by
  rw [div_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- `0.8414 ≤ sin 1`, a rational lower bound by interval enclosure. -/
theorem sin_one_lower : (8414 / 10000 : ℝ) ≤ Real.sin 1 := by
  interval

/-- `cos (1/√3) ≤ 0.838`, certified by rational interval enclosure. -/
theorem cos_node_upper : Real.cos (1 / Real.sqrt 3) ≤ (838 / 1000 : ℝ) := by
  interval

/-- `sin 1 ≤ 0.8414711`, certified by rational interval enclosure. -/
theorem sin_one_upper : Real.sin 1 ≤ (8414711 / 10000000 : ℝ) := by
  interval

/-- The error of the one-point rule on `testfun_r` is at most `0.159`. -/
theorem error_1_0_1' :
    |Legendre.intgal testfun_r - Legendre.Gauss_Legendre_quadrature 1 testfun_r| ≤
      (159 / 1000 : ℝ) := by
  rw [Legendre.intgal_eq_integral, Legendre.Gauss_Legendre_quadrature_one, integral_eq,
    one_point_eq, abs_le]
  constructor
  · linarith [sin_one_lower]
  · linarith [sin_one_upper]

/-- `0.8379115 ≤ cos (1/√3)`, certified by rational interval enclosure. -/
theorem cos_node_lower : (8379115 / 10000000 : ℝ) ≤ Real.cos (1 / Real.sqrt 3) := by
  interval

/-- The two-point error is at most `0.00356`. Both `sin 1` and `cos (1/√3)` are enclosed to
about seven digits. -/
theorem two_point_bound :
    |(∫ x in (-1 : ℝ)..1, testfun_r x) -
      (testfun_r (-(1 / Real.sqrt 3)) + testfun_r (1 / Real.sqrt 3))| ≤
      (356 / 100000 : ℝ) := by
  rw [integral_eq, two_point_eq, abs_of_nonneg]
  · linarith [sin_one_upper, cos_node_lower]
  · linarith [sin_one_lower, cos_node_upper]

/-- The two-point rule has error exactly `8/45` on `x ^ 4`: the integral is `2/5` and the
rule gives `2/9`. -/
theorem quartic_two_point_error :
    (∫ x in (-1 : ℝ)..1, x ^ 4) -
      ((-(1 / Real.sqrt 3)) ^ 4 + (1 / Real.sqrt 3) ^ 4) = (8 / 45 : ℝ) := by
  have hi : (∫ x in (-1 : ℝ)..1, x ^ 4) = 2 / 5 := by cas
  rw [hi]
  calc
    _ = 2 / 5 - 2 * ((1 / Real.sqrt (3 : ℝ)) ^ 2) ^ 2 := by ring
    _ = 8 / 45 := by rw [gauss_node_sq]; norm_num

/-- The sixth derivative of `x ^ 4` is identically zero. -/
theorem quartic_sixth_derivative (x : ℝ) :
    iteratedDeriv 6 (fun y : ℝ => y ^ 4) x = 0 := by
  simp [iteratedDeriv_pow, Nat.descFactorial]

/-- No constant `C` bounds the two-point error by `C * M` whenever `M` bounds the absolute
sixth derivative on `[-1, 1]`. The quartic `x ^ 4` has sixth derivative bounded by `M = 0`
and error `8/45`. -/
theorem sixth_derivative_bound_impossible (C : ℝ) :
    ¬ (∀ (f : ℝ → ℝ) (M : ℝ), ContDiff ℝ 6 f → 0 ≤ M →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv 6 f x| ≤ M) →
      |(∫ x in (-1 : ℝ)..1, f x) -
        (f (-(1 / Real.sqrt 3)) + f (1 / Real.sqrt 3))| ≤ C * M) := by
  intro h
  have hq := h (fun x => x ^ 4) 0 (by fun_prop) le_rfl
    (fun x _ => by simp only [quartic_sixth_derivative, abs_zero, le_refl])
  rw [quartic_two_point_error, mul_zero] at hq
  norm_num at hq

end

end Quadrature.Example
