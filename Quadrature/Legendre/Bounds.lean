/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Quadrature.Legendre.Rules

/-!
# Bounds on functions and derivatives

This module restates simple_cfem's `proof/quadrature2.v`. Its accuracy theorems state their
hypotheses with two predicates on an interval `[lo, hi]`: `fbound` bounds a function and
`deriv_bound` its derivative. A derivative
bound gives a Lipschitz bound through the mean value theorem, `g_max_deriv`. The nodes and
weights of the Gauss–Legendre rules with fewer than five nodes are `gauss_pt` and `gauss_wt`.

## Main definitions

* `fbound lo hi g fb`: `|g| ≤ fb` on `[lo, hi]`.
* `deriv_bound lo hi f b`: `f` is differentiable on `[lo, hi]` with `|f'| ≤ b` there.
* `gauss_pt n i`, `gauss_wt n i`: the `i`-th node and weight of
  `Legendre.Gauss_Legendre_quadrature n`.

## Main results

* `g_max_deriv`, `g_max_deriv_specialized`: a derivative bound is a Lipschitz bound.
* `gauss_pt_range`, `gauss_wt_range`: the nodes lie in `[-1, 1]` and the weights in `[0, 2]`.

## Implementation notes

Compared with `quadrature2.v`: there `g_max_deriv` reduces to the case `y > 0` by reflection, and T.
Saikawa proved that case, `g_max_deriv_oneway`, with the mean value theorem. Mathlib's mean value
inequality on a convex set covers both signs of `y` at once, so we need no case split. The Rocq
proofs of `gauss_pt_range` and `gauss_wt_range` check each of the ten values with the `interval`
tactic. Ours read the node ranges off the record of the roots. A weight is positive by
`gauss_weight_positive` and at most the integral of `1` over `[-1, 1]`, which is `2`, by
`gauss_weight_leq_1`.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/quadrature2.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/quadrature2.v):
  `fbound`, `deriv_bound`, `g_max_deriv`, `g_max_deriv_specialized`, `gauss_pt`, `gauss_wt` and
  their range lemmas.
* É. Martin-Dorel and G. Melquiond, *Proving tight bounds on univariate expressions with
  elementary functions in Coq*, J. Automat. Reason. 57 (2016), no. 3, 187–217,
  [doi:10.1007/s10817-015-9350-4](https://doi.org/10.1007/s10817-015-9350-4).
-/

namespace Quadrature

open Polynomial

noncomputable section

/-- `|g x| ≤ fb` for every `x ∈ [lo, hi]`. -/
def fbound (lo hi : ℝ) (g : ℝ → ℝ) (fb : ℝ) : Prop := ∀ x ∈ Set.Icc lo hi, |g x| ≤ fb

/-- `f` is differentiable at every `x ∈ [lo, hi]`, with `|f' x| ≤ b`. -/
def deriv_bound (lo hi : ℝ) (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ x ∈ Set.Icc lo hi, DifferentiableAt ℝ f x ∧ |deriv f x| ≤ b

/-- If `|g'| ≤ d` on `[lo, hi]`, then `|g (x + y) - g x| ≤ |y d|` whenever `x` and `x + y` lie in
`[lo, hi]`. -/
theorem g_max_deriv (lo hi d : ℝ) (g : ℝ → ℝ) (x y : ℝ) (hd : deriv_bound lo hi g d)
    (hx : x ∈ Set.Icc lo hi) (hy : x + y ∈ Set.Icc lo hi) : |g (x + y) - g x| ≤ |y * d| := by
  have h := (convex_Icc lo hi).norm_image_sub_le_of_norm_deriv_le (fun z hz => (hd z hz).1)
    (fun z hz => by rw [Real.norm_eq_abs]; exact (hd z hz).2) hx hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs, add_sub_cancel_left] at h
  calc |g (x + y) - g x| ≤ d * |y| := h
    _ ≤ |d| * |y| := mul_le_mul_of_nonneg_right (le_abs_self d) (abs_nonneg y)
    _ = |y * d| := by rw [abs_mul, mul_comm]

/-- `g_max_deriv` on `[-1, 1]`, with the bound written `|y| d`. -/
theorem g_max_deriv_specialized (d : ℝ) (g : ℝ → ℝ) (x y : ℝ)
    (hd : deriv_bound Legendre.lo Legendre.hi g d)
    (hx : x ∈ Set.Icc Legendre.lo Legendre.hi) (hy : x + y ∈ Set.Icc Legendre.lo Legendre.hi) :
    |g (x + y) - g x| ≤ |y| * d := by
  have hd₀ : 0 ≤ d := (abs_nonneg _).trans (hd x hx).2
  calc |g (x + y) - g x| ≤ |y * d| := g_max_deriv Legendre.lo Legendre.hi d g x y hd hx hy
    _ = |y| * d := by rw [abs_mul, abs_of_nonneg hd₀]

/-- The `i`-th root of `legendre n` in increasing order, for `n < 5`. -/
def gauss_pt (n : Fin 5) (i : Fin n) : ℝ :=
  (Legendre.some_legendre_roots n).LR_roots.ROOTS_vals i

/-- Every node lies in `[-1, 1]`. -/
theorem gauss_pt_range (n : Fin 5) (i : Fin n) : gauss_pt n i ∈ Set.Icc (-1 : ℝ) 1 :=
  (Legendre.some_legendre_roots n).LR_roots.ROOTS_inrange i

/-- The `i`-th weight of `Legendre.Gauss_Legendre_quadrature n`. -/
def gauss_wt (n : Fin 5) (i : Fin n) : ℝ := (Legendre.some_gauss_weights n).GW_vals i

/-- Every weight lies in `[0, 2]`. -/
theorem gauss_wt_range (n : Fin 5) (i : Fin n) : gauss_wt n i ∈ Set.Icc (0 : ℝ) 2 := by
  have hmass : Legendre.intgal (fun x => (1 : ℝ[X]).eval x) = 2 := by
    rw [Legendre.intgal_eq_integral]
    norm_num
  rw [gauss_wt, ← (Legendre.some_gauss_weights n).GW_good i]
  constructor
  · exact (gauss_weight_positive Legendre.lo_lt_hi Legendre.w_positive Legendre.wcontinuous
      (Legendre.some_gauss_weights n).GW_legendre.LR_roots i).le
  · exact (gauss_weight_leq_1 Legendre.lo_lt_hi Legendre.w_positive Legendre.wcontinuous
      (Legendre.some_gauss_weights n).GW_legendre.LR_roots i).trans_eq hmass

end

end Quadrature
