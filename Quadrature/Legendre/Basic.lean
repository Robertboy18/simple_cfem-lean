/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import CAS.Continuum.Quadrature.Legendre.Polynomials
import Quadrature.Gaussian.Rule

/-!
# Gauss–Legendre quadrature on `[-1, 1]`

This module restates the beginning of the module `Legendre` of simple_cfem's
`proof/quadrature.v`, Stewart's paragraph 21: the Gaussian theory for the constant weight on
`[-1, 1]`, whose orthogonal polynomials are the monic Legendre polynomials `legendre n`. A rule is
packaged as the record `legendre_roots n` of the roots and the record `gauss_weights n` of their
weights, and `compute_G` applies it; the names are the Rocq ones. The polynomials of degree at
most four come from SymLean, our verified computer algebra system, through
`legendre_eq_monicPolynomial`.

## Main definitions

* `lo`, `hi`, `w`: the interval `[-1, 1]` and the constant weight `1`.
* `legendre n`: the monic Legendre polynomial `ortho_p lo hi w n`.
* `intgal f`: the integral of `f` over `[-1, 1]`.
* `legendre_roots n`, with fields `LR_poly`, `LR_poly_eq`, `LR_roots`; `gauss_weights n`, with
  fields `GW_legendre`, `GW_vals`, `GW_good`; and `compute_G`.

## Main results

* `compute_G_eq`: `compute_G` is the rule `G` on the recorded roots.
* `legendre_quadrature_error`: the error formula for these rules.
* `Legendre_poly_0`, ..., `Legendre_poly_4` and their evaluated forms `Legendre_poly_0'`, ...,
  `Legendre_poly_4'`.

## Implementation notes

Compared with `quadrature.v`: we prove `legendre_quadrature_error` with the square of
`legendre n`, as in our `quadrature_error`, for `0 < n` and `f` with `2n` continuous derivatives;
the Rocq statement instantiates the Rocq `quadrature_error` and squares `legendre (n + 1)`.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/quadrature.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/quadrature.v),
  module `Legendre`: `legendre`, `legendre_roots`, `gauss_weights`, `compute_G` and the lemmas
  `Legendre_poly_0` to `Legendre_poly_4'`.
-/

namespace Quadrature.Legendre

open Polynomial MeasureTheory

noncomputable section

/-- The left endpoint `-1`. -/
def lo : ℝ := -1

/-- The right endpoint `1`. -/
def hi : ℝ := 1

/-- The left endpoint is below the right one. -/
theorem lo_lt_hi : lo < hi := by norm_num [lo, hi]

/-- The Legendre weight, constant `1`. -/
def w : ℝ → ℝ := fun _ => 1

/-- The Legendre weight is positive on `[lo, hi]`. -/
theorem w_positive : ∀ x ∈ Set.Icc lo hi, 0 < w x := fun _ _ => one_pos

/-- The Legendre weight is continuous on `[lo, hi]`. -/
theorem wcontinuous : ContinuousOn w (Set.Icc lo hi) := continuousOn_const

/-- Stewart's paragraph 21: the monic Legendre polynomial of degree `n`, the orthogonal
polynomial of the constant weight on `[-1, 1]`. -/
def legendre (n : ℕ) : ℝ[X] := ortho_p lo hi w n

/-- The integral of `f` against the Legendre weight over `[lo, hi]`. -/
def intgal (f : ℝ → ℝ) : ℝ := Quadrature.intgal lo hi w f

/-- `intgal f` is the integral of `f` over `[lo, hi]`. -/
theorem intgal_eq (f : ℝ → ℝ) : intgal f = ∫ x in Set.Icc lo hi, f x := by
  simp only [intgal, Quadrature.intgal, w, mul_one]

/-- `intgal f` is the interval integral of `f` from `-1` to `1`. -/
theorem intgal_eq_integral (f : ℝ → ℝ) : intgal f = ∫ x in (-1 : ℝ)..1, f x := by
  rw [intgal, Quadrature.intgal_eq_integral lo_lt_hi.le]
  simp only [w, mul_one, lo, hi]

/-- A Legendre polynomial `LR_poly` equal to `legendre n`, together with its roots. -/
structure legendre_roots (n : ℕ) where
  /-- The polynomial. -/
  LR_poly : ℝ[X]
  /-- It is `legendre n`. -/
  LR_poly_eq : legendre n = LR_poly
  /-- Its roots in increasing order. -/
  LR_roots : roots_of_ortho_p lo hi w n

/-- The roots of `legendre n` together with the values `GW_vals` of their Gauss weights. -/
structure gauss_weights (n : ℕ) where
  /-- The roots. -/
  GW_legendre : legendre_roots n
  /-- The weights. -/
  GW_vals : Fin n → ℝ
  /-- Each value is the Gauss weight at the corresponding root. -/
  GW_good : ∀ i, gauss_weight GW_legendre.LR_roots i = GW_vals i

/-- The rule of `GW` applied to `f`, computed from the recorded weights. -/
def compute_G {n : ℕ} (GW : gauss_weights n) (f : ℝ → ℝ) : ℝ :=
  ∑ i, GW.GW_vals i * f (GW.GW_legendre.LR_roots.ROOTS_vals i)

/-- `compute_G` is the Gaussian rule `G` on the recorded roots. -/
theorem compute_G_eq {n : ℕ} (GW : gauss_weights n) (f : ℝ → ℝ) :
    compute_G GW f = G GW.GW_legendre.LR_roots f := by
  simp only [compute_G, G, GW.GW_good]

/-- For `0 < n` and `f` that is `2n` times continuously differentiable, the error of `GW` on `f`
is `f^(2n)(ξ) / (2n)!` times the integral of `(legendre n)^2` for some `ξ ∈ [lo, hi]`. -/
theorem legendre_quadrature_error {n : ℕ} (GW : gauss_weights n) (f : ℝ → ℝ) (hn : 0 < n)
    (hf : ContDiff ℝ (2 * n) f) :
    ∃ ξ ∈ Set.Icc lo hi, intgal f - compute_G GW f =
      iteratedDeriv (2 * n) f ξ / (2 * n).factorial *
        intgal (fun x => (legendre n).eval x ^ 2) := by
  rw [compute_G_eq]
  exact quadrature_error lo_lt_hi w_positive wcontinuous GW.GW_legendre.LR_roots f hn hf

/-- `legendre n` is SymLean's monic Legendre polynomial `monicPolynomial n`. -/
theorem legendre_eq_monicPolynomial (n : ℕ) :
    legendre n = CAS.Continuum.Legendre.monicPolynomial n :=
  ortho_p_eq_integralOrthogonalPolynomial lo_lt_hi w_positive continuousOn_const n

/-- The nodal polynomial of a Gaussian rule for the Legendre weight is `legendre n`. -/
theorem nodal_eq_legendre {n : ℕ} (rule : CAS.Continuum.Legendre.Rule n) :
    Lagrange.nodal Finset.univ rule.nodes = legendre n := by
  rw [legendre_eq_monicPolynomial]
  exact rule.nodal_eq_integralOrthogonalPolynomial (by norm_num) fun _ _ => one_pos

/-- The monic Legendre polynomial of degree zero is `1`. -/
theorem Legendre_poly_0 : legendre 0 = 1 := by
  rw [legendre_eq_monicPolynomial, CAS.Continuum.Legendre.monicPolynomial_zero]

/-- The monic Legendre polynomial of degree zero evaluates to `1`. -/
theorem Legendre_poly_0' : (fun x => (legendre 0).eval x) = fun _ => 1 := by
  simp only [Legendre_poly_0, eval_one]

/-- The monic Legendre polynomial of degree one is `X`. -/
theorem Legendre_poly_1 : legendre 1 = X := by
  rw [legendre_eq_monicPolynomial, CAS.Continuum.Legendre.monicPolynomial_one]

/-- The monic Legendre polynomial of degree one evaluates to `x`. -/
theorem Legendre_poly_1' : (fun x => (legendre 1).eval x) = fun x => x := by
  simp only [Legendre_poly_1, eval_X]

/-- The monic Legendre polynomial of degree two is `X * X - 1 / 3`. -/
theorem Legendre_poly_2 : legendre 2 = X * X - C (1 / 3) := by
  rw [legendre_eq_monicPolynomial, CAS.Continuum.Legendre.monicPolynomial_two]
  ring

/-- The monic Legendre polynomial of degree two evaluates to `x * x - 1 / 3`. -/
theorem Legendre_poly_2' : (fun x => (legendre 2).eval x) = fun x => x * x - 1 / 3 := by
  simp only [Legendre_poly_2, eval_sub, eval_mul, eval_X, eval_C]

/-- The monic Legendre polynomial of degree three is `X * X * X - (3 / 5) X`. -/
theorem Legendre_poly_3 : legendre 3 = X * X * X - C (3 / 5) * X := by
  rw [legendre_eq_monicPolynomial, CAS.Continuum.Legendre.monicPolynomial_three]
  ring

/-- The monic Legendre polynomial of degree three evaluates to `x * x * x - (3 / 5) x`. -/
theorem Legendre_poly_3' :
    (fun x => (legendre 3).eval x) = fun x => x * x * x - 3 / 5 * x := by
  simp only [Legendre_poly_3, eval_sub, eval_mul, eval_X, eval_C]

/-- The monic Legendre polynomial of degree four is
`X * X * X * X - (30 / 35) (X * X) + 3 / 35`. -/
theorem Legendre_poly_4 :
    legendre 4 = X * X * X * X - C (30 / 35) * (X * X) + C (3 / 35) := by
  rw [legendre_eq_monicPolynomial, CAS.Continuum.Legendre.monicPolynomial_four]
  ring

/-- The monic Legendre polynomial of degree four evaluates to
`x * x * x * x - (30 / 35) (x * x) + 3 / 35`. -/
theorem Legendre_poly_4' : (fun x => (legendre 4).eval x) =
    fun x => x * x * x * x - 30 / 35 * (x * x) + 3 / 35 := by
  simp only [Legendre_poly_4, eval_add, eval_sub, eval_mul, eval_X, eval_C]

end

end Quadrature.Legendre
