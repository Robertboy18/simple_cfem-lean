/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Quadrature.Legendre.Basic

/-!
# The Gauss–Legendre rules with one to four nodes

This module restates the rest of the module `Legendre` of simple_cfem's `proof/quadrature.v`,
from its sections on the Legendre polynomials of degree 0 to 4 to the specialization of the
quadrature error. The records `legendre_roots n` and `gauss_weights n` for `n ≤ 4` have the same
explicit roots and weights as in Rocq and are collected in `some_legendre_roots` and
`some_gauss_weights`, which define `Gauss_Legendre_quadrature n`. The Rocq proofs compute each
weight by integrating a Lagrange basis polynomial. We instead identify each record with an
explicit Gaussian rule of SymLean, our verified computer algebra system, and read the weights off
SymLean's interpolatory weights.

## Main definitions

* `legendre_roots_0`, ..., `legendre_roots_4`, with the four-point roots `legendre_roots_val`.
* `gauss_weights_0`, ..., `gauss_weights_4`.
* `some_legendre_roots`, `some_gauss_weights`, `Gauss_Legendre_quadrature`: the rules indexed
  by `Fin 5`.
* `quadrature_error_bound f n b`: a bound on the `2n`-th derivative of `f` that makes `b` an
  error bound.

## Main results

* `legendre_roots_4a`, `legendre_roots_4b`, `legendre_roots_4c`: the four-point roots are roots
  of `legendre 4`, increasing, and in `[lo, hi]`.
* `gauss_weight_1_0`, ..., `gauss_weight_4_3`: the explicit weights.
* `legendre_roots_unique`: there is only one record of the roots of `legendre n`.
* `legendre_quadrature_error'`, `quadrature_error_bound_is_bound`: the error of
  `Gauss_Legendre_quadrature n`.

## Implementation notes

Compared with `quadrature.v`: the Rocq four-point values `√((3 ± 2√(6/5)) / 7)` and
`1/2 ∓ √(5/6) / 6` are SymLean's `√((15 ± 2√30) / 35)` and `(18 ∓ √30) / 36` after
`√(6/5) = √30 / 5` and `√(5/6) = √30 / 6`. Rocq collects the records in a dependently typed list
read by `nth_iseq`; a dependent function on `Fin 5` does the same job, so `iseq` and `nth_iseq`
have no Lean counterpart. As in `legendre_quadrature_error`, we state `quadrature_error_bound`
with `legendre n`, where the Rocq definition has `legendre (n + 1)`, and prove
`quadrature_error_bound_is_bound` for `0 < n` and `2n` continuous derivatives.

`QUADRATURE-TODO.md` in `simple_cfem` gives two reasons for stopping at four nodes: degree two is
the highest that is useful in the intended finite element application, and up to degree four the
Legendre roots have closed forms built from square roots. The C tables go up to ten nodes, and
we certify orders five to ten without closed forms, by rational root brackets, in
`Quadrature.Rules.Certificates`.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/quadrature.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/quadrature.v),
  module `Legendre`: `legendre_roots_0` to `legendre_roots_4`, `gauss_weights_0` to
  `gauss_weights_4`, `Gauss_Legendre_quadrature` and `quadrature_error_bound_is_bound`.
* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/QUADRATURE-TODO.md`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/QUADRATURE-TODO.md),
  the item on `Module Legendre`.
-/

namespace Quadrature.Legendre

open Polynomial
open CAS.Continuum.Legendre (oneGaussian twoGaussian threeGaussian fourGaussian fourInner
  fourOuter fourRadical fourRadical_bounds fourRadical_sq fourNodes_ordered
  twoNode_eq_one_div_sqrt)

noncomputable section

/-- Each node of a Gaussian rule for the Legendre weight is a root of `legendre n`. -/
theorem isRoot_legendre {n : ℕ} (rule : CAS.Continuum.Legendre.Rule n) (i : Fin n) :
    (legendre n).IsRoot (rule.nodes i) := by
  rw [← nodal_eq_legendre rule]
  exact Lagrange.eval_nodal_at_node (Finset.mem_univ i)

/-- The nodes of a Gaussian rule for the Legendre weight, written as `v` and increasing, as a
record of the roots of `legendre n`. -/
private def rootsOfRule {n : ℕ} (rule : CAS.Continuum.Legendre.Rule n) (v : Fin n → ℝ)
    (hv : v = rule.nodes) (hsorted : StrictMono v) : roots_of_ortho_p lo hi w n where
  ROOTS_vals := v
  ROOTS_zero := by
    subst hv
    exact isRoot_legendre rule
  ROOTS_sorted := hsorted
  ROOTS_inrange := by
    subst hv
    exact fun i => Set.Ioo_subset_Icc_self (rule.interior i)

/-- If a record lists the nodes of a Gaussian rule for the Legendre weight, its Gauss weights
are the weights of the rule. -/
private theorem gauss_weight_eq_weights {n : ℕ} (roots : roots_of_ortho_p lo hi w n)
    (rule : CAS.Continuum.Legendre.Rule n) (h : roots.ROOTS_vals = rule.nodes) (i : Fin n) :
    gauss_weight roots i = rule.weights i := by
  rw [gauss_weight_eq_interpolatoryWeight (w := w) lo_lt_hi.le continuousOn_const roots i, h]
  exact (rule.weights_eq_interpolatoryWeight i.pos i).symm

private theorem sqrt_six_fifths : Real.sqrt (6 / 5) = fourRadical / 5 := by
  have hy : 0 ≤ fourRadical / 5 := div_nonneg fourRadical_bounds.1 (by norm_num)
  refine (Real.sqrt_eq_iff_mul_self_eq (by norm_num : (0 : ℝ) ≤ 6 / 5) hy).mpr ?_
  linear_combination (-1 / 25 : ℝ) * fourRadical_sq

private theorem sqrt_five_sixths : Real.sqrt (5 / 6) = fourRadical / 6 := by
  have hy : 0 ≤ fourRadical / 6 := div_nonneg fourRadical_bounds.1 (by norm_num)
  refine (Real.sqrt_eq_iff_mul_self_eq (by norm_num : (0 : ℝ) ≤ 5 / 6) hy).mpr ?_
  linear_combination (-1 / 36 : ℝ) * fourRadical_sq

/-- The record of the roots of `legendre 0`, which has none. -/
def legendre_roots_0 : legendre_roots 0 where
  LR_poly := 1
  LR_poly_eq := Legendre_poly_0
  LR_roots :=
    { ROOTS_vals := ![]
      ROOTS_zero := fun i => i.elim0
      ROOTS_sorted := by
        intro a
        exact a.elim0
      ROOTS_inrange := fun i => i.elim0 }

/-- The record of the root `0` of `legendre 1`. -/
def legendre_roots_1 : legendre_roots 1 where
  LR_poly := X
  LR_poly_eq := Legendre_poly_1
  LR_roots := rootsOfRule oneGaussian ![0] rfl strictMono_vecEmpty

private theorem two_nodes_eq : ![-1 / Real.sqrt 3, 1 / Real.sqrt 3] = twoGaussian.nodes := by
  change _ = ![-CAS.Continuum.Legendre.twoNode, CAS.Continuum.Legendre.twoNode]
  rw [twoNode_eq_one_div_sqrt, neg_div]

private theorem two_nodes_sorted : StrictMono ![-1 / Real.sqrt 3, 1 / Real.sqrt 3] := by
  have h : (0 : ℝ) < 1 / Real.sqrt 3 := by positivity
  refine strictMono_vecEmpty.vecCons ?_
  change -1 / Real.sqrt 3 < 1 / Real.sqrt 3
  rw [neg_div]
  linarith

/-- The record of the roots `±1 / √3` of `legendre 2`. -/
def legendre_roots_2 : legendre_roots 2 where
  LR_poly := X * X - C (1 / 3)
  LR_poly_eq := Legendre_poly_2
  LR_roots := rootsOfRule twoGaussian ![-1 / Real.sqrt 3, 1 / Real.sqrt 3] two_nodes_eq
    two_nodes_sorted

private theorem three_nodes_sorted :
    StrictMono ![-Real.sqrt (3 / 5), 0, Real.sqrt (3 / 5)] := by
  have h : 0 < Real.sqrt (3 / 5) := by positivity
  exact (strictMono_vecEmpty.vecCons h).vecCons (by linarith : -Real.sqrt (3 / 5) < 0)

/-- The record of the roots `-√(3/5)`, `0`, `√(3/5)` of `legendre 3`. -/
def legendre_roots_3 : legendre_roots 3 where
  LR_poly := X * X * X - C (3 / 5) * X
  LR_poly_eq := Legendre_poly_3
  LR_roots := rootsOfRule threeGaussian ![-Real.sqrt (3 / 5), 0, Real.sqrt (3 / 5)] rfl
    three_nodes_sorted

/-- The four roots `±√((3 ± 2√(6/5)) / 7)` of `legendre 4`, in increasing order. -/
def legendre_roots_val : Fin 4 → ℝ :=
  ![-Real.sqrt ((3 + 2 * Real.sqrt (6 / 5)) / 7), -Real.sqrt ((3 - 2 * Real.sqrt (6 / 5)) / 7),
    Real.sqrt ((3 - 2 * Real.sqrt (6 / 5)) / 7), Real.sqrt ((3 + 2 * Real.sqrt (6 / 5)) / 7)]

private theorem legendre_roots_val_eq : legendre_roots_val = fourGaussian.nodes := by
  have h₁ : (3 + 2 * Real.sqrt (6 / 5)) / 7 = (15 + 2 * fourRadical) / 35 := by
    rw [sqrt_six_fifths]
    ring
  have h₂ : (3 - 2 * Real.sqrt (6 / 5)) / 7 = (15 - 2 * fourRadical) / 35 := by
    rw [sqrt_six_fifths]
    ring
  rw [legendre_roots_val, h₁, h₂]
  rfl

/-- Each entry of `legendre_roots_val` is a root of `legendre 4`. -/
theorem legendre_roots_4a : ∀ i, (ortho_p lo hi w 4).IsRoot (legendre_roots_val i) := by
  rw [legendre_roots_val_eq]
  exact isRoot_legendre fourGaussian

/-- The entries of `legendre_roots_val` are strictly increasing. -/
theorem legendre_roots_4b : StrictMono legendre_roots_val := by
  rw [legendre_roots_val_eq]
  change StrictMono ![-fourOuter, -fourInner, fourInner, fourOuter]
  obtain ⟨h₁, h₂, -⟩ := fourNodes_ordered
  exact ((strictMono_vecEmpty.vecCons h₂).vecCons (by linarith : -fourInner < fourInner)).vecCons
    (by linarith : -fourOuter < -fourInner)

/-- Every entry of `legendre_roots_val` lies in `[lo, hi]`. -/
theorem legendre_roots_4c : ∀ i, legendre_roots_val i ∈ Set.Icc lo hi := by
  rw [legendre_roots_val_eq]
  exact fun i => Set.Ioo_subset_Icc_self (fourGaussian.interior i)

/-- The record of the roots `legendre_roots_val` of `legendre 4`. -/
def legendre_roots_4 : legendre_roots 4 where
  LR_poly := X * X * X * X - C (30 / 35) * (X * X) + C (3 / 35)
  LR_poly_eq := Legendre_poly_4
  LR_roots := ⟨legendre_roots_val, legendre_roots_4a, legendre_roots_4b, legendre_roots_4c⟩

/-- The record of the weights of the empty rule. -/
def gauss_weights_0 : gauss_weights 0 where
  GW_legendre := legendre_roots_0
  GW_vals := ![]
  GW_good i := i.elim0

/-- The one-point weight is `2`. -/
theorem gauss_weight_1_0 : gauss_weight legendre_roots_1.LR_roots 0 = 2 :=
  gauss_weight_eq_weights legendre_roots_1.LR_roots oneGaussian rfl 0

/-- The record of the one-point weight. -/
def gauss_weights_1 : gauss_weights 1 where
  GW_legendre := legendre_roots_1
  GW_vals := ![2]
  GW_good i := by
    fin_cases i
    exact gauss_weight_1_0

/-- The first two-point weight is `1`. -/
theorem gauss_weight_2_0 : gauss_weight legendre_roots_2.LR_roots 0 = 1 :=
  gauss_weight_eq_weights legendre_roots_2.LR_roots twoGaussian two_nodes_eq 0

/-- The second two-point weight is `1`. -/
theorem gauss_weight_2_1 : gauss_weight legendre_roots_2.LR_roots 1 = 1 :=
  gauss_weight_eq_weights legendre_roots_2.LR_roots twoGaussian two_nodes_eq 1

/-- The record of the two-point weights. -/
def gauss_weights_2 : gauss_weights 2 where
  GW_legendre := legendre_roots_2
  GW_vals := ![1, 1]
  GW_good i := by
    fin_cases i
    exacts [gauss_weight_2_0, gauss_weight_2_1]

/-- The first three-point weight is `5 / 9`. -/
theorem gauss_weight_3_0 : gauss_weight legendre_roots_3.LR_roots 0 = 5 / 9 :=
  gauss_weight_eq_weights legendre_roots_3.LR_roots threeGaussian rfl 0

/-- The middle three-point weight is `8 / 9`. -/
theorem gauss_weight_3_1 : gauss_weight legendre_roots_3.LR_roots 1 = 8 / 9 :=
  gauss_weight_eq_weights legendre_roots_3.LR_roots threeGaussian rfl 1

/-- The last three-point weight is `5 / 9`. -/
theorem gauss_weight_3_2 : gauss_weight legendre_roots_3.LR_roots 2 = 5 / 9 :=
  gauss_weight_eq_weights legendre_roots_3.LR_roots threeGaussian rfl 2

/-- The record of the three-point weights. -/
def gauss_weights_3 : gauss_weights 3 where
  GW_legendre := legendre_roots_3
  GW_vals := ![5 / 9, 8 / 9, 5 / 9]
  GW_good i := by
    fin_cases i
    exacts [gauss_weight_3_0, gauss_weight_3_1, gauss_weight_3_2]

/-- The first four-point weight is `1 / 2 - √(5/6) / 6`. -/
theorem gauss_weight_4_0 :
    gauss_weight legendre_roots_4.LR_roots 0 = 1 / 2 - Real.sqrt (5 / 6) / 6 := by
  rw [gauss_weight_eq_weights legendre_roots_4.LR_roots fourGaussian legendre_roots_val_eq 0,
    sqrt_five_sixths]
  change (18 - fourRadical) / 36 = _
  ring

/-- The second four-point weight is `1 / 2 + √(5/6) / 6`. -/
theorem gauss_weight_4_1 :
    gauss_weight legendre_roots_4.LR_roots 1 = 1 / 2 + Real.sqrt (5 / 6) / 6 := by
  rw [gauss_weight_eq_weights legendre_roots_4.LR_roots fourGaussian legendre_roots_val_eq 1,
    sqrt_five_sixths]
  change (18 + fourRadical) / 36 = _
  ring

/-- The third four-point weight is `1 / 2 + √(5/6) / 6`. -/
theorem gauss_weight_4_2 :
    gauss_weight legendre_roots_4.LR_roots 2 = 1 / 2 + Real.sqrt (5 / 6) / 6 := by
  rw [gauss_weight_eq_weights legendre_roots_4.LR_roots fourGaussian legendre_roots_val_eq 2,
    sqrt_five_sixths]
  change (18 + fourRadical) / 36 = _
  ring

/-- The last four-point weight is `1 / 2 - √(5/6) / 6`. -/
theorem gauss_weight_4_3 :
    gauss_weight legendre_roots_4.LR_roots 3 = 1 / 2 - Real.sqrt (5 / 6) / 6 := by
  rw [gauss_weight_eq_weights legendre_roots_4.LR_roots fourGaussian legendre_roots_val_eq 3,
    sqrt_five_sixths]
  change (18 - fourRadical) / 36 = _
  ring

/-- The record of the four-point weights. -/
def gauss_weights_4 : gauss_weights 4 where
  GW_legendre := legendre_roots_4
  GW_vals := ![1 / 2 - Real.sqrt (5 / 6) / 6, 1 / 2 + Real.sqrt (5 / 6) / 6,
    1 / 2 + Real.sqrt (5 / 6) / 6, 1 / 2 - Real.sqrt (5 / 6) / 6]
  GW_good i := by
    fin_cases i
    exacts [gauss_weight_4_0, gauss_weight_4_1, gauss_weight_4_2, gauss_weight_4_3]

/-- The records of the roots of `legendre n` for `n < 5`. -/
def some_legendre_roots : (n : Fin 5) → legendre_roots n
  | ⟨0, _⟩ => legendre_roots_0
  | ⟨1, _⟩ => legendre_roots_1
  | ⟨2, _⟩ => legendre_roots_2
  | ⟨3, _⟩ => legendre_roots_3
  | ⟨4, _⟩ => legendre_roots_4

/-- The records of the Gauss weights for `n < 5`. -/
def some_gauss_weights : (n : Fin 5) → gauss_weights n
  | ⟨0, _⟩ => gauss_weights_0
  | ⟨1, _⟩ => gauss_weights_1
  | ⟨2, _⟩ => gauss_weights_2
  | ⟨3, _⟩ => gauss_weights_3
  | ⟨4, _⟩ => gauss_weights_4

/-- Any two records of the roots of `legendre n` are equal. -/
theorem legendre_roots_unique {n : ℕ} (r r' : legendre_roots n) : r = r' := by
  obtain ⟨p, rfl, roots⟩ := r
  obtain ⟨p', rfl, roots'⟩ := r'
  rw [roots_of_ortho_p_unique roots roots']

/-- The Gauss–Legendre rule with `n` nodes, for `n < 5`. -/
def Gauss_Legendre_quadrature (n : Fin 5) : (ℝ → ℝ) → ℝ :=
  compute_G (some_gauss_weights n)

/-- The one-point rule is the midpoint rule `2 f(0)`. -/
theorem Gauss_Legendre_quadrature_one (f : ℝ → ℝ) : Gauss_Legendre_quadrature 1 f = 2 * f 0 := by
  change compute_G gauss_weights_1 f = 2 * f 0
  rw [compute_G, Fin.sum_univ_one]
  rfl

/-- For `0 < n` and `f` that is `2n` times continuously differentiable, the error of
`Gauss_Legendre_quadrature n` on `f` is `f^(2n)(ξ) / (2n)!` times the integral of
`(legendre n)^2` for some `ξ ∈ [-1, 1]`. -/
theorem legendre_quadrature_error' (n : Fin 5) (f : ℝ → ℝ) (hn : 0 < (n : ℕ))
    (hf : ContDiff ℝ (2 * (n : ℕ)) f) :
    ∃ ξ ∈ Set.Icc (-1 : ℝ) 1, intgal f - Gauss_Legendre_quadrature n f =
      iteratedDeriv (2 * (n : ℕ)) f ξ / (2 * (n : ℕ)).factorial *
        intgal (fun x => (legendre n).eval x ^ 2) :=
  legendre_quadrature_error (some_gauss_weights n) f hn hf

/-- `b` bounds the error of `Gauss_Legendre_quadrature n` on `f` through the `2n`-th derivative:
on `[-1, 1]` it is at most `b` times `(2n)!` over the integral of `(legendre n)^2`. -/
def quadrature_error_bound (f : ℝ → ℝ) (n : Fin 5) (b : ℝ) : Prop :=
  ∀ x ∈ Set.Icc (-1 : ℝ) 1, |iteratedDeriv (2 * (n : ℕ)) f x| ≤
    b * ((2 * (n : ℕ)).factorial / intgal (fun x => (legendre n).eval x ^ 2))

/-- For `0 < n` and `f` that is `2n` times continuously differentiable, a bound in the sense of
`quadrature_error_bound` bounds the error of `Gauss_Legendre_quadrature n` on `f`. -/
theorem quadrature_error_bound_is_bound (n : Fin 5) (f : ℝ → ℝ) (b : ℝ) (hn : 0 < (n : ℕ))
    (hf : ContDiff ℝ (2 * (n : ℕ)) f) (h : quadrature_error_bound f n b) :
    |intgal f - Gauss_Legendre_quadrature n f| ≤ b := by
  obtain ⟨ξ, hξ, e⟩ := legendre_quadrature_error' n f hn hf
  have hu : 0 < intgal (fun x => (legendre n).eval x ^ 2) := by
    have h₀ := ortho_p2_positive lo_lt_hi w_positive wcontinuous n
    simp only [eval_mul] at h₀
    simpa only [intgal, legendre, sq] using h₀
  have hk : (0 : ℝ) < (2 * (n : ℕ)).factorial := by exact_mod_cast Nat.factorial_pos _
  rw [e, abs_mul, abs_div, abs_of_pos hk, abs_of_pos hu, div_mul_eq_mul_div, div_le_iff₀ hk,
    ← le_div_iff₀ hu, mul_div_assoc]
  exact h ξ hξ

end

end Quadrature.Legendre
