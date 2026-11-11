/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import CAS.Continuum.Quadrature.Gaussian.Nodal
import Quadrature.Gaussian.Orthogonal

/-!
# Gaussian quadrature at the roots of `ortho_p`

This module restates the second part of simple_cfem's `proof/quadrature.v`, which covers
paragraphs 13 to 19 of Stewart's Lecture 23. The Gaussian rule takes the `n` roots of
`ortho_p a b w n`, listed in increasing order, as nodes, and the integrals of the Lagrange basis
polynomials on those roots as weights. The record of the roots and the lemmas about the rule keep
their Rocq names. Each proof turns the record into a `GaussianRule` of SymLean, our verified
computer algebra system, and reads the result off SymLean's exactness, positivity and remainder
theorems. Paragraph 20, convergence for continuous integrands, is SymLean's
`gaussian_rules_converge`; `quadrature.v` has no completed statement of it.

## Main definitions

* `roots_of_ortho_p a b w n`: the roots of `ortho_p a b w n`, strictly increasing and in
  `[a, b]`, with the Rocq fields `ROOTS_vals`, `ROOTS_zero`, `ROOTS_sorted` and `ROOTS_inrange`.
* `gauss_weight roots i`: the integral of the `i`-th Lagrange basis polynomial on the roots.
* `G roots f`: the rule applied to `f`.

## Main results

* `roots_of_ortho_p_at_most`, `roots_of_ortho_p_unique`: the record lists every root, so there
  is only one record.
* `quadrature_exact_upto_n`, `quadrature_exact_for`, `quadrature_exact_for'`: the rule is exact
  for polynomials of degree below `n`, and below `2n`.
* `gauss_weight_positive`, `gauss_weight_leq_1`: each weight is positive and at most `∫ w`.
* `quadrature_error`: the remainder is `f^(2n)(ξ) / (2n)!` times `∫ (ortho_p a b w n)^2 w` for
  some `ξ ∈ [a, b]`.

## How it works

Exactness below degree `2n` is division with remainder: write a polynomial `f` as
`ortho_p a b w n * q + r` with `q` and `r` of degree below `n`. The first term integrates to zero
by orthogonality and vanishes at the nodes, and the rule is interpolatory, so it is exact for `r`.
Each weight is the integral of the square of its Lagrange basis polynomial, by exactness, and
that integral is positive.

`quadrature_error` is the classical remainder, and SymLean proves it by Hermite interpolation.
Let `H` be the polynomial of degree below `2n` that agrees with `f` and `f'` at the nodes. The
rule only sees values at the nodes and is exact for `H`, so its error on `f` is the integral of
`(f - H) w`. Write `p = ortho_p a b w n`, the nodal polynomial. At each `x`, subtracting the right
multiple of `p ^ 2` from `f - H` leaves a function with double zeros at the nodes and one more
zero at `x`. The generalized Rolle theorem then gives some `ξ` with
`f x - H x = f^(2n)(ξ) / (2n)! * p x ^ 2`. As `p ^ 2 w` is nonnegative, a mean-value principle for
integrals merges the pointwise `ξ` into a single one.

## Implementation notes

Compared with `quadrature.v`: the roots are a strictly monotone function on `Fin n` rather than a
sorted tuple, so `roots_of_ortho_p_unique` follows from Mathlib's statement that a strictly
monotone function on `Fin n` is determined by its range, and we need no analogue of the Rocq lemma
`same_members_increasing_equal`. We prove `quadrature_error` for `0 < n` and `f` that is `2n` times
continuously differentiable, with the derivative of order `2n` and the square of
`ortho_p a b w n`, the nodal polynomial of the `n` roots; the Rocq statement squares
`ortho_p (n + 1)`. Stewart writes the formula for the `n + 1` nodes `x_0, ..., x_n`, with
`f^(2n+2)` and `p_{n+1}`. The statement uses the global derivative `iteratedDeriv`, like the Rocq
`derive1n`, and so asks for `ContDiff`; SymLean's `GaussianRule.remainder` needs smoothness only
on `[a, b]`.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/quadrature.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/quadrature.v):
  `roots_of_ortho_p`, `gauss_weight`, `G` and their lemmas.
* G. W. Stewart, *Afternotes on Numerical Analysis*, SIAM, Philadelphia, 1996,
  [doi:10.1137/1.9781611971491](https://doi.org/10.1137/1.9781611971491). Lecture 23, which
  `quadrature.v` follows.
-/

namespace Quadrature

open Polynomial MeasureTheory CAS.Continuum

noncomputable section

/-- Stewart's paragraph 13: the roots of `ortho_p a b w n`, that is, `n` real numbers in
increasing order, each a root of `ortho_p a b w n` and each in `[a, b]`. Stewart shows in
paragraphs 13 and 14 that these roots exist; SymLean proves it for every `n` (`orthogonal_splits`,
`orthogonal_squarefree`, `orthogonal_root_mem_Ioo`). -/
@[ext]
structure roots_of_ortho_p (a b : ℝ) (w : ℝ → ℝ) (n : ℕ) where
  /-- The roots, indexed in increasing order. -/
  ROOTS_vals : Fin n → ℝ
  /-- Every entry is a root of `ortho_p a b w n`. -/
  ROOTS_zero : ∀ i, (ortho_p a b w n).IsRoot (ROOTS_vals i)
  /-- The entries are strictly increasing. -/
  ROOTS_sorted : StrictMono ROOTS_vals
  /-- Every entry lies in `[a, b]`. -/
  ROOTS_inrange : ∀ i, ROOTS_vals i ∈ Set.Icc a b

variable {a b : ℝ} {w : ℝ → ℝ} {n : ℕ}

/-- Stewart's paragraph 15: the weight at the `i`-th root, the integral against `w` of the
`i`-th Lagrange basis polynomial on the roots. -/
def gauss_weight (roots : roots_of_ortho_p a b w n) (i : Fin n) : ℝ :=
  intgal a b w (fun x => (Lagrange.basis Finset.univ roots.ROOTS_vals i).eval x)

/-- Stewart's paragraph 15: the Gaussian rule on the roots applied to `f`. -/
def G (roots : roots_of_ortho_p a b w n) (f : ℝ → ℝ) : ℝ :=
  ∑ i, gauss_weight roots i * f (roots.ROOTS_vals i)

/-- The nodal polynomial of the roots is `ortho_p a b w n`. -/
theorem roots_of_ortho_p.nodal_eq (roots : roots_of_ortho_p a b w n) :
    Lagrange.nodal Finset.univ roots.ROOTS_vals = ortho_p a b w n := by
  refine Polynomial.eq_of_degree_le_of_eval_index_eq Finset.univ
    (Set.injOn_of_injective roots.ROOTS_sorted.injective) Lagrange.degree_nodal.le ?_ ?_
    fun i _ => ?_
  · rw [Lagrange.degree_nodal, ortho_p_size, Finset.card_univ, Fintype.card_fin]
  · rw [Lagrange.nodal_monic.leadingCoeff, (ortho_p_monic n).leadingCoeff]
  · rw [Lagrange.eval_nodal_at_node (Finset.mem_univ i), (roots.ROOTS_zero i).eq_zero]

/-- For a continuous weight that is positive on `[a, b]`, the nodal polynomial of the roots is
orthogonal to every polynomial of degree below `n`. -/
theorem roots_of_ortho_p.nodal_orthogonal (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (hw : ContinuousOn w (Set.uIcc a b)) (roots : roots_of_ortho_p a b w n) (q : ℝ[X])
    (hq : q.natDegree < n) :
    polynomialIntegral a b w hw (Lagrange.nodal Finset.univ roots.ROOTS_vals * q) = 0 := by
  rw [roots.nodal_eq]
  exact polynomialIntegral_ortho_p_mul Hab wpos hw
    (degree_le_natDegree.trans_lt (by exact_mod_cast hq))

/-- For `a ≤ b`, `gauss_weight` is SymLean's interpolatory weight for `polynomialIntegral`. -/
theorem gauss_weight_eq_interpolatoryWeight (hab : a ≤ b) (hw : ContinuousOn w (Set.uIcc a b))
    (roots : roots_of_ortho_p a b w n) (i : Fin n) :
    gauss_weight roots i =
      interpolatoryWeight (polynomialIntegral a b w hw) roots.ROOTS_vals i :=
  intgal_eq_polynomialIntegral hab hw fun _ => rfl

/-- For a continuous weight that is positive on `[a, b]`, the roots and their weights form a
SymLean `GaussianRule`. -/
def roots_of_ortho_p.toGaussianRule (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (hw : ContinuousOn w (Set.uIcc a b)) (roots : roots_of_ortho_p a b w n) :
    GaussianRule a b w hw n where
  nodes := roots.ROOTS_vals
  weights := gauss_weight roots
  injective := roots.ROOTS_sorted.injective
  interior i := orthogonal_root_mem_Ioo Hab w hw wpos (ortho_p a b w n) (ortho_p_nonzero n)
    (fun r hr => polynomialIntegral_ortho_p_mul Hab wpos hw (by rwa [ortho_p_size] at hr))
    (roots.ROOTS_zero i)
  positive i := by
    rw [gauss_weight_eq_interpolatoryWeight Hab.le hw]
    exact gaussian_weight_pos i.pos _ _ roots.ROOTS_sorted.injective
      (roots.nodal_orthogonal Hab wpos hw) (polynomialIntegral_square_pos Hab w hw wpos) i
  exact p hp := by
    simp only [gauss_weight_eq_interpolatoryWeight Hab.le hw]
    exact gaussian_exact _ _ roots.ROOTS_sorted.injective (roots.nodal_orthogonal Hab wpos hw)
      p hp

/-- Every root of `ortho_p a b w n` is one of the recorded roots, as in paragraph 14 of Stewart,
where the `n` roots are all the zeros of `p_n`. -/
theorem roots_of_ortho_p_at_most (roots : roots_of_ortho_p a b w n) (x : ℝ)
    (hx : (ortho_p a b w n).IsRoot x) : x ∈ Set.range roots.ROOTS_vals := by
  rw [← roots.nodal_eq, IsRoot.def, Lagrange.eval_nodal, Finset.prod_eq_zero_iff] at hx
  obtain ⟨i, -, hi⟩ := hx
  exact ⟨i, (sub_eq_zero.mp hi).symm⟩

/-- Any two records of the roots of `ortho_p a b w n` are equal. -/
theorem roots_of_ortho_p_unique (r r' : roots_of_ortho_p a b w n) : r = r' := by
  refine roots_of_ortho_p.ext ((r.ROOTS_sorted.range_inj_of_wellFoundedLT r'.ROOTS_sorted).mp ?_)
  apply Set.Subset.antisymm
  · rintro _ ⟨i, rfl⟩
    exact roots_of_ortho_p_at_most r' _ (r.ROOTS_zero i)
  · rintro _ ⟨i, rfl⟩
    exact roots_of_ortho_p_at_most r _ (r'.ROOTS_zero i)

/-- Stewart's paragraph 15, first step: for `a ≤ b` and a weight that is continuous on `[a, b]`,
the rule on the `n + 1` roots of `ortho_p a b w (n + 1)` integrates every polynomial of degree at
most `n` exactly. -/
theorem quadrature_exact_upto_n (hab : a ≤ b) (wcontinuous : ContinuousOn w (Set.Icc a b))
    (roots : roots_of_ortho_p a b w (n + 1)) (f : ℝ[X]) (hf : f.degree < (n + 1 : ℕ)) :
    intgal a b w (fun x => f.eval x) = G roots (fun x => f.eval x) := by
  have hw : ContinuousOn w (Set.uIcc a b) := by rwa [Set.uIcc_of_le hab]
  rw [intgal_eq_polynomialIntegral (p := f) hab hw fun _ => rfl,
    ← interpolatory_exact (polynomialIntegral a b w hw) roots.ROOTS_vals
      roots.ROOTS_sorted.injective f hf]
  simp only [interpolatoryValue, G, gauss_weight_eq_interpolatoryWeight hab hw]

/-- Stewart's paragraphs 15 and 16: for `a < b` and a weight that is continuous and positive on
`[a, b]`, the rule on the roots of `ortho_p a b w n` integrates every polynomial of degree below
`2n` exactly. -/
theorem quadrature_exact_for (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (wcontinuous : ContinuousOn w (Set.Icc a b)) (roots : roots_of_ortho_p a b w n)
    (f : ℝ[X]) (hf : f.degree < (2 * n : ℕ)) :
    intgal a b w (fun x => f.eval x) = G roots (fun x => f.eval x) := by
  have hw : ContinuousOn w (Set.uIcc a b) := by rwa [Set.uIcc_of_le Hab.le]
  rw [intgal_eq_polynomialIntegral (p := f) Hab.le hw fun _ => rfl]
  rcases eq_or_ne f 0 with rfl | hf₀
  · simp [G]
  · exact ((roots.toGaussianRule Hab wpos hw).exact f
      ((natDegree_lt_iff_degree_lt hf₀).mpr hf)).symm

/-- `quadrature_exact_for` for `n + 1` roots: the rule on the roots of `ortho_p a b w (n + 1)`
integrates every polynomial of degree below `2n + 2` exactly. -/
theorem quadrature_exact_for' (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (wcontinuous : ContinuousOn w (Set.Icc a b)) (roots : roots_of_ortho_p a b w (n + 1))
    (f : ℝ[X]) (hf : f.degree < (2 * n + 2 : ℕ)) :
    intgal a b w (fun x => f.eval x) = G roots (fun x => f.eval x) :=
  quadrature_exact_for Hab wpos wcontinuous roots f (by rwa [mul_add_one])

/-- Stewart's paragraph 17: for `a < b` and a weight that is continuous and positive on
`[a, b]`, every weight of the rule is positive. -/
theorem gauss_weight_positive (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (wcontinuous : ContinuousOn w (Set.Icc a b)) (roots : roots_of_ortho_p a b w n)
    (i : Fin n) : 0 < gauss_weight roots i :=
  (roots.toGaussianRule Hab wpos (by rwa [Set.uIcc_of_le Hab.le])).positive i

/-- Stewart's paragraph 18: for `a < b` and a weight that is continuous and positive on
`[a, b]`, every weight of the rule is at most the integral of `w`, the sum of the weights. -/
theorem gauss_weight_leq_1 (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (wcontinuous : ContinuousOn w (Set.Icc a b)) (roots : roots_of_ortho_p a b w n)
    (i : Fin n) : gauss_weight roots i ≤ intgal a b w (fun x => (1 : ℝ[X]).eval x) := by
  have hw : ContinuousOn w (Set.uIcc a b) := by rwa [Set.uIcc_of_le Hab.le]
  rw [intgal_eq_polynomialIntegral (p := 1) Hab.le hw fun _ => rfl]
  exact (roots.toGaussianRule Hab wpos hw).weight_le_mass i

/-- Stewart's paragraph 19: for `a < b`, a weight that is continuous and positive on `[a, b]`,
`0 < n` and `f` that is `2n` times continuously differentiable, the error of the rule on the roots
of `ortho_p a b w n` is `f^(2n)(ξ) / (2n)!` times the integral of `(ortho_p a b w n)^2` for some
`ξ ∈ [a, b]`. -/
theorem quadrature_error (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (wcontinuous : ContinuousOn w (Set.Icc a b)) (roots : roots_of_ortho_p a b w n)
    (f : ℝ → ℝ) (hn : 0 < n) (hf : ContDiff ℝ (2 * n) f) :
    ∃ ξ ∈ Set.Icc a b, intgal a b w f - G roots f =
      iteratedDeriv (2 * n) f ξ / (2 * n).factorial *
        intgal a b w (fun x => (ortho_p a b w n).eval x ^ 2) := by
  have hw : ContinuousOn w (Set.uIcc a b) := by rwa [Set.uIcc_of_le Hab.le]
  obtain ⟨ξ, hξ, h⟩ := GaussianRule.remainder_orthogonal Hab wpos hn
    (roots.toGaussianRule Hab wpos hw) hf.contDiffOn
  have hf' : ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) f := by exact_mod_cast hf
  have e : intgal a b w (fun x => (ortho_p a b w n).eval x ^ 2) =
      polynomialIntegral a b w hw (ortho_p a b w n ^ 2) :=
    intgal_eq_polynomialIntegral Hab.le hw fun x => by rw [eval_pow]
  refine ⟨ξ, hξ, ?_⟩
  rw [e, intgal_eq_integral Hab.le,
    ← iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc Hab) hf'.contDiffAt hξ,
    ortho_p_eq_integralOrthogonalPolynomial Hab wpos hw]
  exact h

end

end Quadrature
