/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import CAS.Continuum.Quadrature.Gaussian.Recurrence

/-!
# Orthogonal polynomials by the three-term recurrence

This module restates the first part of simple_cfem's `proof/quadrature.v`, which covers
paragraphs 1 to 12 of Stewart's Lecture 23: the weighted integral, orthogonality, and the monic
orthogonal polynomials of a weight `w` on `[a, b]`, defined by the three-term recurrence. The
definitions and lemmas keep their Rocq names. The proofs are short because SymLean, our verified
computer algebra system, already has the theory with the polynomials defined by projection: an
induction along the recurrence shows that `ortho_p` is SymLean's `integralOrthogonalPolynomial`,
and orthogonality and positivity come from there.

## Main definitions

* `intgal a b w f`: the integral of `f x * w x` over `[a, b]`.
* `orthogonal`, `orthogonal_polynomials`: orthogonality for this pairing.
* `three_term_recurrence`, `ortho_p`: the monic orthogonal polynomials by the recurrence.

## Main results

* `ortho_p_size`, `ortho_p_monic`, `ortho_p_nonzero`: `ortho_p a b w n` is monic of degree `n`
  for every `w`.
* `ortho_p_eq_integralOrthogonalPolynomial`: the recurrence produces SymLean's polynomials.
* `sqr_poly_positive`, `ortho_p2_positive`: nonzero squares have positive integral.
* `ortho_p_orthogonal`, `ortho_p_orthogonal_special`, `orthogonal_polynomials_ortho_p`.

## Implementation notes

Compared with `quadrature.v`: a polynomial of Rocq `size` `n + 1` is a polynomial of degree `n`
here. The section hypotheses `Hab`, `wpos` and `wcontinuous` become explicit arguments of the lemmas
that use them, and `wcontinuous` is continuity of `w` on `[a, b]`, which follows from the Rocq
hypothesis of continuity at every point of `[a, b]`. We prove `sqr_poly_positive` from SymLean's
`polynomialIntegral_square_pos`, under `a < b` as in the Rocq section; the Rocq proof uses
`Rintegral_gt_0`, which refers to Saikawa's MathComp-Analysis pull request. We do not restate
Stewart's paragraphs 6 to 8 (`stewart_lemma_23_6`, `polySn_orthogonal_n`), which the construction
by projection does not need.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/quadrature.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/quadrature.v):
  `intgal`, `three_term_recurrence`, `ortho_p` and their lemmas.
* G. W. Stewart, *Afternotes on Numerical Analysis*, SIAM, Philadelphia, 1996,
  [doi:10.1137/1.9781611971491](https://doi.org/10.1137/1.9781611971491). Lecture 23, which
  `quadrature.v` follows.
* T. Saikawa, *add Rintegral_gt0 and Rintegral_gt0_itvcc*, MathComp-Analysis pull request 2086,
  [github.com/math-comp/analysis/pull/2086](https://github.com/math-comp/analysis/pull/2086).
-/

namespace Quadrature

open Polynomial MeasureTheory CAS.Continuum

noncomputable section

/-- Stewart's paragraph 2: `intgal a b w f` is the integral of `f x * w x` over the closed
interval `[a, b]`. -/
def intgal (a b : ℝ) (w f : ℝ → ℝ) : ℝ := ∫ x in Set.Icc a b, f x * w x

/-- Stewart's paragraph 4: `f` and `g` are orthogonal when the integral of `f x * g x` against
`w` vanishes. -/
def orthogonal (a b : ℝ) (w f g : ℝ → ℝ) : Prop := intgal a b w (fun x => f x * g x) = 0

/-- Stewart's paragraph 5: `p` is a sequence of orthogonal polynomials, that is, `p i` has
degree `i`, and distinct members are orthogonal. -/
def orthogonal_polynomials (a b : ℝ) (w : ℝ → ℝ) (p : ℕ → ℝ[X]) : Prop :=
  (∀ i, (p i).degree = i) ∧
    ∀ i j, i ≠ j → orthogonal a b w (fun x => (p i).eval x) (fun x => (p j).eval x)

/-- Stewart's paragraphs 9 to 12: the three-term recurrence. Entry `n` is the pair of
`ortho_p a b w n` and `ortho_p a b w (n - 1)`, with `0` in place of the second when `n = 0`. -/
def three_term_recurrence (a b : ℝ) (w : ℝ → ℝ) : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, 0)
  | 1 => (X - C (intgal a b w id / intgal a b w fun _ => 1), 1)
  | n + 2 =>
    let p := (three_term_recurrence a b w (n + 1)).1
    let q := (three_term_recurrence a b w (n + 1)).2
    let α := intgal a b w (fun x => x * (p.eval x * p.eval x)) /
      intgal a b w (fun x => p.eval x * p.eval x)
    let β := intgal a b w (fun x => x * (p.eval x * q.eval x)) /
      intgal a b w (fun x => q.eval x * q.eval x)
    (X * p - C α * p - C β * q, p)

/-- The polynomial of degree `n` produced by the three-term recurrence. -/
def ortho_p (a b : ℝ) (w : ℝ → ℝ) (n : ℕ) : ℝ[X] := (three_term_recurrence a b w n).1

variable {a b : ℝ} {w : ℝ → ℝ}

/-- The second entry of step `n + 1` of the recurrence is the first entry of step `n`. -/
theorem ortho_p_prev (n : ℕ) :
    (three_term_recurrence a b w (n + 1)).2 = (three_term_recurrence a b w n).1 := by
  cases n <;> rfl

/-- The recurrence step, written with `ortho_p`. -/
theorem ortho_p_add_two (n : ℕ) :
    ortho_p a b w (n + 2) =
      X * ortho_p a b w (n + 1) -
        C (intgal a b w (fun x => x * ((ortho_p a b w (n + 1)).eval x *
            (ortho_p a b w (n + 1)).eval x)) /
          intgal a b w (fun x => (ortho_p a b w (n + 1)).eval x *
            (ortho_p a b w (n + 1)).eval x)) * ortho_p a b w (n + 1) -
        C (intgal a b w (fun x => x * ((ortho_p a b w (n + 1)).eval x *
            (ortho_p a b w n).eval x)) /
          intgal a b w (fun x => (ortho_p a b w n).eval x * (ortho_p a b w n).eval x)) *
          ortho_p a b w n := by
  simp only [ortho_p, three_term_recurrence, ortho_p_prev]

private theorem ortho_p_monic_degree :
    ∀ n, (ortho_p a b w n).Monic ∧ (ortho_p a b w n).degree = n
  | 0 => by simp [ortho_p, three_term_recurrence]
  | 1 => by
    simp only [ortho_p, three_term_recurrence]
    exact ⟨monic_X_sub_C _, by simp⟩
  | n + 2 => by
    have hp₁ : (ortho_p a b w (n + 1)).Monic ∧
        (ortho_p a b w (n + 1)).degree = ((n + 1 : ℕ) : WithBot ℕ) :=
      ortho_p_monic_degree (n + 1)
    have hr₀ : (ortho_p a b w n).Monic ∧ (ortho_p a b w n).degree = n := ortho_p_monic_degree n
    obtain ⟨α, β, h⟩ : ∃ α β : ℝ, ortho_p a b w (n + 2) = X * ortho_p a b w (n + 1) -
        C α * ortho_p a b w (n + 1) - C β * ortho_p a b w n := ⟨_, _, ortho_p_add_two n⟩
    rw [h]
    generalize ortho_p a b w (n + 1) = p at hp₁ ⊢
    generalize ortho_p a b w n = r at hr₀ ⊢
    obtain ⟨hp, hpd⟩ := hp₁
    have hrd := hr₀.2
    have hxp : (X * p).degree = ((n + 2 : ℕ) : WithBot ℕ) := by
      rw [degree_mul, degree_X, hpd]
      push_cast
      ring
    have hα : (C α * p).degree < (X * p).degree := by
      apply (show (C α * p).degree ≤ p.degree by
        simpa [smul_eq_C_mul] using degree_smul_le α p).trans_lt
      rw [hpd, hxp]
      exact_mod_cast (show n + 1 < n + 2 by omega)
    have hfirst : (X * p - C α * p).degree = ((n + 2 : ℕ) : WithBot ℕ) := by
      rw [degree_sub_eq_left_of_degree_lt hα, hxp]
    have hβ : (C β * r).degree < (X * p - C α * p).degree := by
      apply (show (C β * r).degree ≤ r.degree by
        simpa [smul_eq_C_mul] using degree_smul_le β r).trans_lt
      rw [hrd, hfirst]
      exact_mod_cast (show n < n + 2 by omega)
    exact ⟨((monic_X.mul hp).sub_of_left hα).sub_of_left hβ,
      by rw [degree_sub_eq_left_of_degree_lt hβ, hfirst]⟩

/-- `ortho_p a b w n` has degree `n`, the Rocq `size` `n + 1`. -/
theorem ortho_p_size (n : ℕ) : (ortho_p a b w n).degree = n := (ortho_p_monic_degree n).2

/-- `ortho_p a b w n` is monic. -/
theorem ortho_p_monic (n : ℕ) : (ortho_p a b w n).Monic := (ortho_p_monic_degree n).1

/-- `ortho_p a b w n` is not the zero polynomial. -/
theorem ortho_p_nonzero (n : ℕ) : ortho_p a b w n ≠ 0 := (ortho_p_monic n).ne_zero

/-- For `a ≤ b`, `intgal` is the interval integral of `f x * w x` from `a` to `b`. -/
theorem intgal_eq_integral (hab : a ≤ b) (f : ℝ → ℝ) :
    intgal a b w f = ∫ x in a..b, f x * w x := by
  rw [intgal, intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

/-- For `a ≤ b`, the `intgal` of the evaluation of a polynomial `p` is SymLean's
`polynomialIntegral` of `p`. -/
theorem intgal_eq_polynomialIntegral (hab : a ≤ b) (hw : ContinuousOn w (Set.uIcc a b))
    {f : ℝ → ℝ} {p : ℝ[X]} (h : ∀ x, f x = p.eval x) :
    intgal a b w f = polynomialIntegral a b w hw p := by
  rw [intgal_eq_integral hab]
  change ∫ x in a..b, f x * w x = ∫ x in a..b, p.eval x * w x
  simp only [h]

/-- For a continuous weight that is positive on `[a, b]`, `ortho_p` is SymLean's
`integralOrthogonalPolynomial`. -/
theorem ortho_p_eq_integralOrthogonalPolynomial (Hab : a < b)
    (wpos : ∀ x ∈ Set.Icc a b, 0 < w x) (hw : ContinuousOn w (Set.uIcc a b)) :
    ∀ n, ortho_p a b w n = integralOrthogonalPolynomial a b Hab w hw wpos n
  | 0 => by
    rw [integralOrthogonalPolynomial, orthogonalPolynomial_zero]
    rfl
  | 1 => by
    rw [integralOrthogonalPolynomial, orthogonalPolynomial_one, recurrenceAlpha,
      orthogonalPolynomial_zero]
    change X - C (intgal a b w id / intgal a b w fun _ => 1) = _
    have e₁ : intgal a b w id = polynomialIntegral a b w hw (X * 1 ^ 2) :=
      intgal_eq_polynomialIntegral Hab.le hw fun x => by simp
    have e₂ : intgal a b w (fun _ => 1) = polynomialIntegral a b w hw (1 ^ 2) :=
      intgal_eq_polynomialIntegral Hab.le hw fun x => by simp
    rw [e₁, e₂]
  | n + 2 => by
    have h₁ : ortho_p a b w (n + 1) = integralOrthogonalPolynomial a b Hab w hw wpos (n + 1) :=
      ortho_p_eq_integralOrthogonalPolynomial Hab wpos hw (n + 1)
    have h₀ : ortho_p a b w n = integralOrthogonalPolynomial a b Hab w hw wpos n :=
      ortho_p_eq_integralOrthogonalPolynomial Hab wpos hw n
    rw [ortho_p_add_two, h₁, h₀]
    simp only [integralOrthogonalPolynomial]
    rw [orthogonalPolynomial_recurrence, recurrenceAlpha, recurrenceBeta]
    generalize orthogonalPolynomial (polynomialIntegral a b w hw)
      (polynomialIntegral_square_pos Hab w hw wpos) (n + 1) = P
    generalize orthogonalPolynomial (polynomialIntegral a b w hw)
      (polynomialIntegral_square_pos Hab w hw wpos) n = Q
    have e₁ : intgal a b w (fun x => x * (P.eval x * P.eval x)) =
        polynomialIntegral a b w hw (X * P ^ 2) :=
      intgal_eq_polynomialIntegral Hab.le hw fun x => by
        simp only [eval_mul, eval_pow, eval_X]
        ring
    have e₂ : intgal a b w (fun x => P.eval x * P.eval x) =
        polynomialIntegral a b w hw (P ^ 2) :=
      intgal_eq_polynomialIntegral Hab.le hw fun x => by
        simp only [eval_pow]
        ring
    have e₃ : intgal a b w (fun x => x * (P.eval x * Q.eval x)) =
        polynomialIntegral a b w hw (X * P * Q) :=
      intgal_eq_polynomialIntegral Hab.le hw fun x => by
        simp only [eval_mul, eval_X]
        ring
    have e₄ : intgal a b w (fun x => Q.eval x * Q.eval x) =
        polynomialIntegral a b w hw (Q ^ 2) :=
      intgal_eq_polynomialIntegral Hab.le hw fun x => by
        simp only [eval_pow]
        ring
    rw [e₁, e₂, e₃, e₄]

/-- For a continuous weight that is positive on `[a, b]`, `ortho_p a b w n` is orthogonal to
every polynomial of degree below `n`. -/
theorem polynomialIntegral_ortho_p_mul (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (hw : ContinuousOn w (Set.uIcc a b)) {n : ℕ} {q : ℝ[X]} (hq : q.degree < n) :
    polynomialIntegral a b w hw (ortho_p a b w n * q) = 0 := by
  rw [ortho_p_eq_integralOrthogonalPolynomial Hab wpos hw, integralOrthogonalPolynomial]
  exact orthogonalPolynomial_orthogonal _ _ n q hq

/-- Orthogonality is symmetric. -/
theorem orthogonal_comm {f g : ℝ → ℝ} : orthogonal a b w f g ↔ orthogonal a b w g f := by
  have h : (fun x => f x * g x) = fun x => g x * f x := funext fun x => mul_comm _ _
  unfold orthogonal
  rw [h]

/-- For `a < b` and a weight that is continuous and positive on `[a, b]`, the square of a
nonzero polynomial has positive integral. -/
theorem sqr_poly_positive (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (wcontinuous : ContinuousOn w (Set.Icc a b)) (p : ℝ[X]) (hp : p ≠ 0) :
    0 < intgal a b w (fun x => (p * p).eval x) := by
  have hw : ContinuousOn w (Set.uIcc a b) := by rwa [Set.uIcc_of_le Hab.le]
  have h : intgal a b w (fun x => (p * p).eval x) = polynomialIntegral a b w hw (p ^ 2) :=
    intgal_eq_polynomialIntegral Hab.le hw fun x => by rw [sq]
  rw [h]
  exact polynomialIntegral_square_pos Hab w hw wpos p hp

/-- For `a < b` and a weight that is continuous and positive on `[a, b]`, the square of
`ortho_p a b w n` has positive integral. -/
theorem ortho_p2_positive (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (wcontinuous : ContinuousOn w (Set.Icc a b)) (n : ℕ) :
    0 < intgal a b w (fun x => (ortho_p a b w n * ortho_p a b w n).eval x) :=
  sqr_poly_positive Hab wpos wcontinuous _ (ortho_p_nonzero n)

/-- For `a < b` and a weight that is continuous and positive on `[a, b]`, `ortho_p a b w j` and
`ortho_p a b w i` are orthogonal when `i < j`. -/
theorem ortho_p_orthogonal (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (wcontinuous : ContinuousOn w (Set.Icc a b)) (i j : ℕ) (hij : i < j) :
    orthogonal a b w (fun x => (ortho_p a b w j).eval x) (fun x => (ortho_p a b w i).eval x) := by
  have hw : ContinuousOn w (Set.uIcc a b) := by rwa [Set.uIcc_of_le Hab.le]
  have h : intgal a b w (fun x => (ortho_p a b w j).eval x * (ortho_p a b w i).eval x) =
      polynomialIntegral a b w hw (ortho_p a b w j * ortho_p a b w i) :=
    intgal_eq_polynomialIntegral Hab.le hw fun x => by rw [eval_mul]
  change intgal a b w (fun x => (ortho_p a b w j).eval x * (ortho_p a b w i).eval x) = 0
  rw [h]
  exact polynomialIntegral_ortho_p_mul Hab wpos hw (by rw [ortho_p_size]; exact_mod_cast hij)

/-- Consecutive polynomials `ortho_p a b w (n + 1)` and `ortho_p a b w n` are orthogonal. -/
theorem ortho_p_orthogonal_special (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (wcontinuous : ContinuousOn w (Set.Icc a b)) (n : ℕ) :
    orthogonal a b w (fun x => (ortho_p a b w (n + 1)).eval x)
      (fun x => (ortho_p a b w n).eval x) :=
  ortho_p_orthogonal Hab wpos wcontinuous n (n + 1) n.lt_add_one

/-- Stewart's paragraph 12: the recurrence produces a sequence of orthogonal polynomials. -/
theorem orthogonal_polynomials_ortho_p (Hab : a < b) (wpos : ∀ x ∈ Set.Icc a b, 0 < w x)
    (wcontinuous : ContinuousOn w (Set.Icc a b)) :
    orthogonal_polynomials a b w (ortho_p a b w) := by
  refine ⟨ortho_p_size, fun i j hij => ?_⟩
  rcases lt_or_gt_of_ne hij with h | h
  · exact orthogonal_comm.mp (ortho_p_orthogonal Hab wpos wcontinuous i j h)
  · exact ortho_p_orthogonal Hab wpos wcontinuous j i h

end

end Quadrature
