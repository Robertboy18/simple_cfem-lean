/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import CAS.Continuum.Quadrature.Gaussian.Remainder
import Quadrature.Binary64.FiniteExecution
import Quadrature.Legendre.Bounds
import Quadrature.Rules.Basic

/-!
# Accuracy for a certified stored Gaussian rule

This module restates the accuracy theorems of section `FLOAT` of simple_cfem's
`proof/quadmodel_accuracy.v`. We bound the error of the C program's loop for every stored table
that has a certificate. If the
callback `f` is within `error` of a real integrand `g` that is bounded and Lipschitz on `[-1, 1]`,
and a range budget holds, the floating-point result is finite and close to the exact Gaussian
rule applied to `g`. If `g` also has a bounded derivative of order `2n`, adding the Gaussian
remainder bounds the distance of the result from the integral of `g` over `[-1, 1]`.

## Main definitions

* `function_accuracy g f error`: on finite binary64 inputs in `[-1, 1]`, the callback `f` is
  finite and within `error` of `g`. The name and argument order follow the Rocq development.

## Main results

* `StoredRule.Certificate.integrate_model_roundoff_err`: the loop result is finite and close to
  the ideal Gaussian rule applied to `g`.
* `StoredRule.Certificate.finite_integrate_model`: every intermediate value of the loop is
  finite.
* `StoredRule.Certificate.integrate_model_err`: the loop result is close to the exact integral.

## How it works

We split the error at the exact sum of the products of the stored weights and the callback
values. That sum differs from the ideal rule applied to `g` by table and callback errors alone
(`samples_error`): a term moves by at most its absolute stored weight times the sum of the
callback error and the Lipschitz constant of `g` times the node error, plus the bound on `g`
times the weight error. The rounded loop is within `2n` half-ULPs at `radius` of the exact sum,
one for each multiplication and each addition, under the range budget of
`Quadrature.Binary64.BoundedRoundoff`. `product_mass_le` bounds the mass of the products that
the budget counts. SymLean's `GaussianRule.abs_error_le` closes the gap between the ideal rule
and the integral.

## Implementation notes

Compared with `quadmodel_accuracy.v`: the Rocq lemmas of the same names take at most four nodes, fix
the node and weight errors at `default_rel`, and bound the result by the closed expressions
`integrate_model_acc` and `maxwf` under the overflow conditions `parameter_limits` and
`finite_integrate_condition`. We keep the node and weight tolerances and the range budget as
parameters instead, so one theorem serves every stored table. The bound on `g` is their
`fbound (-1) 1 g bound`. Where they assume `deriv_bound (-1) 1 g d`, we assume the Lipschitz bound
that `g_max_deriv` derives from it. Their `integrate_model_err` takes the quadrature error bound as
a hypothesis `quadrature_error_bound g n b`; ours assumes a bound on the `2n`-th derivative of `g`
and adds the remainder itself.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/quadmodel_accuracy.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/quadmodel_accuracy.v):
  section `FLOAT`.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange CAS.Continuum
open scoped BigOperators

/-- On every finite binary64 input in `[-1,1]`, the callback `f` returns a finite value within
`error` of `g` at the decoded input. -/
def function_accuracy (g : ℝ → ℝ) (f : Value → Value) (error : ℝ) : Prop :=
  ∀ x, Model.isFinite x = true → Model.toReal x ∈ Set.Icc (-1 : ℝ) 1 →
    Model.isFinite (f x) = true ∧
    |Model.toReal (f x) - g (Model.toReal x)| ≤ error

namespace StoredRule.Certificate

variable {n : ℕ} {stored : StoredRule n} {ideal : Legendre.Rule n}
    {nodeTolerance weightTolerance : ℝ}

/-- Under a stored-rule certificate with `0 < n`, the absolute values of the stored weights sum
to at most `2 + n * weightTolerance`, since the ideal weights are positive and sum to `2`. -/
theorem sum_abs_weights_le
    (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n) :
    ∑ i, |Model.toReal (stored.weights i)| ≤ 2 + n * weightTolerance := by
  have hm := ideal.sum_weights hn
  norm_num [polynomialIntegral] at hm
  calc
    _ ≤ ∑ i, (ideal.weights i + weightTolerance) := by
      apply Finset.sum_le_sum
      intro i _
      have h := abs_add_le (Model.toReal (stored.weights i) - ideal.weights i)
        (ideal.weights i)
      rw [sub_add_cancel, abs_of_pos (ideal.positive i)] at h
      linarith [cert.weight_error i]
    _ = _ := by simp [Finset.sum_add_distrib, hm]

/-- Under a certificate, `function_accuracy g f error` and a Lipschitz constant `lipschitz` for
`g` on `[-1, 1]`, the callback at stored node `i` is finite and within
`error + lipschitz * nodeTolerance` of `g` at ideal node `i`. -/
theorem callback_at_node (cert : stored.Certificate ideal nodeTolerance weightTolerance)
    {f : Value → Value} {g : ℝ → ℝ} {error lipschitz : ℝ}
    (hc : function_accuracy g f error) (hL : 0 ≤ lipschitz)
    (hg : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |g x - g y| ≤ lipschitz * |x - y|) (i : Fin n) :
    Model.isFinite (f (stored.nodes i)) = true ∧
    |Model.toReal (f (stored.nodes i)) - g (ideal.nodes i)| ≤
      error + lipschitz * nodeTolerance := by
  have hc' := hc _ (cert.node_finite i) (cert.node_mem i)
  have hn := hg _ (cert.node_mem i) _
    ⟨(ideal.interior i).1.le, (ideal.interior i).2.le⟩
  have he := mul_le_mul_of_nonneg_left (cert.node_error i) hL
  exact ⟨hc'.1, (abs_sub_le _ _ _).trans (add_le_add hc'.2 (hn.trans he))⟩

/-- Under a certificate with `0 < n`, `function_accuracy g f error` and `|g| ≤ bound` on
`[-1, 1]`, the products of the stored weights and the callback values have absolute values
summing to at most `(2 + n * weightTolerance) * (bound + error)`. Only values of `g` at the
stored nodes enter, so no Lipschitz term appears. -/
theorem product_mass_le (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n)
    {f : Value → Value} {g : ℝ → ℝ} {bound error : ℝ}
    (hc : function_accuracy g f error) (hB : 0 ≤ bound) (he : 0 ≤ error)
    (hg : fbound (-1) 1 g bound) :
    ∑ i, |Model.toReal (stored.weights i) * Model.toReal (f (stored.nodes i))| ≤
      (2 + n * weightTolerance) * (bound + error) := by
  have hsample (i : Fin n) : |Model.toReal (f (stored.nodes i))| ≤ bound + error := by
    have h := abs_add_le
      (Model.toReal (f (stored.nodes i)) - g (Model.toReal (stored.nodes i)))
      (g (Model.toReal (stored.nodes i)))
    rw [sub_add_cancel] at h
    linarith [(hc _ (cert.node_finite i) (cert.node_mem i)).2,
      hg _ (cert.node_mem i)]
  calc
    _ ≤ ∑ i, |Model.toReal (stored.weights i)| * (bound + error) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hsample i) (abs_nonneg _)
    _ = (∑ i, |Model.toReal (stored.weights i)|) * (bound + error) :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (cert.sum_abs_weights_le hn) (add_nonneg hB he)

/-- Under a certificate with `0 < n`, `function_accuracy g f error`, `|g| ≤ bound` and a
Lipschitz constant `lipschitz` for `g` on `[-1, 1]`, the exact sum of the products of the stored
weights and the callback values is within
`(2 + n * weightTolerance) * (error + lipschitz * nodeTolerance) + n * weightTolerance * bound`
of the ideal rule applied to `g`. No rounding enters. -/
theorem samples_error (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n)
    {f : Value → Value} {g : ℝ → ℝ} {bound error lipschitz : ℝ}
    (hc : function_accuracy g f error) (he : 0 ≤ error) (hL : 0 ≤ lipschitz)
    (hg : fbound (-1) 1 g bound)
    (hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |g x - g y| ≤ lipschitz * |x - y|) :
    |(∑ i, Model.toReal (stored.weights i) * Model.toReal (f (stored.nodes i))) -
        ideal.value g| ≤
      (2 + n * weightTolerance) * (error + lipschitz * nodeTolerance) +
        n * weightTolerance * bound := by
  have hsample (i : Fin n) :
      |Model.toReal (stored.weights i) * Model.toReal (f (stored.nodes i)) -
        ideal.weights i * g (ideal.nodes i)| ≤
      |Model.toReal (stored.weights i)| * (error + lipschitz * nodeTolerance) +
        weightTolerance * bound := by
    have h := weighted_sample_error (cert.weight_error i)
      (cert.callback_at_node hc hL hlip i).2
    have hi := hg _ ⟨(ideal.interior i).1.le, (ideal.interior i).2.le⟩
    exact h.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hi (cert.weight_tolerance_nonneg hn)))
  unfold GaussianRule.value
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |Model.toReal (stored.weights i) * Model.toReal (f (stored.nodes i)) -
        ideal.weights i * g (ideal.nodes i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, (|Model.toReal (stored.weights i)| *
        (error + lipschitz * nodeTolerance) + weightTolerance * bound) :=
      Finset.sum_le_sum (fun i _ => hsample i)
    _ = (∑ i, |Model.toReal (stored.weights i)|) *
        (error + lipschitz * nodeTolerance) + n * weightTolerance * bound := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_right (cert.sum_abs_weights_le hn)
        (add_nonneg he (mul_nonneg hL (cert.node_tolerance_nonneg hn)))) le_rfl

/-- Under the hypotheses of `samples_error` and the range budget at `radius`, the loop result
`integrate_model_f f stored.terms` is finite and within `2n` half-ULPs at `radius` plus the
bound of `samples_error` of the ideal rule applied to `g`. The `2n` half-ULPs cover one
multiplication and one addition per stored term. -/
theorem integrate_model_roundoff_err
    (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n)
    {f : Value → Value} {g : ℝ → ℝ} {bound error lipschitz radius : ℝ}
    (hc : function_accuracy g f error)
    (hB : 0 ≤ bound) (he : 0 ≤ error) (hL : 0 ≤ lipschitz)
    (hg : fbound (-1) 1 g bound)
    (hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |g x - g y| ≤ lipschitz * |x - y|)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hbudget : (2 + n * weightTolerance) * (bound + error) +
      2 * n * Model.halfUlpAt FloatFormat.binary64 radius ≤ radius) :
    Model.isFinite (integrate_model_f f stored.terms) = true ∧
    |Model.toReal (integrate_model_f f stored.terms) - ideal.value g| ≤
      2 * n * Model.halfUlpAt FloatFormat.binary64 radius +
        (2 + n * weightTolerance) * (error + lipschitz * nodeTolerance) +
        n * weightTolerance * bound := by
  have hf : ∀ t ∈ stored.terms,
      Model.isFinite t.1 = true ∧ Model.isFinite (f t.2) = true := by
    intro t ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨cert.weight_finite i, (hc _ (cert.node_finite i) (cert.node_mem i)).1⟩
  have hb :
      (stored.terms.map fun t => |Model.toReal t.1 * Model.toReal (f t.2)|).sum +
        2 * stored.terms.length * Model.halfUlpAt FloatFormat.binary64 radius ≤ radius := by
    simp only [StoredRule.terms, List.map_ofFn, List.sum_ofFn, List.length_ofFn]
    exact (add_le_add (cert.product_mass_le hn hc hB he hg) le_rfl).trans hbudget
  have ha := integrate_error_from_budget f stored.terms radius hmax hf hb
  simp only [StoredRule.terms, List.map_ofFn, List.sum_ofFn, List.length_ofFn] at ha
  refine ⟨ha.1, ?_⟩
  -- Use the exact sum of stored products to separate rounding from table and callback errors.
  have ht := abs_sub_le (Model.toReal (integrate_model_f f stored.terms))
    (∑ i, Model.toReal (stored.weights i) * Model.toReal (f (stored.nodes i)))
    (ideal.value g)
  simpa only [add_assoc] using
    ht.trans (add_le_add ha.2 (cert.samples_error hn hc he hL hg hlip))

/-- Under a certificate with `0 < n`, `function_accuracy g f error`, `|g| ≤ bound` on `[-1, 1]`
and the range budget at `radius`, every intermediate value of the loop is finite
(`Model.ReductionTree.FiniteEval`). -/
theorem finite_integrate_model
    (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n)
    {f : Value → Value} {g : ℝ → ℝ} {bound error radius : ℝ}
    (hc : function_accuracy g f error) (hB : 0 ≤ bound) (he : 0 ≤ error)
    (hg : fbound (-1) 1 g bound)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hbudget : (2 + n * weightTolerance) * (bound + error) +
      2 * n * Model.halfUlpAt FloatFormat.binary64 radius ≤ radius) :
    Model.ReductionTree.FiniteEval (integrationTree f stored.terms) := by
  apply integrationTree_finite_from_budget f stored.terms radius hmax
  · intro t ht
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
    exact ⟨cert.weight_finite i, (hc _ (cert.node_finite i) (cert.node_mem i)).1⟩
  · simp only [StoredRule.terms, List.map_ofFn, List.sum_ofFn, List.length_ofFn]
    exact (add_le_add (cert.product_mass_le hn hc hB he hg) le_rfl).trans hbudget

/-- Under the hypotheses of `integrate_model_roundoff_err`, if `g` is `2n` times continuously
differentiable on `[-1, 1]` and its `2n`-th derivative there is at most `derivativeBound` in
absolute value, the loop result is finite and within the bound of
`integrate_model_roundoff_err` plus `derivativeBound / (2n)! * ∫ nodal ^ 2` of the integral of
`g` over `[-1, 1]`. -/
theorem integrate_model_err
    (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n)
    {f : Value → Value} {g : ℝ → ℝ} {bound error lipschitz radius derivativeBound : ℝ}
    (hc : function_accuracy g f error)
    (hB : 0 ≤ bound) (he : 0 ≤ error) (hL : 0 ≤ lipschitz)
    (hg : fbound (-1) 1 g bound)
    (hlip : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1,
      |g x - g y| ≤ lipschitz * |x - y|)
    (hmax : radius ≤ Model.toReal (Model.posMaxFinite FloatFormat.binary64))
    (hbudget : (2 + n * weightTolerance) * (bound + error) +
      2 * n * Model.halfUlpAt FloatFormat.binary64 radius ≤ radius)
    (hsmooth : ContDiffOn ℝ (2 * n) g (Set.Icc (-1 : ℝ) 1))
    (hderiv : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      |iteratedDerivWithin (2 * n) g (Set.Icc (-1 : ℝ) 1) x| ≤ derivativeBound) :
    Model.isFinite (integrate_model_f f stored.terms) = true ∧
    |Model.toReal (integrate_model_f f stored.terms) - ∫ x in (-1 : ℝ)..1, g x| ≤
      2 * n * Model.halfUlpAt FloatFormat.binary64 radius +
        (2 + n * weightTolerance) * (error + lipschitz * nodeTolerance) +
        n * weightTolerance * bound +
        derivativeBound / (2 * n).factorial *
          polynomialIntegral (-1) 1 (fun _ => 1) continuousOn_const
            ((Lagrange.nodal Finset.univ ideal.nodes) ^ 2) := by
  have hr := cert.integrate_model_roundoff_err hn hc hB he hL hg hlip hmax hbudget
  have hq := ideal.abs_error_le (by norm_num) (fun _ _ => by norm_num) hn hsmooth hderiv
  simp only [mul_one, abs_sub_comm (∫ x in (-1 : ℝ)..1, g x)] at hq
  -- The ideal Gaussian rule connects the floating-point estimate to the real integral.
  exact ⟨hr.1, (abs_sub_le _ (ideal.value g) _).trans (add_le_add hr.2 hq)⟩

end StoredRule.Certificate

end Quadrature.Binary64
