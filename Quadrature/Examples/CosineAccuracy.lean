/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Quadrature.Examples.CosineCallback

/-!
# Accuracy of the two-point binary64 program

This module restates, for the functional model, the accuracy of the C function `integrate_testfun`
of `src/quadrules.c`, which simple_cfem specifies in `proof/C/spec_quadrules_highlevel.v`. The
function approximates the integral of `(1 - x) cos x / 2` over `[-1, 1]` by the two-point rule in
binary64. We bound the error of its functional model
`integrate_model_f (testfun_f cosine) twoPointTerms` under one hypothesis on the cosine,
`CosineContract`: the cosine call is finite and within `10⁻¹⁵` of the exact cosine at the two stored
nodes. The result is then finite and within `2·10⁻¹⁴` of `cos(1/√3)`, so within `0.00356` of the
integral `sin 1`.

## Main definitions

* `CosineContract`: the accuracy hypothesis on the cosine at the two nodes.

## Main results

* `two_point_roundoff`: the program's result is finite and within `2·10⁻¹⁴` of `cos(1/√3)`.
* `two_point_program_accuracy`: the result is finite and within `0.00356` of the integral.

## How it works

We follow the program one operation at a time. At each node, `testfun_at_node` adds up the cosine
error, the three roundings inside the callback and the change of the integrand caused by the stored
node's displacement of at most `10⁻¹⁶` from `±1/√3`, for at most `6·10⁻¹⁵`. The two multiplications
by the unit weights and the two additions, the first of them with the initial zero, cost at most
`10⁻¹⁵` each by the radius-8 lemmas of `Quadrature.Binary64.BoundedRoundoff`, which also make every
operation finite. The exact two-point sum is `cos(1/√3)`, and the rational bounds of
`Quadrature.Example` put it within `0.0035596` of `sin 1`.

## Implementation notes

Compared with `spec_quadrules_highlevel.v`: the Rocq specification `integrate_testfun_spec` states
the bound `0.00425`. Its proof calls the specification of `integrate`, which `integrate_model_err`
justifies: the rounding error of the loop plus the quadrature error bound `424/100000` of
`error_1_0_2`. The callback's error comes from `testfun_function_accuracy`, which VCFloat derives.
We compare the program with the exact two-point sum instead, so no derivative bound enters and what
remains is the true error of the rule.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`src/quadrules.c`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/src/quadrules.c):
  `testfun` and `integrate_testfun`.
* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/quadmodel_accuracy.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/quadmodel_accuracy.v):
  `integrate_model_err`, `testfun_function_accuracy` and `testfun_quadrature_error_bound`.
* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/C/spec_quadrules_highlevel.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/C/spec_quadrules_highlevel.v):
  `integrate_spec` and `integrate_testfun_spec`.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange
open MeasureTheory

/-- The cosine call is finite and within `10⁻¹⁵` of `Real.cos` at the two inputs `leftNode` and
`rightNode`, the only arguments the two-point program passes to it. -/
def CosineContract (cosine : Value → Value) : Prop :=
  ∀ x, x = leftNode ∨ x = rightNode →
    Model.isFinite (cosine x) = true ∧
    |Model.toReal (cosine x) - Real.cos (Model.toReal x)| ≤ (1 / 10 ^ 15 : ℝ)

/-- If a stored node is within `10⁻¹⁶` of the ideal node and the cosine is finite and accurate
to `10⁻¹⁵` there, then `testfun_f` is finite and within `6·10⁻¹⁵` of the ideal integrand
value. -/
theorem testfun_at_node (cosine : Value → Value) {node : Value} {ideal : ℝ}
    (hnode : Model.isFinite node = true) (hbound : |Model.toReal node| ≤ 1)
    (hdisplacement : |Model.toReal node - ideal| ≤ (1 / 10 ^ 16 : ℝ))
    (hcfinite : Model.isFinite (cosine node) = true)
    (hcerror : |Model.toReal (cosine node) - Real.cos (Model.toReal node)| ≤
      (1 / 10 ^ 15 : ℝ)) :
    Model.isFinite (testfun_f cosine node) = true ∧
    |Model.toReal (testfun_f cosine node) - Example.testfun_r ideal| ≤
      (6 / 10 ^ 15 : ℝ) := by
  have hf := testfun_error cosine node hnode hbound hcfinite hcerror
  refine ⟨hf.1, ?_⟩
  have hn := integrand_node_error hbound hdisplacement
  have ht := abs_sub_le (Model.toReal (testfun_f cosine node))
    (Example.testfun_r (Model.toReal node)) (Example.testfun_r ideal)
  linarith

/-- If y is finite and within `6·10⁻¹⁵` of an ideal of magnitude at most 1, then `one * y` is
finite, within `7·10⁻¹⁵` of the ideal, and of magnitude at most 2. -/
theorem unit_weight_sample (y : Value) (ideal : ℝ)
    (hy : Model.isFinite y = true) (hi : |ideal| ≤ 1)
    (he : |Model.toReal y - ideal| ≤ (6 / 10 ^ 15 : ℝ)) :
    Model.isFinite (Model.mul one y) = true ∧
    |Model.toReal (Model.mul one y) - ideal| ≤ (7 / 10 ^ 15 : ℝ) ∧
    |Model.toReal (Model.mul one y)| ≤ 2 := by
  have hyb : |Model.toReal y| ≤ 2 := by
    have he' := abs_le.mp he
    have hi' := abs_le.mp hi
    rw [abs_le]
    constructor <;> linarith
  have hm := mul_small one y one_finite hy (by
    rw [one_toReal, one_mul]
    linarith)
  rw [one_toReal, one_mul] at hm
  have hb : |Model.toReal (Model.mul one y) - ideal| ≤ (7 / 10 ^ 15 : ℝ) := by
    have ht := abs_sub_le (Model.toReal (Model.mul one y)) (Model.toReal y) ideal
    linarith [hm.2]
  refine ⟨hm.1, hb, ?_⟩
  have he' := abs_le.mp hb
  have hi' := abs_le.mp hi
  rw [abs_le]
  constructor <;> linarith

/-- If both callback values are finite and within `6·10⁻¹⁵` of ideals of magnitude at most 1,
the two-point loop is finite and within `2·10⁻¹⁴` of the ideal sum. The two multiplications
and the two additions, including the one with the initial zero, are each bounded. -/
theorem two_point_accumulation (f : Value → Value) (u v : ℝ)
    (hl : Model.isFinite (f leftNode) = true)
    (hr : Model.isFinite (f rightNode) = true)
    (hu : |u| ≤ 1) (hv : |v| ≤ 1)
    (hel : |Model.toReal (f leftNode) - u| ≤ (6 / 10 ^ 15 : ℝ))
    (her : |Model.toReal (f rightNode) - v| ≤ (6 / 10 ^ 15 : ℝ)) :
    Model.isFinite (integrate_model_f f twoPointTerms) = true ∧
    |Model.toReal (integrate_model_f f twoPointTerms) - (u + v)| ≤ (2 / 10 ^ 14 : ℝ) := by
  have hpl := unit_weight_sample (f leftNode) u hl hu hel
  have hpr := unit_weight_sample (f rightNode) v hr hv her
  have ha := add_small zero (Model.mul one (f leftNode)) zero_finite hpl.1 (by
    rw [zero_toReal, zero_add]
    linarith [hpl.2.2])
  rw [zero_toReal, zero_add] at ha
  have hab : |Model.toReal (Model.add zero (Model.mul one (f leftNode)))| ≤ 3 := by
    have h₁ := abs_le.mp ha.2
    have h₂ := abs_le.mp hpl.2.2
    rw [abs_le]
    constructor <;> linarith
  have hs := add_small (Model.add zero (Model.mul one (f leftNode)))
    (Model.mul one (f rightNode)) ha.1 hpr.1 (by
      exact (abs_add_le _ _).trans (by linarith [hpr.2.2]))
  change Model.isFinite (integrate_model_f f twoPointTerms) = true ∧
    |Model.toReal (integrate_model_f f twoPointTerms) -
      (Model.toReal (Model.add zero (Model.mul one (f leftNode))) +
        Model.toReal (Model.mul one (f rightNode)))| ≤ (1 / 10 ^ 15 : ℝ) at hs
  refine ⟨hs.1, ?_⟩
  have h₁ := abs_le.mp hs.2
  have h₂ := abs_le.mp ha.2
  have h₃ := abs_le.mp hpl.2.1
  have h₄ := abs_le.mp hpr.2.1
  rw [abs_le]
  constructor <;> linarith

/-- Under `CosineContract` the two-point program is finite and within `2·10⁻¹⁴` of the exact
two-point sum, which is `cos(1/√3)`. -/
theorem two_point_roundoff (cosine : Value → Value) (hc : CosineContract cosine) :
    Model.isFinite (integrate_model_f (testfun_f cosine) twoPointTerms) = true ∧
    |Model.toReal (integrate_model_f (testfun_f cosine) twoPointTerms) -
      Real.cos (1 / Real.sqrt 3)| ≤ (2 / 10 ^ 14 : ℝ) := by
  have hcl := hc leftNode (Or.inl rfl)
  have hcr := hc rightNode (Or.inr rfl)
  have hl := testfun_at_node cosine leftNode_finite
    (by rw [leftNode_toReal]; norm_num) leftNode_error hcl.1 hcl.2
  have hr := testfun_at_node cosine rightNode_finite
    (by rw [rightNode_toReal]; norm_num) rightNode_error hcr.1 hcr.2
  have hn : |(1 / Real.sqrt (3 : ℝ))| ≤ 1 := by
    have hsq : (1 / Real.sqrt (3 : ℝ)) ^ 2 = (1 / 3 : ℝ) := by
      rw [div_pow, Real.sq_sqrt (by norm_num)]
      norm_num
    rw [abs_le]
    constructor <;> nlinarith
  have h := two_point_accumulation (testfun_f cosine)
    (Example.testfun_r (-(1 / Real.sqrt 3))) (Example.testfun_r (1 / Real.sqrt 3))
    hl.1 hr.1 (testfun_fbound _ (abs_le.mp (by simpa using hn)))
    (testfun_fbound _ (abs_le.mp hn))
    hl.2 hr.2
  rwa [Example.two_point_eq] at h

/-- Under `CosineContract` the two-point program is finite and within `0.00356` of the integral
of the integrand over `[-1, 1]`; `|cos(1/√3) − sin 1|` is about `0.003560`. -/
theorem two_point_program_accuracy (cosine : Value → Value) (hc : CosineContract cosine) :
    Model.isFinite (integrate_model_f (testfun_f cosine) twoPointTerms) = true ∧
    |Model.toReal (integrate_model_f (testfun_f cosine) twoPointTerms) -
      ∫ x in (-1 : ℝ)..1, Example.testfun_r x| ≤ (356 / 100000 : ℝ) := by
  have h := two_point_roundoff cosine hc
  refine ⟨h.1, ?_⟩
  rw [Example.integral_eq]
  have he : |Real.cos (1 / Real.sqrt 3) - Real.sin 1| ≤ (35596 / 10000000 : ℝ) := by
    rw [abs_le]
    constructor <;>
      linarith [Example.sin_one_upper, Example.cos_node_lower,
        Example.sin_one_lower, Example.cos_node_upper]
  have ht := abs_sub_le (Model.toReal (integrate_model_f (testfun_f cosine) twoPointTerms))
    (Real.cos (1 / Real.sqrt 3)) (Real.sin 1)
  linarith [h.2]

end Quadrature.Binary64
