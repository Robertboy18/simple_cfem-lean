/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Quadrature.Binary64.BoundedRoundoff
import Quadrature.Examples.TwoPointCosine
import Quadrature.Legendre.Bounds
import Quadrature.Rules.Accuracy

/-!
# The example callback and node perturbation

This module restates the bounds on the callback `testfun` of simple_cfem's
`proof/quadmodel_accuracy.v`. The callback of `src/quadrules.c` computes `0.5 * (1 - x) * cos(x)`
with one subtraction and two multiplications. We bound the real function `testfun_r` and its
derivative on `[-1, 1]` and its sensitivity to node displacement. Then we prove that the three
operations are finite and that the callback result is within `5·10⁻¹⁵` of `testfun_r`. The cosine
hypothesis is stated at the binary64 input `x` that the callback passes to the cosine, so no
separate rounding of the argument is needed.

## Main results

* `testfun_fbound`, `testfun_deriv_bound`: `|testfun_r| ≤ testfun_fb` and
  `|testfun_r'| ≤ testfun_d` on `[-1, 1]`, where `testfun_fb = testfun_d = 1`.
* `integrand_node_error`: moving the argument by `δ` moves `testfun_r` by at most `2δ`.
* `testfun_error`: the binary64 callback is finite and within `5·10⁻¹⁵` of `testfun_r`.
* `testfun_function_accuracy`: the same bound in the form `function_accuracy testfun_r`.

## Implementation notes

Compared with `quadmodel_accuracy.v`: there T. Saikawa proved the two bounds for a MathComp copy
`testfun_mcr` of the function and moved them to `testfun_r` with `testfun_rE`. The derivative bound
splits on the sign of `x`. Ours works with `testfun_r` directly, and FloatLib's `interval` tactic
bounds the derivative on all of `[-1, 1]`. A comment there observes that the true bound on the
derivative is about `0.6`; both developments use `1`. The Rocq accuracy constant `testfun_f_acc`
comes from VCFloat's automatic roundoff analysis of the callback with VSTlib's binary64 cosine. Our
`testfun_f` takes the cosine as an argument, so we bound the three rounded operations by hand and
make the cosine's error a hypothesis.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/quadmodel_accuracy.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/quadmodel_accuracy.v):
  sections `testfun_mcr`, `stdlib_testfun` and `VCFLOAT`.
* A. W. Appel and A. E. Kellison, *VCFloat2: Floating-point error analysis in Coq*, Proceedings
  of the 13th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2024),
  ACM, 2024, 14–29, [doi:10.1145/3636501.3636953](https://doi.org/10.1145/3636501.3636953).
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange

/-- The bound `1` on `|testfun_r|` over `[-1, 1]`. -/
noncomputable def testfun_fb : ℝ := 1

/-- `|testfun_r x| ≤ testfun_fb` on `[-1, 1]`, since `|(1 - x) / 2| ≤ 1` and `|cos x| ≤ 1`. -/
theorem testfun_fbound : fbound (-1) 1 Example.testfun_r testfun_fb := by
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := hx
  have hw : |(1 / 2 : ℝ) * (1 - x)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith
  rw [Example.testfun_r, abs_mul, testfun_fb]
  exact (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one x) (abs_nonneg _)).trans
    (by simpa using hw)

/-- The bound `1` on the derivative of `testfun_r` over `[-1, 1]`. -/
noncomputable def testfun_d : ℝ := 1

private theorem testfun_r_hasDerivAt (x : ℝ) :
    HasDerivAt Example.testfun_r (-(Real.cos x + (1 - x) * Real.sin x) / 2) x :=
  ((((hasDerivAt_id' x).const_sub 1).const_mul (1 / 2 : ℝ)).fun_mul
    (Real.hasDerivAt_cos x)).congr_deriv (by ring)

/-- `testfun_r` is differentiable on `[-1, 1]`, with `|testfun_r'| ≤ testfun_d` there. -/
theorem testfun_deriv_bound : deriv_bound (-1) 1 Example.testfun_r testfun_d := by
  intro x hx
  obtain ⟨hx₁, hx₂⟩ := hx
  have h := testfun_r_hasDerivAt x
  refine ⟨h.differentiableAt, ?_⟩
  have hc : 0 ≤ Real.cos x :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.two_le_pi], by linarith [Real.two_le_pi]⟩
  have hl := mul_nonneg (sub_nonneg.mpr hx₂)
    (by linarith [Real.neg_one_le_sin x] : (0 : ℝ) ≤ 1 + Real.sin x)
  rw [h.deriv, testfun_d]
  interval

/-- If |x| ≤ 1 and |x − y| ≤ δ then the integrand values at x and y differ by at most 2δ.
Cosine is 1-Lipschitz and the linear factor moves by δ/2. -/
theorem integrand_node_error {x y δ : ℝ} (hx : |x| ≤ 1) (hxy : |x - y| ≤ δ) :
    |Example.testfun_r x - Example.testfun_r y| ≤ 2 * δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans hxy
  have hw : |(1 / 2 : ℝ) * (1 - x)| ≤ 1 := by
    have hx' := abs_le.mp hx
    rw [abs_le]
    constructor <;> linarith
  have hwd : |(1 / 2 : ℝ) * (1 - x) - (1 / 2) * (1 - y)| ≤ δ / 2 := by
    have he : (1 / 2 : ℝ) * (1 - x) - (1 / 2) * (1 - y) = -(x - y) / 2 := by ring
    rw [he, abs_div, abs_neg]
    norm_num
    linarith
  have h := weighted_sample_error hwd ((Real.abs_cos_sub_cos_le x y).trans hxy)
  change |Example.testfun_r x - Example.testfun_r y| ≤
    |(1 / 2 : ℝ) * (1 - x)| * δ + δ / 2 * |Real.cos y| at h
  have ht := mul_le_mul_of_nonneg_right hw hδ
  have hc := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one y) (by positivity : 0 ≤ δ / 2)
  nlinarith

/-- If x is finite with |x| ≤ 1 and `cosine x` is finite and within `10⁻¹⁵` of cos x, then
`testfun_f cosine x` is finite and within `5·10⁻¹⁵` of `testfun_r x`. Finiteness of the
subtraction and both multiplications is a conclusion, from the radius-8 lemmas. -/
theorem testfun_error (cosine : Value → Value) (x : Value)
    (hx : Model.isFinite x = true) (hbound : |Model.toReal x| ≤ 1)
    (hcfinite : Model.isFinite (cosine x) = true)
    (hcerror : |Model.toReal (cosine x) - Real.cos (Model.toReal x)| ≤
      (1 / 10 ^ 15 : ℝ)) :
    Model.isFinite (testfun_f cosine x) = true ∧
    |Model.toReal (testfun_f cosine x) - Example.testfun_r (Model.toReal x)| ≤
      (5 / 10 ^ 15 : ℝ) := by
  have hx' := abs_le.mp hbound
  have hsub := sub_small one x (by decide) hx (by
    rw [one_toReal, abs_le]
    constructor <;> linarith)
  rw [one_toReal] at hsub
  have hsabs : |Model.toReal (Model.sub one x)| ≤ 3 := by
    have h := abs_le.mp hsub.2
    rw [abs_le]
    constructor <;> linarith
  have hhalf := mul_small half (Model.sub one x) (by decide) hsub.1 (by
    rw [half_toReal, abs_mul]
    norm_num
    linarith)
  rw [half_toReal] at hhalf
  have hhabs : |Model.toReal (Model.mul half (Model.sub one x))| ≤ 2 := by
    have hh := abs_le.mp hhalf.2
    have hs := abs_le.mp hsabs
    rw [abs_le]
    constructor <;> linarith
  have hcabs : |Model.toReal (cosine x)| ≤ 2 := by
    have htri := abs_add_le
      (Model.toReal (cosine x) - Real.cos (Model.toReal x)) (Real.cos (Model.toReal x))
    rw [sub_add_cancel] at htri
    linarith [Real.abs_cos_le_one (Model.toReal x)]
  have hmul := mul_small (Model.mul half (Model.sub one x)) (cosine x)
    hhalf.1 hcfinite (by
      rw [abs_mul]
      nlinarith [abs_nonneg (Model.toReal (Model.mul half (Model.sub one x))),
        abs_nonneg (Model.toReal (cosine x))])
  refine ⟨hmul.1, ?_⟩
  have hherror :
      |Model.toReal (Model.mul half (Model.sub one x)) -
        (1 / 2 : ℝ) * (1 - Model.toReal x)| ≤ (2 / 10 ^ 15 : ℝ) := by
    have h₁ := abs_le.mp hhalf.2
    have h₂ := abs_le.mp hsub.2
    rw [abs_le]
    constructor <;> linarith
  have h := rounded_weighted_sample_error hherror hcerror hmul.2
  change |Model.toReal (testfun_f cosine x) - Example.testfun_r (Model.toReal x)| ≤
    1 / 10 ^ 15 + |Model.toReal (Model.mul half (Model.sub one x))| * (1 / 10 ^ 15) +
      (2 / 10 ^ 15) * |Real.cos (Model.toReal x)| at h
  nlinarith [Real.abs_cos_le_one (Model.toReal x)]

/-- If `cosine` is finite and within `10⁻¹⁵` of `cos` on every finite input in `[-1, 1]`, then
`testfun_f cosine` is within `5·10⁻¹⁵` of `testfun_r` in the sense of `function_accuracy`. -/
theorem testfun_function_accuracy (cosine : Value → Value)
    (hcos : ∀ x, Model.isFinite x = true → Model.toReal x ∈ Set.Icc (-1 : ℝ) 1 →
      Model.isFinite (cosine x) = true ∧
        |Model.toReal (cosine x) - Real.cos (Model.toReal x)| ≤ (1 / 10 ^ 15 : ℝ)) :
    function_accuracy Example.testfun_r (testfun_f cosine) (5 / 10 ^ 15) := by
  intro x hx hmem
  obtain ⟨hcfinite, hcerror⟩ := hcos x hx hmem
  exact testfun_error cosine x hx (abs_le.mpr ⟨hmem.1, hmem.2⟩) hcfinite hcerror

end Quadrature.Binary64
