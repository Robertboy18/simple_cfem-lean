/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Quadrature.Binary64.Program
import CAS.Continuum.Quadrature.Legendre.Identification
import CAS.Continuum.Quadrature.Legendre.Polynomials
import Quadrature.Rules.Constants

/-!
# Stored rules and their certificates

This module restates the table hypotheses of section `FLOAT` of simple_cfem's
`proof/quadmodel_accuracy.v` as a certificate. A stored rule is a table of binary64 weights and
nodes in accumulation order. A
stored-rule certificate for it, against an ideal Legendre rule, consists of
finiteness of every table entry, decoded nodes in `[-1,1]`, and node and weight
error bounds `nodeTolerance` and `weightTolerance` against the ideal rule. We
certify the C program's tables for one to four nodes. Their entries are within `10⁻¹⁶` of the
ideal nodes and weights; the default weight tolerance `5·10⁻¹⁶` is the uniform one of all ten
stored tables (`Quadrature.Binary64.StoredRule.table_certificate`), which the 15-digit weights
of orders five to ten need.

## Main definitions

* `StoredRule n`, `StoredRule.terms`: a stored `n`-point rule and its (weight, node) list.
* `StoredRule.Certificate`: a stored-rule certificate against an ideal rule.
* `oneStored`, `twoStored`, `threeStored`, `fourStored`: the C tables for one to four nodes.

## Main results

* `oneStored_certificate` to `fourStored_certificate`: each of these tables is certified
  against its Gauss–Legendre rule with the default tolerances.

## Implementation notes

Compared with `quadmodel_accuracy.v`: `StoredRule.Certificate` collects the hypotheses
`gauss_pt_f_range`, `gauss_pts_accuracy` and `gauss_wts_accuracy` of section `FLOAT`, where both
tolerances are `default_rel`, which is `2⁻⁵³` in binary64; we make them parameters.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`src/quadrules.c`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/src/quadrules.c):
  the tables `gauss_pts` and `gauss_wts`.
* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/quadmodel_accuracy.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/quadmodel_accuracy.v):
  section `FLOAT`.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange
open CAS.Continuum

/-- A table of `n` binary64 weights and `n` nodes, indexed in accumulation order. -/
structure StoredRule (n : ℕ) where
  weights : Fin n → Value
  nodes : Fin n → Value

namespace StoredRule

/-- The (weight, node) list in accumulation order, as `integrate_model_f` consumes it. -/
def terms {n : ℕ} (stored : StoredRule n) : List (Value × Value) :=
  List.ofFn fun i => (stored.weights i, stored.nodes i)

/-- A stored-rule certificate: every entry is finite, every decoded node lies in `[-1,1]`, and
every node and weight is within `nodeTolerance` and `weightTolerance` of the ideal rule. The
tolerances default to `1/10^16` and `5/10^16`, which orders one to four meet; order six misses
the node tolerance (`six_node_exceeds_tighter_tolerance`). -/
structure Certificate {n : ℕ} (stored : StoredRule n) (ideal : Legendre.Rule n)
    (nodeTolerance : ℝ := 1 / 10 ^ 16) (weightTolerance : ℝ := 5 / 10 ^ 16) : Prop where
  weight_finite : ∀ i, Model.isFinite (stored.weights i) = true
  node_finite : ∀ i, Model.isFinite (stored.nodes i) = true
  node_mem : ∀ i, Model.toReal (stored.nodes i) ∈ Set.Icc (-1 : ℝ) 1
  node_error : ∀ i, |Model.toReal (stored.nodes i) - ideal.nodes i| ≤ nodeTolerance
  weight_error : ∀ i,
    |Model.toReal (stored.weights i) - ideal.weights i| ≤ weightTolerance

/-- A certificate for a rule with at least one node forces `0 ≤ nodeTolerance`. -/
theorem Certificate.node_tolerance_nonneg {n : ℕ} {stored : StoredRule n}
    {ideal : Legendre.Rule n} {nodeTolerance weightTolerance : ℝ}
    (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n) :
    0 ≤ nodeTolerance :=
  (abs_nonneg _).trans (cert.node_error ⟨0, hn⟩)

/-- A certificate for a rule with at least one node forces `0 ≤ weightTolerance`. -/
theorem Certificate.weight_tolerance_nonneg {n : ℕ} {stored : StoredRule n}
    {ideal : Legendre.Rule n} {nodeTolerance weightTolerance : ℝ}
    (cert : stored.Certificate ideal nodeTolerance weightTolerance) (hn : 0 < n) :
    0 ≤ weightTolerance :=
  (abs_nonneg _).trans (cert.weight_error ⟨0, hn⟩)

end StoredRule

/-- The stored one-point rule: weight `2` at node `0`. -/
def oneStored : StoredRule 1 := ⟨![two], ![zero]⟩
/-- The stored two-point rule: unit weights at the stored nodes for `∓1/√3`. -/
def twoStored : StoredRule 2 := ⟨![one, one], ![leftNode, rightNode]⟩
/-- The stored three-point rule: the C outer weight, the middle weight `8/9`, and the stored
nodes for `-√(3/5)`, `0`, `√(3/5)`. -/
def threeStored : StoredRule 3 :=
  ⟨![threeOuterWeight, threeMiddleWeight, threeOuterWeight],
    ![negativeThreeNode64, zero, threeNode64]⟩
/-- The stored four-point rule: outer, inner, inner, outer weights and the four stored nodes in
increasing order. -/
def fourStored : StoredRule 4 :=
  ⟨![fourOuterWeight, fourInnerWeight, fourInnerWeight, fourOuterWeight],
    ![negativeFourOuter64, negativeFourInner64, fourInner64, fourOuter64]⟩

/-- The one-point table is certified against `Legendre.oneGaussian` with the default tolerances.
Both entries are exact. -/
theorem oneStored_certificate : oneStored.Certificate Legendre.oneGaussian where
  weight_finite := by decide
  node_finite := by decide
  node_mem := by intro i; fin_cases i; norm_num [oneStored, zero_toReal]
  node_error := by
    intro i
    fin_cases i
    norm_num [oneStored, Legendre.oneGaussian, zero_toReal]
  weight_error := by
    intro i
    fin_cases i
    norm_num [oneStored, Legendre.oneGaussian, two_toReal]

/-- The two-point table is certified against `Legendre.twoGaussian` with the default tolerances,
using `leftNode_error` and `rightNode_error`. -/
theorem twoStored_certificate : twoStored.Certificate Legendre.twoGaussian where
  weight_finite := by decide
  node_finite := by decide
  node_mem := by
    intro i
    fin_cases i <;> norm_num [twoStored, leftNode_toReal, rightNode_toReal]
  node_error := by
    intro i
    fin_cases i
    · change |Model.toReal leftNode - -Legendre.twoNode| ≤ (1 / 10 ^ 16 : ℝ)
      rw [Legendre.twoNode_eq_one_div_sqrt]
      exact leftNode_error
    · change |Model.toReal rightNode - Legendre.twoNode| ≤ (1 / 10 ^ 16 : ℝ)
      rw [Legendre.twoNode_eq_one_div_sqrt]
      exact rightNode_error
  weight_error := by
    intro i
    fin_cases i <;> norm_num [twoStored, Legendre.twoGaussian, one_toReal]

/-- The three-point table is certified against `Legendre.threeGaussian` with the default
tolerances. -/
theorem threeStored_certificate : threeStored.Certificate Legendre.threeGaussian where
  weight_finite := by decide
  node_finite := by decide
  node_mem := by
    intro i
    fin_cases i <;>
      norm_num [threeStored, negativeThreeNode64_toReal, threeNode64_toReal, zero_toReal]
  node_error := by
    intro i
    fin_cases i
    · exact negativeThreeNode64_error
    · norm_num [threeStored, Legendre.threeGaussian, zero_toReal]
    · exact threeNode64_error
  weight_error := by
    intro i
    fin_cases i
    · exact threeOuterWeight_error.trans (by norm_num)
    · exact threeMiddleWeight_error.trans (by norm_num)
    · exact threeOuterWeight_error.trans (by norm_num)

/-- The four-point table is certified against `Legendre.fourGaussian` with the default
tolerances. -/
theorem fourStored_certificate : fourStored.Certificate Legendre.fourGaussian where
  weight_finite := by decide
  node_finite := by decide
  node_mem := by
    intro i
    fin_cases i <;>
      norm_num [fourStored, negativeFourOuter64_toReal, negativeFourInner64_toReal,
        fourOuter64_toReal, fourInner64_toReal]
  node_error := by
    intro i
    fin_cases i
    · exact negativeFourOuter64_error
    · exact negativeFourInner64_error
    · exact fourInner64_error
    · exact fourOuter64_error
  weight_error := by
    intro i
    fin_cases i
    · exact fourOuterWeight_error.trans (by norm_num)
    · exact fourInnerWeight_error.trans (by norm_num)
    · exact fourInnerWeight_error.trans (by norm_num)
    · exact fourOuterWeight_error.trans (by norm_num)

end Quadrature.Binary64
