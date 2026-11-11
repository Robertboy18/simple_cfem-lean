/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import FloatLib.Floats.Formats.BinaryInterchange.Reduction.Tree
import Quadrature.Binary64.Constants
import Quadrature.Binary64.Roundoff

/-!
# Binary64 quadrature in the C evaluation order

This module restates `integrate_model_f` and `testfun_f` of simple_cfem's `proof/quadmodel.v`,
the functional model of the loop of `integrate` in `src/quadrules.c`. `integrate_model_f` performs
one rounded multiplication and one rounded addition per sample, starting from positive zero, in
the order of the C loop. It uses FloatLib's executable IEEE model.

## Main definitions

* `integrate_model_f f terms`: the loop over a list of (weight, node) pairs.
* `testfun_f cosine`: the callback `0.5 * (1 - x) * cosine x` for a given binary64 cosine.
* `integrationTree f terms`: the loop as a FloatLib reduction tree.

## Main results

* `integrationTree_eval`: evaluating the tree gives `integrate_model_f f terms`.
* `integrate_roundoff_bound`: if every node of the tree is finite, the result is within
  FloatLib's `errorBudget` of the exact sum of the rounded products.
* `sample_error`: the error of one rounded weighted sample.

## Implementation notes

Compared with `quadmodel.v`: the Rocq `integrate_model_f` folds `BPLUS s (BMULT w (f x))` over
the node indices, starting from `pos_zero`; ours maps the multiplications over a list of terms
and then folds the additions. Both perform the same operations, since no product depends on the
accumulator. The Rocq `testfun_f` uses VSTlib's binary64 cosine; ours takes the cosine as an
argument.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`src/quadrules.c`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/src/quadrules.c):
  `integrate` and `testfun`.
* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`proof/quadmodel.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/quadmodel.v):
  `integrate_model_f` and `testfun_f`.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange FloatLib.Numerics

/-- The loop of the original C program: for each (weight, node) pair, multiply the weight by
`f node` and add the product to the accumulator, which starts at positive zero. -/
def integrate_model_f (f : Value → Value) (terms : List (Value × Value)) : Value :=
  (terms.map fun term => Model.mul term.1 (f term.2)).foldl Model.add zero

/-- The callback `0.5 * (1 - x) * cosine x`, with the left-to-right parenthesization of the
original C program. -/
def testfun_f (cosine : Value → Value) (x : Value) : Value :=
  Model.mul (Model.mul half (Model.sub one x)) (cosine x)

/-- The two-point rule as the loop sees it: unit weights at `leftNode` and `rightNode`. -/
def twoPointTerms : List (Value × Value) := [(one, leftNode), (one, rightNode)]

/-- Append additions to an accumulator tree in loop order. -/
def accumulationTree (initial : ReductionTree Value) : List Value → ReductionTree Value
  | [] => initial
  | x :: xs => accumulationTree (.node initial (.leaf x)) xs

/-- Evaluating an accumulation tree is a left fold, for any operation and leaf decoder. -/
theorem accumulationTree_eval_with {α : Type*}
    (op : α → α → α) (decode : Value → α)
    (initial : ReductionTree Value) (xs : List Value) :
    (accumulationTree initial xs).eval op decode =
      (xs.map decode).foldl op (initial.eval op decode) := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih => exact ih (.node initial (.leaf x))

/-- Evaluating the accumulation tree with `Model.add` is the left fold of `Model.add` over the
appended values, starting from the value of the initial tree. -/
theorem accumulationTree_eval (initial : ReductionTree Value) (xs : List Value) :
    (accumulationTree initial xs).eval Model.add id =
      xs.foldl Model.add (initial.eval Model.add id) := by
  simpa only [List.map_id] using accumulationTree_eval_with Model.add id initial xs

/-- The leaves of the accumulation tree are the initial leaves followed by the appended list. -/
theorem accumulationTree_leaves (initial : ReductionTree Value) (xs : List Value) :
    (accumulationTree initial xs).leaves = initial.leaves ++ xs := by
  induction xs generalizing initial with
  | nil => simp [accumulationTree]
  | cons x xs ih =>
    simp [accumulationTree, ih, ReductionTree.leaves, List.append_assoc]

/-- The execution tree includes the loop's initial zero and every weighted sample. -/
def integrationTree (f : Value → Value) (terms : List (Value × Value)) :
    ReductionTree Value :=
  accumulationTree (.leaf zero) (terms.map fun term => Model.mul term.1 (f term.2))

/-- Evaluating `integrationTree f terms` with `Model.add` gives `integrate_model_f f terms`. -/
theorem integrationTree_eval (f : Value → Value) (terms : List (Value × Value)) :
    (integrationTree f terms).eval Model.add id = integrate_model_f f terms :=
  accumulationTree_eval _ _

/-- The real value of positive zero is 0. -/
theorem zero_toReal : Model.toReal zero = 0 := by
  have hz : Model.toDyadic? zero = some ⟨false, 0, 0⟩ := by decide
  rw [Model.toReal_eq, hz]
  norm_num [FloatLib.Numerics.Dyadic.toReal,
    FloatLib.Numerics.Dyadic.signedSignificand]

/-- If every node of the integration tree is finite, the result differs from the exact sum of
the rounded products by at most FloatLib's `errorBudget`, the sum of half-ULPs at the
additions performed. -/
theorem integrate_roundoff_bound (f : Value → Value) (terms : List (Value × Value))
    (hfinite : Model.ReductionTree.FiniteEval (integrationTree f terms)) :
    |Model.toReal (integrate_model_f f terms) -
      (terms.map fun term => Model.toReal (Model.mul term.1 (f term.2))).sum| ≤
      Model.ReductionTree.errorBudget (integrationTree f terms) := by
  have h := Model.ReductionTree.abs_toReal_eval_sub_sum_le
    (integrationTree f terms) (by decide) hfinite
  rw [integrationTree_eval] at h
  simpa [integrationTree, accumulationTree_leaves,
    ReductionTree.leaves, List.map_map, Function.comp_def, zero_toReal] using h

/-- If the stored weight is within `ew` of the ideal weight and the callback value within `ef`
of the ideal sample, the rounded product is within one half-ULP plus `|weight|·ef + ew·|sample|`
of the ideal product. -/
theorem sample_error (weight node : Value) (f : Value → Value)
    (idealWeight idealSample ew ef : ℝ)
    (hmfinite : Model.isFinite (Model.mul weight (f node)) = true)
    (hw : |Model.toReal weight - idealWeight| ≤ ew)
    (hf : |Model.toReal (f node) - idealSample| ≤ ef) :
    |Model.toReal (Model.mul weight (f node)) - idealWeight * idealSample| ≤
      Model.halfUlpAt FloatFormat.binary64 (Model.toReal weight * Model.toReal (f node)) +
        |Model.toReal weight| * ef + ew * |idealSample| := by
  exact rounded_weighted_sample_error hw hf
    (Model.abs_toReal_mul_sub_le weight (f node) (by decide) hmfinite)

end Quadrature.Binary64
