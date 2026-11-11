/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import FloatLib.Floats.Formats.BinaryInterchange.Format.Catalog
import FloatLib.Floats.Formats.BinaryInterchange.Model.RealSemantics
import Quadrature.Examples.TwoPointCosine

/-!
# Binary64 constants from the original C program

The original C program stores the two-point nodes `∓1/√3` as the decimal literals
`∓0.5773502691896257`. Their binary64 values `leftNode` and `rightNode` have the bit patterns
`0xbfe279a74590331c` and `0x3fe279a74590331c`. We decode them with FloatLib to the dyadics
`∓1300077228592327 / 2⁵¹` and prove that each lies within `10⁻¹⁶` of the exact node. `one`,
`half` and `zero` are the other constants that the callback and the loop use, and `Value` is
FloatLib's binary64 model.

## Main results

* `leftNode_toReal`, `rightNode_toReal`: the exact values of the stored nodes.
* `leftNode_error`, `rightNode_error`: each stored node is within `10⁻¹⁶` of `∓1/√3`.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`,
  [`src/quadrules.c`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/src/quadrules.c):
  the two-point entries of `gauss_pts`.
-/

namespace Quadrature.Binary64

open FloatLib.Floats.Formats.BinaryInterchange

/-- FloatLib's binary64 model, the type of every floating-point value in this development. -/
abbrev Value := Model FloatFormat.binary64

/-- The stored two-point node for `-1/√3`, bit pattern `0xbfe279a74590331c`. -/
def leftNode : Value := Model.ofNatBits 0xbfe279a74590331c
/-- The stored two-point node for `+1/√3`, bit pattern `0x3fe279a74590331c`. -/
def rightNode : Value := Model.ofNatBits 0x3fe279a74590331c
/-- The binary64 value `1.0`, used as both two-point weights and in the callback's `1 - x`. -/
def one : Value := Model.ofNatBits 0x3ff0000000000000
/-- The binary64 value `0.5`, the leading factor of the callback. -/
def half : Value := Model.ofNatBits 0x3fe0000000000000
/-- Positive zero, the initial accumulator of the loop. -/
def zero : Value := Model.ofNatBits 0

/-- `rightNode` is a finite binary64 value. -/
theorem rightNode_finite : Model.isFinite rightNode = true := by decide
/-- `leftNode` is a finite binary64 value. -/
theorem leftNode_finite : Model.isFinite leftNode = true := by decide
/-- `one` is a finite binary64 value. -/
theorem one_finite : Model.isFinite one = true := by decide

/-- `zero` is a finite binary64 value. -/
theorem zero_finite : Model.isFinite zero = true := by decide

/-- `rightNode` decodes to the positive dyadic `5200308914369308 · 2⁻⁵³`. -/
theorem rightNode_decode :
    Model.toDyadic? rightNode = some ⟨false, 5200308914369308, -53⟩ := by decide

/-- `leftNode` decodes to the negative dyadic `-5200308914369308 · 2⁻⁵³`. -/
theorem leftNode_decode :
    Model.toDyadic? leftNode = some ⟨true, 5200308914369308, -53⟩ := by decide

/-- The real value of `rightNode` is `1300077228592327 / 2⁵¹`. -/
theorem rightNode_toReal :
    Model.toReal rightNode = (1300077228592327 / 2251799813685248 : ℝ) := by
  rw [Model.toReal_eq, rightNode_decode]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The real value of `leftNode` is `-1300077228592327 / 2⁵¹`. -/
theorem leftNode_toReal :
    Model.toReal leftNode = -(1300077228592327 / 2251799813685248 : ℝ) := by
  rw [Model.toReal_eq, leftNode_decode]
  norm_num [FloatLib.Numerics.Dyadic.toReal, FloatLib.Numerics.Dyadic.signedSignificand]

/-- The stored right node is within `10⁻¹⁶` of `1/√3`, by interval evaluation with 80
fractional bits. -/
theorem rightNode_error :
    |Model.toReal rightNode - 1 / Real.sqrt 3| ≤ (1 / 10 ^ 16 : ℝ) := by
  rw [rightNode_toReal]
  interval (precision := 80)

/-- The stored left node is within `10⁻¹⁶` of `-1/√3`, by symmetry from `rightNode_error`. -/
theorem leftNode_error :
    |Model.toReal leftNode - -(1 / Real.sqrt 3)| ≤ (1 / 10 ^ 16 : ℝ) := by
  rw [leftNode_toReal, ← rightNode_toReal, neg_sub_neg, abs_sub_comm]
  exact rightNode_error

end Quadrature.Binary64
