/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import CCLib.Cop
import Mathlib.Tactic.NormNum
import Quadrature.Binary64.Constants

/-!
# Arithmetic in the adapted Clight semantics

In this port `CC.Floats.Float` is definitionally FloatLib's binary64 `Model`,
so Clight's `double` operators `+ - * /` are `Model.add`, `Model.sub`,
`Model.mul` and `Model.div`. The four `_semantics` lemmas are `rfl` and record
that. The next eleven lemmas are regression tests, checked by `decide`, of
comparison, absolute value and conversion to 64-bit integers. They cover
exceptional values and the limits of the signed and unsigned ranges, computed
without native floating point, and no other proof uses them.

The integrator computes the start `n * (n - 1) / 2` of the `n`-node rule in its tables with
signed 32-bit arithmetic. `signed_repr_nat`, `divs_repr_nat_two`, `mul_pred_repr_nat` and
`divs_two` connect that calculation to natural-number arithmetic. The product `n * (n - 1)`
agrees in both representations even at `n = 0`.

## References

* FloatLib 3.1.0, verified floating-point arithmetic in Lean,
  [source](https://github.com/lean-dojo/FloatLib/tree/0fe4f0496153a1a494115af1fbcb825069cb4017).
* Certora CLean,
  [source](https://github.com/Certora/clean/tree/123f7f7767e215aceb4821f0d044336d78103ade).
-/

namespace Quadrature.Binary64.Clight

open FloatLib.Floats.Formats.BinaryInterchange

/-- Clight `double` addition is `Model.add`, by `rfl`. -/
theorem add_semantics (ce : CC.CompositeEnv) (m : CC.Mem) (x y : Value) :
    CC.Cop.semBinaryOperation ce .Oadd (.Vfloat x) CC.tdouble (.Vfloat y) CC.tdouble m =
      some (.Vfloat (Model.add x y)) := rfl

/-- Clight `double` multiplication is `Model.mul`, by `rfl`. -/
theorem mul_semantics (ce : CC.CompositeEnv) (m : CC.Mem) (x y : Value) :
    CC.Cop.semBinaryOperation ce .Omul (.Vfloat x) CC.tdouble (.Vfloat y) CC.tdouble m =
      some (.Vfloat (Model.mul x y)) := rfl

/-- Clight `double` subtraction is `Model.sub`, by `rfl`. -/
theorem sub_semantics (ce : CC.CompositeEnv) (m : CC.Mem) (x y : Value) :
    CC.Cop.semBinaryOperation ce .Osub (.Vfloat x) CC.tdouble (.Vfloat y) CC.tdouble m =
      some (.Vfloat (Model.sub x y)) := rfl

/-- Clight `double` division is `Model.div`, by `rfl`. -/
theorem div_semantics (ce : CC.CompositeEnv) (m : CC.Mem) (x y : Value) :
    CC.Cop.semBinaryOperation ce .Odiv (.Vfloat x) CC.tdouble (.Vfloat y) CC.tdouble m =
      some (.Vfloat (Model.div x y)) := rfl

/-- `+0.0 == -0.0` holds under Clight's `double` comparison. -/
theorem signed_zero_equal :
    CC.Floats.Float.cmp .Ceq (Model.ofNatBits 0) (Model.ofNatBits 0x8000000000000000) =
      true := by decide

/-- The absolute value of `-0.0` is `+0.0`, sign bit included. -/
theorem abs_negative_zero :
    CC.Floats.Float.abs (Model.ofNatBits 0x8000000000000000) = Model.ofNatBits 0 := by
  decide

/-- A NaN compares unequal to itself under `!=`. -/
theorem nan_not_equal :
    CC.Floats.Float.cmp .Cne (Model.ofNatBits 0x7ff8000000000001)
      (Model.ofNatBits 0x7ff8000000000001) = true := by decide

/-- A NaN is not less than zero: ordered comparisons with a NaN are false. -/
theorem nan_not_less :
    CC.Floats.Float.cmp .Clt (Model.ofNatBits 0x7ff8000000000001)
      (Model.ofNatBits 0) = false := by decide

/-- Converting a NaN to a signed 64-bit integer fails. -/
theorem nan_to_long_none :
    CC.Floats.Float.toLong (Model.ofNatBits 0x7ff8000000000001) = none := by decide

/-- Converting `+∞` to a signed 64-bit integer fails. -/
theorem infinity_to_long_none :
    CC.Floats.Float.toLong (Model.ofNatBits 0x7ff0000000000000) = none := by decide

/-- `2^63` is outside the range of signed 64-bit integers, so the conversion fails. -/
theorem two_pow_63_to_long_none :
    CC.Floats.Float.toLong (Model.ofNatBits 0x43e0000000000000) = none := by decide

/-- `2^63` converts to the unsigned 64-bit integer `9223372036854775808`. -/
theorem two_pow_63_to_longu :
    CC.Floats.Float.toLongu (Model.ofNatBits 0x43e0000000000000) =
      some (CC.Integers.Int64.repr 9223372036854775808) := by decide

/-- `2^64` is outside the unsigned 64-bit range, so the conversion fails. -/
theorem two_pow_64_to_longu_none :
    CC.Floats.Float.toLongu (Model.ofNatBits 0x43f0000000000000) = none := by decide

/-- `-1.0` converts to no unsigned 64-bit integer. -/
theorem negative_one_to_longu_none :
    CC.Floats.Float.toLongu (Model.ofNatBits 0xbff0000000000000) = none := by decide

/-- `-0.5` converts to unsigned zero: the range check applies to the truncated integer. -/
theorem negative_half_to_longu :
    CC.Floats.Float.toLongu (Model.ofNatBits 0xbfe0000000000000) =
      some (CC.Integers.Int64.repr 0) := by decide

end Quadrature.Binary64.Clight

namespace CC.Integers.Int

/-- Converting a natural number below `2 ^ 31` to a signed 32-bit integer preserves its value. -/
theorem signed_repr_nat (n : Nat) (hn : n < 2 ^ 31) :
    signed (repr n) = (n : Z) := by
  apply BitVec.toInt_ofInt_eq_self (by decide)
  · norm_num
  · exact_mod_cast hn

/-- Signed division by two agrees with natural-number division below the signed limit. -/
theorem divs_repr_nat_two (n : Nat) (hn : n < 2 ^ 31) :
    divs (repr n) (repr 2) = repr (n / 2 : Nat) := by
  apply BitVec.toInt_inj.mp
  change ((BitVec.ofInt 32 (n : Z)).sdiv (BitVec.ofInt 32 2)).toInt = _
  rw [BitVec.toInt_sdiv_of_ne_or_ne _ _ (Or.inr (by decide))]
  change (signed (repr n)).tdiv 2 = signed (repr (n / 2 : Nat))
  rw [signed_repr_nat n hn, signed_repr_nat (n / 2) (by omega)]
  simp

/-- Multiplication by `n` absorbs the difference between signed and natural predecessors. -/
theorem mul_pred_repr_nat (n : Nat) :
    mul (repr n) (sub (repr n) (repr 1)) = repr (n * (n - 1) : Nat) := by
  change BitVec.ofInt 32 (n : Z) *
    (BitVec.ofInt 32 (n : Z) - BitVec.ofInt 32 1) = _
  rw [BitVec.sub_eq_add_neg, ← BitVec.ofInt_neg, ← BitVec.ofInt_add,
    ← BitVec.ofInt_mul]
  congr 1
  cases n <;> simp

end CC.Integers.Int

namespace CC.Val

/-- The value-level guards allow division by two for every signed 32-bit dividend. -/
theorem divs_two (a : Integers.Int) :
    divs (.Vint a) (.Vint (Integers.Int.repr 2)) =
      some (.Vint (Integers.Int.divs a (Integers.Int.repr 2))) := by
  change (if (false || (a.eq (Integers.Int.repr Integers.Int.min_signed) && false)) = true
    then none else _) = _
  simp

end CC.Val
