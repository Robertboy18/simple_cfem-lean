/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Quadrature.Rules.Basic

/-!
# The polynomial cosine of the quadrature applications

The Clight and C applications replace the library cosine by the degree-14 Taylor polynomial,
with the binary64 coefficient encodings and Horner order of the companion Rocq proofs in
`rocq/clight/InternalCosine.v`. This module defines that polynomial.

## Main definitions

* `coefficients`: the eight binary64 coefficients, in ascending degree of `x²`.
* `horner`: Horner evaluation with every multiplication and addition rounded separately.
* `cosine`: the polynomial cosine, evaluated by Horner's rule in the rounded square of the input.

## References

* FloatLib 3.1.0, verified floating-point arithmetic in Lean,
  [source](https://github.com/lean-dojo/FloatLib/tree/0fe4f0496153a1a494115af1fbcb825069cb4017).
-/

namespace Quadrature.Binary64.Polynomial

open FloatLib.Floats.Formats.BinaryInterchange

/-- Stored binary64 coefficients in ascending polynomial degree. -/
def coefficients : List Value :=
  [4607182418800017408, 13826050856027422720, 4586165620538955093,
   13787419979223755799, 4537941361671905306, 13732177094651715420,
   4477122120089393304, 13666517717442657437].map Model.ofNatBits

/-- Each multiplication and addition is separately rounded, including the final zero. -/
def horner (z : Value) : List Value → Value
  | [] => zero
  | c :: cs => Model.add c (Model.mul z (horner z cs))

/-- The degree-fourteen polynomial is evaluated in the rounded square of the input. -/
def cosine (x : Value) : Value := horner (Model.mul x x) coefficients

end Quadrature.Binary64.Polynomial
