/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import CAS.Continuum.Quadrature.Gaussian.Characterization
import CAS.Continuum.Quadrature.Gaussian.Recurrence
import CAS.Continuum.Quadrature.Gaussian.Weighted
import CAS.Continuum.Quadrature.PositiveRule
import Quadrature.Binary64.BoundedRoundoff
import Quadrature.Binary64.Constants
import Quadrature.Binary64.FiniteExecution
import Quadrature.Binary64.FunctionalAccuracy
import Quadrature.Binary64.Program
import Quadrature.Binary64.Roundoff
import Quadrature.CSource.Accessors.Calls
import Quadrature.CSource.Accessors.Entry
import Quadrature.CSource.Accessors.TableExpressions
import Quadrature.CSource.Frontend.ClightFunctions
import Quadrature.CSource.Frontend.ElaborationChecks
import Quadrature.CSource.Frontend.ParserChecks
import Quadrature.CSource.Integrator.Function
import Quadrature.CSource.Library.Accuracy
import Quadrature.CSource.Library.Application
import Quadrature.CSource.Library.Preservation
import Quadrature.CSource.Library.Total
import Quadrature.CSource.Wrapper.Accuracy
import Quadrature.Clight.Arithmetic
import Quadrature.Clight.Main
import Quadrature.Clight.RuleAccuracy
import Quadrature.Clight.StoredAccuracy
import Quadrature.Clight.StoredRules
import Quadrature.Examples.CosineAccuracy
import Quadrature.Examples.CosineCallback
import Quadrature.Examples.PolynomialCosine
import Quadrature.Examples.TwoPointCosine
import Quadrature.Rules.Accuracy
import Quadrature.Rules.Basic
import Quadrature.Rules.Constants

/-!
# simple_cfem-lean: Gaussian quadrature from simple_cfem in Lean

Appel and Bindel verify in Rocq a small C library of Gaussian quadrature rules, `quadrules.c` of
their `simple_cfem` repository, from the theory of orthogonal polynomials through floating-point
error to the C functions themselves. We do the same in Lean 4 with Mathlib: exactness and error
theory on compact intervals, binary64 error bounds for the stored rules, and the C functions with
an internal polynomial cosine in an adaptation of CompCert's C and Clight semantics. Declarations
that correspond to Rocq declarations carry the Rocq names.

The Lean proofs stop at Clight. As in VeriNum's own setup, where VST proves the C program and
CompCert's correctness theorem carries the result to assembly, the step from Clight to x86-64
assembly is CompCert's. The certificates in `rocq/certification` compile twelve corresponding
programs in Rocq, with CompCert's optimizations turned off.

## Main results

Names are relative to the `Quadrature` namespace.

* `quadrature_exact_for`, `gauss_weight_positive`, `quadrature_error`: the Gaussian rule at the
  roots of `ortho_p a b w n` is exact below degree `2n` and has positive weights. For `0 < n`
  and `f` with `2n` continuous derivatives its error is `f^(2n)(ξ) / (2n)!` times
  `∫ (ortho_p a b w n)^2 w`.
* `Legendre.Gauss_Legendre_quadrature`, `Legendre.quadrature_error_bound_is_bound`: the
  Gauss–Legendre rules with one to four nodes and their error bound.
* `Binary64.StoredRule.table_certificate`: each of the ten node and weight tables of the C
  program lies within `6e-16` and `5e-16` of the ideal rule.
* `Binary64.StoredRule.Certificate.integrate_model_err`: FloatLib models the rounding of each
  product and sum in the integrator. For a certified table the result is finite, and its
  distance from the exact integral is bounded by roundoff terms, the node and weight
  tolerances, the callback error and the Gaussian remainder.
* `Example.two_point_bound`: the two-point error on the cosine example is at most
  `0.00356`.
* `CSource.Typed.body_integrate_testfun`: the `0.00356` bound for the parsed C source of the
  wrapper calling an external cosine under its contract.
* `CSource.Library.parsed_wrapper_total_accuracy` discharges that contract by a verified C
  polynomial and includes parsing, global initialization and the complete wrapper call in every
  permitted C evaluation order. `CSource.Library.integral_total_accuracy` covers all ten stored
  orders, including termination, absence of stuck executions, and caller memory preservation.
* `CSource.Library.parsed_refinement` connects the C and Clight outputs of our frontend for all
  six functions. Their calls have the same returned bits and traces; both terminate, and their
  final memories agree on pre-call loads and permissions.
* `Binary64.Clight.StoredPolynomial.integral_accuracy` and
  `Binary64.Clight.Application.final_accuracy`: Clight applications written around the same
  tables and degree-14 polynomial report a finite binary64 value within the proved bound of the
  integral for all ten orders, and exit with status zero. `final_accuracy` assumes
  `[CC.ExternalCallsDeterministic calls]`, which holds for `Binary64.Clight.emptyCalls`.
  `CSource.Library.application_observations_iff` shows that they report exactly the value the
  initialized C integrator returns.

## How it works

The proof has four layers. How the C theorems use them is described after the fourth.

The first layer is mathematics. A Gaussian rule with `n` nodes is exact below degree `2n` because
its nodal polynomial is orthogonal to every polynomial of lower degree. Its weights are positive
because each one is the integral of the square of a Lagrange basis polynomial, and its remainder
comes from Hermite interpolation at the nodes. All of this is classical, and the Rocq development
follows Lecture 23 of Stewart's *Afternotes on Numerical Analysis*. We prove it in SymLean and
restate it under the Rocq names in `Gaussian/` and `Legendre/`.

The second layer is the stored data. The C program reads its nodes and weights from two arrays
of decimal literals, one rule after another. We decode the binary64 value of every entry and
certify each of the ten rules against the exact Gauss–Legendre rule of the same order. Orders one
to four have closed forms. For orders five to ten the kernel checks rational brackets around each
Legendre root and rational enclosures of each weight.

The third layer is rounding. FloatLib's IEEE model fixes the result of every product and sum of
the loop. `Binary64.StoredRule.Certificate.integrate_model_err` splits the distance from the
exact integral into the rounding of that arithmetic, the displacement of the stored nodes and
weights, the error of the callback, and the Gaussian remainder. A range budget, an inequality on
the exact data, implies that no product or partial sum overflows, so their finiteness is proved.
Only the callback values are assumed finite, as part of `Binary64.function_accuracy`.

The fourth layer is code. We parse `quadrules.c`, elaborate it to typed C and to Clight, and
prove its calls in an adaptation of CompCert's C semantics. The ten polynomial applications are
written in Clight around the same tables, and their runs are proved in CLean's Clight semantics.

The theorems about the code with the polynomial cosine do not use the first three layers. Lean
computes by kernel evaluation the bits that the loop returns at each stored order, decodes them
exactly and compares them with an enclosure of `sin 1`
(`Binary64.Clight.StoredPolynomial.integral_accuracy`), and the fourth layer shows that the code
returns these bits. `CSource.Typed.body_integrate_testfun` uses the fourth layer and
`Binary64.two_point_program_accuracy`, which bounds the rounding of the two-point program one
operation at a time. `integrate_model_err` reaches code only in
`Binary64.Clight.stored_callback_execution_accuracy`, for a general callback.

## Notation

* `n` is the number of nodes, and `Fin n` indexes them `0, ..., n - 1`. An `n`-node rule is exact
  below degree `2n`, and its remainder has the derivative of order `2n`; Stewart, who indexes the
  nodes `0, ..., m`, writes `2m + 2`.
* `w` is the weight function of the integral, and `weights i` one coefficient of the finite sum.
* `GaussianRule` (SymLean) is an exact real rule; `StoredRule` is a table of binary64 nodes and
  weights; a `StoredRule.Certificate` relates the two.
* `Value` is FloatLib's binary64 model and `Model.toReal` its real interpretation, which does not
  by itself exclude NaN or infinity; finiteness is proved separately.
* `CC.Val` is a C runtime value; `Step` and `Steps` are one and finitely many transitions, with
  their event trace. `fuel` bounds the number of transitions a computation checks.
* A range budget bounds the sum of the absolute products and the accumulated rounding by a radius
  within the binary64 range; it is what makes the intermediate values finite.

## Implementation notes

The general theory comes from SymLean, our verified computer algebra system, under
`CAS.Continuum.Quadrature`. For a continuous positive weight `w` on `[a, b]` the monic orthogonal
polynomials exist by projection, their roots are simple and interior, the Christoffel numbers are
positive, the remainder has the classical form, and the rules converge for every continuous
integrand (`gaussian_rules_converge`). SymLean also has the explicit Gauss–Legendre rules of
orders one to four, the monic Legendre polynomials of degree at most four, and the root and
weight certificate theorems.

`Gaussian/` and `Legendre/` hold the layer that mirrors the Rocq development. They state Appel
and Bindel's definitions and lemmas under their names and in their form, and prove each lemma
from the SymLean theorems. `docs/comparison.md` lists the correspondence.

The other files are grouped by subject under `Quadrature/`:

* `Binary64/`: FloatLib operations, rounding, and loop models.
* `Rules/`: stored tables, rational root brackets for orders five to ten checked by kernel
  evaluation, table certificates, and accuracy bounds.
* `Examples/`: the cosine applications and the polynomial cosine. The trigonometric estimates
  use FloatLib's `interval` tactic.
* `CSource/`: the frontend, C semantics, original functions, and internal cosine library.
* `Clight/`: library calls and initialized polynomial applications.

`ORGANIZATION.md` outlines the folders. `Quadrature` imports every source module, directly or
through a dependency, so the assumption audit checks the entire library.

Our C parser is a restricted one. Its output for the five original functions is checked against
`clightgen`'s, and the internal C polynomial is checked by parsing its shipped source. C calls
are proved in the adaptation of CompCert's full C small-step rules using FloatLib, and behavioral
preservation is proved between the typed C and normalized Clight outputs for the selected calls.
We do not prove the parser and elaborator correct in general, including preprocessing and
static-array hoisting, against an independent source semantics. The Clight semantics is adapted
from CLean and is not related by proof to CompCert's Rocq semantics, so the Rocq compilation
certificates and these Lean proofs are separate results about corresponding applications. They
share `main`, the five original functions, the two tables and the polynomial cosine; the Rocq
programs (`program_of_main` in `rocq/clight/StoredPolynomialRules.v`) also keep every other global
of the `clightgen` output, which `Binary64.Clight.Application.program` omits. The platform `cos`
is not verified; the polynomial library supplies its own C routine. FloatLib and Flocq arithmetic
are not related by proof.

## References

* A. W. Appel and D. S. Bindel, `simple_cfem`, the Rocq proofs in
  [`proof/`](https://github.com/VeriNum/simple_cfem/tree/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof).
* A. W. Appel and D. S. Bindel, `simple_cfem`, the original C program
  [`src/quadrules.c`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/src/quadrules.c).
* G. W. Stewart, *Afternotes on Numerical Analysis*, SIAM, Philadelphia, 1996,
  [doi:10.1137/1.9781611971491](https://doi.org/10.1137/1.9781611971491). Lecture 23.
* X. Leroy, *Formal verification of a realistic compiler*, Commun. ACM 52 (2009), no. 7, 107–115,
  [doi:10.1145/1538788.1538814](https://doi.org/10.1145/1538788.1538814).
* The mathlib Community, *The Lean mathematical library*, in Proceedings of the 9th ACM SIGPLAN
  International Conference on Certified Programs and Proofs (CPP 2020), ACM, 2020, 367–381,
  [doi:10.1145/3372885.3373824](https://doi.org/10.1145/3372885.3373824).
* FloatLib 3.1.0, verified floating-point arithmetic in Lean,
  [source](https://github.com/lean-dojo/FloatLib/tree/0fe4f0496153a1a494115af1fbcb825069cb4017).
-/
