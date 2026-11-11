# Comparison with simple_cfem's Rocq proofs

This page maps the Lean development to the quadrature proofs of
[simple_cfem](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof): first by the paragraphs of Lecture 23 of Stewart's *Afternotes on
Numerical Analysis*, which [`quadrature.v`](https://github.com/VeriNum/simple_cfem/blob/96d4462f8cb1a31ac31990a173da4edcfe7f6852/proof/quadrature.v) follows and numbers, then
declaration by declaration. Lean names are relative to the namespace `Quadrature`, and SymLean
names to `CAS.Continuum`.

## Stewart's paragraphs

Stewart indexes the nodes `0, ..., m`; with `n = m + 1` nodes his derivative of order
`2m + 2` is the derivative of order `2n`.

| ¶ | Stewart | Lean | Rocq, `quadrature.v` |
| --- | --- | --- | --- |
| 1 | Approximate `∫ f w` by a weighted sum of `n` values of `f` | `G` | `G` |
| 2 | The weighted integral `I_w(f)` | `intgal` | `intgal` |
| 3 | `I_w` is linear | SymLean's `polynomialIntegral`, a linear map | `intgal_linear1`, `intgal_linear2` |
| 4 | Orthogonality: `I_w(p q) = 0` | `orthogonal` | `orthogonal` |
| 5 | A monic orthogonal polynomial of each degree | `orthogonal_polynomials` | `orthogonal_polynomials` |
| 6–8 | Expansion in a monic family, and orthogonality to every lower degree | Not restated: SymLean constructs the family by projection (`exists_monic_orthogonal`, `orthogonalPolynomial_orthogonal`) | `stewart_lemma_23_6`, `polySn_orthogonal_n` |
| 9–12 | The three-term recurrence | `three_term_recurrence`, `ortho_p`, `ortho_p_orthogonal`, `orthogonal_polynomials_ortho_p` | `three_term_recurrence`, `ortho_p`, `ortho_p_orthogonal` |
| 13 | `p_n` has `n` distinct roots in `(a, b)` | `roots_of_ortho_p`, a structure of roots; SymLean proves they exist (`orthogonal_splits`, `orthogonal_root_mem_Ioo`) | `roots_of_ortho_p`, a record of roots |
| 14 | Proof of 13 by counting sign changes | `roots_of_ortho_p_at_most`; SymLean's `orthogonal_factor_has_root` proves 13 another way | `roots_of_ortho_p_at_most` |
| 15 | Weights from Lagrange interpolation at the roots; exactness below degree `n` | `gauss_weight`, `quadrature_exact_upto_n` | `gauss_weight`, `quadrature_exact_upto_n` |
| 16 | Exactness below degree `2n`, by division by `p_n` | `quadrature_exact_for` | `quadrature_exact_for` |
| 17 | The weights are positive | `gauss_weight_positive` | `gauss_weight_positive` |
| 18 | The weights sum to `I_w(1)` | `gauss_weight_leq_1` | `gauss_weight_leq_1` |
| 19 | The remainder `I_w(p_n²) f^(2n)(ξ) / (2n)!` | `quadrature_error` | `quadrature_error` |
| 20 | Convergence for continuous `f` | SymLean's `gaussian_rules_converge` | `quadrature_converges`, commented out |
| 21 | The weight `1` on `[-1, 1]`: Gauss–Legendre rules | `Legendre.legendre`, `Legendre.Gauss_Legendre_quadrature` | `Module Legendre` |
| 22 | Gauss–Laguerre rules on `[0, ∞)` | None | None |
| 23 | Gauss–Hermite rules on `(-∞, ∞)` | None | None |
| 24 | Other intervals and weights | A continuous positive weight on a compact interval | A continuous positive weight on a finite interval |

## Declaration names

Every Lean declaration that restates a declaration of the Rocq quadrature files carries the Rocq
name exactly. These files are `quadrature.v`, `quadrature2.v`, `quadmodel.v`,
`quadmodel_accuracy.v`, and `spec_quadrules.v`, `spec_quadrules_highlevel.v` and
`verif_quadrules.v` in `C/`. Only a namespace is added, and structure fields keep their case: the
Rocq field `ROOTS_vals` is `Quadrature.roots_of_ortho_p.ROOTS_vals`, written `roots.ROOTS_vals`.
Every Rocq name in the table is also the Lean name: none is a Lean keyword or collides with
Mathlib or with notation. Rocq
defines `intgal` twice, for a general weight and in `Module Legendre`, and both appear. The
`FLOAT` section of `quadmodel_accuracy.v` restates `gauss_pt_range`, `gauss_wt_range`,
`g_max_deriv` and `integrate_model_f` for its section variables; each is listed once.

A few conventions hold throughout. Section hypotheses become explicit arguments with their Rocq
names, and `wcontinuous` is the weaker `ContinuousOn w (Set.Icc a b)`. Arguments that Lean can infer
from the others are implicit, while Rocq passes them explicitly: `a`, `b` and `w` in the lemmas, and
`n` when a record of roots or weights fixes it, as in `G`, `roots_of_ortho_p_unique` and
`compute_G_eq`. A tuple `n.-tuple R` becomes a function `Fin n → ℝ`, and `'I_n` becomes `Fin n`.
`size p ≤ k` becomes `p.degree < k`, `horner p` becomes `p.eval`, and `derive1n` becomes
`iteratedDeriv`. Line numbers refer to the revision linked above. `scripts/check-rocq-names.py` checks
every row against a simple_cfem checkout and the Lean build.

The last column gives one of three labels. *Same* means the same mathematical statement, under the
conventions above. *Same up to encoding* means the same content in other types or representations,
and the column says which. *Different* means a materially different statement, and the column says
how it differs. Of the 116 rows, 85 are the same, 16 are the same up to encoding and 15 are
different.

| Rocq name | Rocq file | Lean name | Lean module | Comparison |
| --- | --- | --- | --- | --- |
| `intgal` | `quadrature.v:791` | `Quadrature.intgal` | `Quadrature.Gaussian.Orthogonal` | Same |
| `orthogonal` | `quadrature.v:888` | `Quadrature.orthogonal` | `Quadrature.Gaussian.Orthogonal` | Same |
| `orthogonal_polynomials` | `quadrature.v:896` | `Quadrature.orthogonal_polynomials` | `Quadrature.Gaussian.Orthogonal` | Same up to encoding: `(p i).degree = i` for `size (p i) = i.+1` |
| `three_term_recurrence` | `quadrature.v:1215` | `Quadrature.three_term_recurrence` | `Quadrature.Gaussian.Orthogonal` | Same |
| `ortho_p` | `quadrature.v:1227` | `Quadrature.ortho_p` | `Quadrature.Gaussian.Orthogonal` | Same; also identified with SymLean's `integralOrthogonalPolynomial` |
| `ortho_p_prev` | `quadrature.v:1229` | `Quadrature.ortho_p_prev` | `Quadrature.Gaussian.Orthogonal` | Same |
| `ortho_p_size` | `quadrature.v:1237` | `Quadrature.ortho_p_size` | `Quadrature.Gaussian.Orthogonal` | Same up to encoding: `degree = n` for `size = n.+1` |
| `ortho_p_monic` | `quadrature.v:1281` | `Quadrature.ortho_p_monic` | `Quadrature.Gaussian.Orthogonal` | Same |
| `ortho_p_nonzero` | `quadrature.v:1327` | `Quadrature.ortho_p_nonzero` | `Quadrature.Gaussian.Orthogonal` | Same |
| `sqr_poly_positive` | `quadrature.v:1340` | `Quadrature.sqr_poly_positive` | `Quadrature.Gaussian.Orthogonal` | Same |
| `ortho_p2_positive` | `quadrature.v:1459` | `Quadrature.ortho_p2_positive` | `Quadrature.Gaussian.Orthogonal` | Same |
| `ortho_p_orthogonal_special` | `quadrature.v:1526` | `Quadrature.ortho_p_orthogonal_special` | `Quadrature.Gaussian.Orthogonal` | Same |
| `ortho_p_orthogonal` | `quadrature.v:1614` | `Quadrature.ortho_p_orthogonal` | `Quadrature.Gaussian.Orthogonal` | Same |
| `roots_of_ortho_p` | `quadrature.v:1651` | `Quadrature.roots_of_ortho_p` | `Quadrature.Gaussian.Rule` | Same up to encoding: a structure with four fields for the Rocq record |
| `ROOTS_vals` | `quadrature.v:1652` | `Quadrature.roots_of_ortho_p.ROOTS_vals` | `Quadrature.Gaussian.Rule` | Same up to encoding: `Fin n → ℝ` for `n.-tuple R` |
| `ROOTS_zero` | `quadrature.v:1653` | `Quadrature.roots_of_ortho_p.ROOTS_zero` | `Quadrature.Gaussian.Rule` | Same |
| `ROOTS_sorted` | `quadrature.v:1654` | `Quadrature.roots_of_ortho_p.ROOTS_sorted` | `Quadrature.Gaussian.Rule` | Same up to encoding: `StrictMono` for `sorted Order.lt` |
| `ROOTS_inrange` | `quadrature.v:1655` | `Quadrature.roots_of_ortho_p.ROOTS_inrange` | `Quadrature.Gaussian.Rule` | Same |
| `roots_of_ortho_p_at_most` | `quadrature.v:1666` | `Quadrature.roots_of_ortho_p_at_most` | `Quadrature.Gaussian.Rule` | Same |
| `roots_of_ortho_p_unique` | `quadrature.v:1742` | `Quadrature.roots_of_ortho_p_unique` | `Quadrature.Gaussian.Rule` | Same |
| `gauss_weight` | `quadrature.v:1852` | `Quadrature.gauss_weight` | `Quadrature.Gaussian.Rule` | Same up to encoding: the integral of Mathlib's `Lagrange.basis` on the roots, for MathComp's `lagrange` on the roots extended to all natural numbers |
| `G` | `quadrature.v:1854` | `Quadrature.G` | `Quadrature.Gaussian.Rule` | Same |
| `quadrature_exact_upto_n` | `quadrature.v:1917` | `Quadrature.quadrature_exact_upto_n` | `Quadrature.Gaussian.Rule` | Different: assumes only `a ≤ b` and continuity of `w`, where the section of `quadrature.v` assumes `a < b`, `0 < w` and continuity of `w` |
| `quadrature_exact_for'` | `quadrature.v:1959` | `Quadrature.quadrature_exact_for'` | `Quadrature.Gaussian.Rule` | Same |
| `quadrature_exact_for` | `quadrature.v:1996` | `Quadrature.quadrature_exact_for` | `Quadrature.Gaussian.Rule` | Same |
| `gauss_weight_positive` | `quadrature.v:2016` | `Quadrature.gauss_weight_positive` | `Quadrature.Gaussian.Rule` | Same |
| `gauss_weight_leq_1` | `quadrature.v:2061` | `Quadrature.gauss_weight_leq_1` | `Quadrature.Gaussian.Rule` | Same; as in Rocq, the bound is the integral of `w` |
| `quadrature_error` | `quadrature.v:2083` | `Quadrature.quadrature_error` | `Quadrature.Gaussian.Rule` | Different: squares `ortho_p n` where Rocq squares `ortho_p n.+1`, and assumes `0 < n` and `2n` continuous derivatives of `f`, which the Rocq statement does not |
| `lo` | `quadrature.v:2129` | `Quadrature.Legendre.lo` | `Quadrature.Legendre.Basic` | Same |
| `hi` | `quadrature.v:2130` | `Quadrature.Legendre.hi` | `Quadrature.Legendre.Basic` | Same |
| `lo_lt_hi` | `quadrature.v:2131` | `Quadrature.Legendre.lo_lt_hi` | `Quadrature.Legendre.Basic` | Same |
| `w` | `quadrature.v:2132` | `Quadrature.Legendre.w` | `Quadrature.Legendre.Basic` | Same |
| `w_positive` | `quadrature.v:2133` | `Quadrature.Legendre.w_positive` | `Quadrature.Legendre.Basic` | Same |
| `wcontinuous` | `quadrature.v:2135` | `Quadrature.Legendre.wcontinuous` | `Quadrature.Legendre.Basic` | Same |
| `legendre` | `quadrature.v:2140` | `Quadrature.Legendre.legendre` | `Quadrature.Legendre.Basic` | Same |
| `intgal` | `quadrature.v:2150` | `Quadrature.Legendre.intgal` | `Quadrature.Legendre.Basic` | Same |
| `intgal_eq` | `quadrature.v:2153` | `Quadrature.Legendre.intgal_eq` | `Quadrature.Legendre.Basic` | Same |
| `legendre_roots` | `quadrature.v:2243` | `Quadrature.Legendre.legendre_roots` | `Quadrature.Legendre.Basic` | Same up to encoding: a structure with three fields for the Rocq record |
| `LR_poly` | `quadrature.v:2244` | `Quadrature.Legendre.legendre_roots.LR_poly` | `Quadrature.Legendre.Basic` | Same |
| `LR_poly_eq` | `quadrature.v:2245` | `Quadrature.Legendre.legendre_roots.LR_poly_eq` | `Quadrature.Legendre.Basic` | Same |
| `LR_roots` | `quadrature.v:2246` | `Quadrature.Legendre.legendre_roots.LR_roots` | `Quadrature.Legendre.Basic` | Same |
| `gauss_weights` | `quadrature.v:2255` | `Quadrature.Legendre.gauss_weights` | `Quadrature.Legendre.Basic` | Same up to encoding: a structure with three fields for the Rocq record |
| `GW_legendre` | `quadrature.v:2256` | `Quadrature.Legendre.gauss_weights.GW_legendre` | `Quadrature.Legendre.Basic` | Same |
| `GW_vals` | `quadrature.v:2257` | `Quadrature.Legendre.gauss_weights.GW_vals` | `Quadrature.Legendre.Basic` | Same |
| `GW_good` | `quadrature.v:2258` | `Quadrature.Legendre.gauss_weights.GW_good` | `Quadrature.Legendre.Basic` | Same |
| `compute_G` | `quadrature.v:2267` | `Quadrature.Legendre.compute_G` | `Quadrature.Legendre.Basic` | Same |
| `compute_G_eq` | `quadrature.v:2270` | `Quadrature.Legendre.compute_G_eq` | `Quadrature.Legendre.Basic` | Same |
| `legendre_quadrature_error` | `quadrature.v:2285` | `Quadrature.Legendre.legendre_quadrature_error` | `Quadrature.Legendre.Basic` | Different: squares `legendre n` where Rocq squares `legendre n.+1`, and assumes `0 < n` and `2n` continuous derivatives of `f`, which the Rocq statement does not |
| `Legendre_poly_0` | `quadrature.v:2442` | `Quadrature.Legendre.Legendre_poly_0` | `Quadrature.Legendre.Basic` | Same |
| `Legendre_poly_0'` | `quadrature.v:2447` | `Quadrature.Legendre.Legendre_poly_0'` | `Quadrature.Legendre.Basic` | Same |
| `legendre_roots_0` | `quadrature.v:2453` | `Quadrature.Legendre.legendre_roots_0` | `Quadrature.Legendre.Rules` | Same |
| `Legendre_poly_1` | `quadrature.v:2463` | `Quadrature.Legendre.Legendre_poly_1` | `Quadrature.Legendre.Basic` | Same |
| `Legendre_poly_1'` | `quadrature.v:2469` | `Quadrature.Legendre.Legendre_poly_1'` | `Quadrature.Legendre.Basic` | Same |
| `legendre_roots_1` | `quadrature.v:2474` | `Quadrature.Legendre.legendre_roots_1` | `Quadrature.Legendre.Rules` | Same |
| `Legendre_poly_2` | `quadrature.v:2491` | `Quadrature.Legendre.Legendre_poly_2` | `Quadrature.Legendre.Basic` | Same |
| `Legendre_poly_2'` | `quadrature.v:2502` | `Quadrature.Legendre.Legendre_poly_2'` | `Quadrature.Legendre.Basic` | Same |
| `legendre_roots_2` | `quadrature.v:2527` | `Quadrature.Legendre.legendre_roots_2` | `Quadrature.Legendre.Rules` | Same |
| `Legendre_poly_3` | `quadrature.v:2575` | `Quadrature.Legendre.Legendre_poly_3` | `Quadrature.Legendre.Basic` | Same |
| `Legendre_poly_3'` | `quadrature.v:2591` | `Quadrature.Legendre.Legendre_poly_3'` | `Quadrature.Legendre.Basic` | Same |
| `legendre_roots_3` | `quadrature.v:2597` | `Quadrature.Legendre.legendre_roots_3` | `Quadrature.Legendre.Rules` | Same |
| `Legendre_poly_4` | `quadrature.v:2617` | `Quadrature.Legendre.Legendre_poly_4` | `Quadrature.Legendre.Basic` | Same |
| `Legendre_poly_4'` | `quadrature.v:2659` | `Quadrature.Legendre.Legendre_poly_4'` | `Quadrature.Legendre.Basic` | Same |
| `legendre_roots_val` | `quadrature.v:2664` | `Quadrature.Legendre.legendre_roots_val` | `Quadrature.Legendre.Rules` | Same |
| `legendre_roots_4a` | `quadrature.v:2669` | `Quadrature.Legendre.legendre_roots_4a` | `Quadrature.Legendre.Rules` | Same |
| `legendre_roots_4b` | `quadrature.v:2728` | `Quadrature.Legendre.legendre_roots_4b` | `Quadrature.Legendre.Rules` | Same up to encoding: `StrictMono` for `sorted` |
| `legendre_roots_4c` | `quadrature.v:2748` | `Quadrature.Legendre.legendre_roots_4c` | `Quadrature.Legendre.Rules` | Same |
| `legendre_roots_4` | `quadrature.v:2767` | `Quadrature.Legendre.legendre_roots_4` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weights_0` | `quadrature.v:2777` | `Quadrature.Legendre.gauss_weights_0` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weight_1_0` | `quadrature.v:2787` | `Quadrature.Legendre.gauss_weight_1_0` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weights_1` | `quadrature.v:2798` | `Quadrature.Legendre.gauss_weights_1` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weight_2_0` | `quadrature.v:2808` | `Quadrature.Legendre.gauss_weight_2_0` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weight_2_1` | `quadrature.v:2830` | `Quadrature.Legendre.gauss_weight_2_1` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weights_2` | `quadrature.v:2842` | `Quadrature.Legendre.gauss_weights_2` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weight_3_0` | `quadrature.v:2854` | `Quadrature.Legendre.gauss_weight_3_0` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weight_3_1` | `quadrature.v:2871` | `Quadrature.Legendre.gauss_weight_3_1` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weight_3_2` | `quadrature.v:2891` | `Quadrature.Legendre.gauss_weight_3_2` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weights_3` | `quadrature.v:2908` | `Quadrature.Legendre.gauss_weights_3` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weight_4_0` | `quadrature.v:2927` | `Quadrature.Legendre.gauss_weight_4_0` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weight_4_1` | `quadrature.v:3055` | `Quadrature.Legendre.gauss_weight_4_1` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weight_4_2` | `quadrature.v:3222` | `Quadrature.Legendre.gauss_weight_4_2` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weight_4_3` | `quadrature.v:3250` | `Quadrature.Legendre.gauss_weight_4_3` | `Quadrature.Legendre.Rules` | Same |
| `gauss_weights_4` | `quadrature.v:3274` | `Quadrature.Legendre.gauss_weights_4` | `Quadrature.Legendre.Rules` | Same |
| `some_legendre_roots` | `quadrature.v:3324` | `Quadrature.Legendre.some_legendre_roots` | `Quadrature.Legendre.Rules` | Same up to encoding: a dependent function on `Fin 5` for the `iseq` list |
| `some_gauss_weights` | `quadrature.v:3334` | `Quadrature.Legendre.some_gauss_weights` | `Quadrature.Legendre.Rules` | Same up to encoding: a dependent function on `Fin 5` for the `iseq` list |
| `legendre_roots_unique` | `quadrature.v:3342` | `Quadrature.Legendre.legendre_roots_unique` | `Quadrature.Legendre.Rules` | Same |
| `Gauss_Legendre_quadrature` | `quadrature.v:3358` | `Quadrature.Legendre.Gauss_Legendre_quadrature` | `Quadrature.Legendre.Rules` | Same |
| `legendre_quadrature_error'` | `quadrature.v:3370` | `Quadrature.Legendre.legendre_quadrature_error'` | `Quadrature.Legendre.Rules` | Different: squares `legendre n` where Rocq squares `legendre n.+1`, and assumes `0 < n` and `2n` continuous derivatives of `f`, which the Rocq statement does not |
| `quadrature_error_bound` | `quadrature.v:3382` | `Quadrature.Legendre.quadrature_error_bound` | `Quadrature.Legendre.Rules` | Different: normalized by the integral of `(legendre n)²` where Rocq uses `legendre n.+1` |
| `quadrature_error_bound_is_bound` | `quadrature.v:3387` | `Quadrature.Legendre.quadrature_error_bound_is_bound` | `Quadrature.Legendre.Rules` | Different: for our `quadrature_error_bound`, and assumes `0 < n` and `2n` continuous derivatives, as `legendre_quadrature_error'` does |
| `fbound` | `quadrature2.v:31` | `Quadrature.fbound` | `Quadrature.Legendre.Bounds` | Same |
| `deriv_bound` | `quadrature2.v:32` | `Quadrature.deriv_bound` | `Quadrature.Legendre.Bounds` | Same up to encoding: `DifferentiableAt` and `deriv` for `derivable` and `derive1` |
| `g_max_deriv` | `quadrature2.v:67` | `Quadrature.g_max_deriv` | `Quadrature.Legendre.Bounds` | Same |
| `gauss_pt` | `quadrature2.v:324` | `Quadrature.gauss_pt` | `Quadrature.Legendre.Bounds` | Same |
| `gauss_pt_range` | `quadrature2.v:327` | `Quadrature.gauss_pt_range` | `Quadrature.Legendre.Bounds` | Same |
| `gauss_wt` | `quadrature2.v:337` | `Quadrature.gauss_wt` | `Quadrature.Legendre.Bounds` | Same |
| `gauss_wt_range` | `quadrature2.v:340` | `Quadrature.gauss_wt_range` | `Quadrature.Legendre.Bounds` | Same |
| `error_1_0_1'` | `quadrature2.v:405` | `Quadrature.Example.error_1_0_1'` | `Quadrature.Examples.TwoPointCosine` | Same; proved from enclosures of `sin 1`, not from `error_1_0_1` |
| `g_max_deriv_specialized` | `quadrature2.v:423` | `Quadrature.g_max_deriv_specialized` | `Quadrature.Legendre.Bounds` | Same |
| `integrate_model_f` | `quadmodel.v:32` | `Quadrature.Binary64.integrate_model_f` | `Quadrature.Binary64.Program` | Same up to encoding, at binary64, where Rocq's takes the float format as a parameter: it folds a list of (weight, node) pairs and takes `f` first |
| `testfun_f` | `quadmodel.v:200` | `Quadrature.Binary64.testfun_f` | `Quadrature.Binary64.Program` | Same up to encoding: takes the binary64 cosine as an argument, where Rocq uses VSTlib's `cos` |
| `function_accuracy` | `quadmodel_accuracy.v:131` | `Quadrature.Binary64.function_accuracy` | `Quadrature.Rules.Accuracy` | Same up to encoding, at binary64; `g`, `f` and the error as arguments |
| `finite_integrate_model` | `quadmodel_accuracy.v:563` | `Quadrature.Binary64.StoredRule.Certificate.finite_integrate_model` | `Quadrature.Rules.Accuracy` | Different: for a certified stored rule with `n > 0`, under a range budget in place of `parameter_limits` and `finite_integrate_condition`; every intermediate value of the loop is finite, not only the result |
| `perturb_sum` | `quadmodel_accuracy.v:617` | `Quadrature.Binary64.perturb_sum` | `Quadrature.Binary64.FunctionalAccuracy` | Same up to encoding: for the terms of a list, with its length in place of `n` |
| `integrate_model_roundoff_err` | `quadmodel_accuracy.v:655` | `Quadrature.Binary64.StoredRule.Certificate.integrate_model_roundoff_err` | `Quadrature.Rules.Accuracy` | Different: for a certified stored rule with `n > 0`, under a range budget in place of `parameter_limits` and `finite_integrate_condition`; assumes the Lipschitz bound that `g_max_deriv` gives where Rocq assumes `deriv_bound`; the bound is `2n` half-ulps at the budget radius plus the table and callback errors, in place of `integrate_model_acc`, and the result is also finite |
| `integrate_model_err` | `quadmodel_accuracy.v:714` | `Quadrature.Binary64.StoredRule.Certificate.integrate_model_err` | `Quadrature.Rules.Accuracy` | Different: as `integrate_model_roundoff_err`; a bound on the `2n`-th derivative of a `g` with `2n` continuous derivatives on `[-1, 1]` replaces `quadrature_error_bound g n b`, and the Gaussian remainder replaces `b` |
| `gauss_point_f_bound` | `quadmodel_accuracy.v:779` | `Quadrature.Binary64.StoredRule.gauss_point_f_bound` | `Quadrature.Rules.Tables` | Different: for the decoded C tables with `n ≤ 10`, where Rocq's `n : 'I_5`; membership in `[-1, 1]` for `|x| ≤ 1` |
| `testfun_r` | `quadmodel_accuracy.v:1025` | `Quadrature.Example.testfun_r` | `Quadrature.Examples.TwoPointCosine` | Same |
| `testfun_fb` | `quadmodel_accuracy.v:1030` | `Quadrature.Binary64.testfun_fb` | `Quadrature.Examples.CosineCallback` | Same |
| `testfun_fbound` | `quadmodel_accuracy.v:1031` | `Quadrature.Binary64.testfun_fbound` | `Quadrature.Examples.CosineCallback` | Same |
| `testfun_d` | `quadmodel_accuracy.v:1034` | `Quadrature.Binary64.testfun_d` | `Quadrature.Examples.CosineCallback` | Same |
| `testfun_deriv_bound` | `quadmodel_accuracy.v:1035` | `Quadrature.Binary64.testfun_deriv_bound` | `Quadrature.Examples.CosineCallback` | Same |
| `testfun_function_accuracy` | `quadmodel_accuracy.v:1077` | `Quadrature.Binary64.testfun_function_accuracy` | `Quadrature.Examples.CosineCallback` | Different: assumes a cosine within `10⁻¹⁵` on `[-1, 1]` and gives `5·10⁻¹⁵`; Rocq derives its bound for VSTlib's `cos` with VCFloat |
| `body_gauss_point` | `C/verif_quadrules.v:43` | `Quadrature.CSource.Typed.body_gauss_point` | `Quadrature.CSource.Accessors.Calls` | Different: one terminating execution in the strategy semantics of the function elaborated from the C source, in place of VST's `semax_body`; for `n, i ≤ 10`, if the table holds `value` at the offset of entry `i` of rule `n`, the call returns `value` and `AccessorExit` describes the memory. Rocq's spec has `1 ≤ n ≤ 10`, `i < n` and the entry of `gauss_pts_list` under the table predicate. `CSource.C.accessor_call_correct` covers every execution of the small-step semantics |
| `body_gauss_weight` | `C/verif_quadrules.v:83` | `Quadrature.CSource.Typed.body_gauss_weight` | `Quadrature.CSource.Accessors.Calls` | Different: one terminating execution in the strategy semantics of the function elaborated from the C source, in place of VST's `semax_body`; as `body_gauss_point`, for the weight table and `gauss_wts_list` |
| `body_integrate` | `C/verif_quadrules.v:294` | `Quadrature.CSource.Typed.body_integrate` | `Quadrature.CSource.Integrator.Function` | Different: one terminating execution in the strategy semantics of the function elaborated from the C source, in place of VST's `semax_body`; for at most ten stored terms laid out in memory (`TableCells`) and a callback that returns `f x` silently from every memory (`SourceCallbackContract`), the call returns `integrate_model_f f terms`. Rocq's spec has `n : 'I_5` and the fixed tables. `CSource.C.integrator_call_correct` covers every execution of the small-step semantics |
| `body_integrate_testfun` | `C/verif_quadrules.v:356` | `Quadrature.CSource.Typed.body_integrate_testfun` | `Quadrature.CSource.Wrapper.Accuracy` | Different: one terminating execution in the strategy semantics of the function elaborated from the C source, in place of VST's `semax_body`; the cosine is external, under an execution contract and the accuracy contract `CosineContract`. It also proves the result equal to `integrate_model_f` and finite, with the bound `0.00356` where Rocq's spec has `0.00425`. `CSource.C.wrapper_call_correct` covers every execution of the small-step semantics |

### Rocq declarations without a Lean counterpart

The same files contain 273 further declarations. They are library plumbing, intermediate proof
steps, restatements and VST plumbing, and the Lean development does their work with other tools
or other proofs. The table lists all of them in groups.

| Rocq declarations | Rocq file | What the Lean development uses instead |
| --- | --- | --- |
| `size_behead`, `tuple_behead`, `tuple_ext`, `tuple_rehead`, `sorted_ij`, `size_ord_enum`, `nth_ord_enum'`, `nth_List_nth`, `ord_enum_cases`, `index_enum_ord_enum`, `append1fun`, `append1fun_last`, `append1fun_notlast`, `iseq`, `nth_iseq` | `quadrature.v` | Functions on `Fin n` and sums over `Finset.univ`. The `iseq` lists of rules become dependent functions on `Fin 5`. |
| `hornerXsubC'`, `hornerX'`, `hornerC'`, `hornerD'`, `hornerM'`, `hornerN'`, `hornerD''`, `hornerX_i`, `horner_sum'`, `r_horner`, `poly0`, `mul_polyC'`, `polyCN`, `polynil`, `polynil_eq`, `polyC1'`, `polyC'`, `polyC0'`, `polyX'`, `polyX2'`, `polyX3'`, `polyX4'`, `polyX5'`, `polyX6'`, `polyX7'`, `polyX8'`, `size_polyseq_coeffs'`, `size_polyseq_coeffs`, `scale_polyC'`, `mulrA'X`, `norm_poly`, `mul_polyC_polyC`, `add_polyC_polyC` | `quadrature.v` | Mathlib's `Polynomial.eval` and `Polynomial.C` lemmas, `simp` and `ring`. |
| `mul_fun1r`, `mul_funr1`, `mul_fun0r`, `mul_funr0`, `opp_funC`, `opp_funr0`, `sub_funr0`, `add_fun0r`, `add_funr0`, `mul_funDr`, `mul_funDl`, `mul_funA`, `mul_funC`, `mul_fun_consts`, `r_ring`, `r_lift`, `mulrD`, `eq_opI`, `sub_mul2`, `opp_sub`, `add_mul2`, `add_mul3`, `sqrt_exists`, `sqr_sqrt` | `quadrature.v` | Integrands written as `fun x => …`, rewritten with `simp` and `ring`; Mathlib's `Real.sqrt` lemmas. |
| `integ`, `deriv_integ`, `derivable_oo_LRcontinuous_horner`, `Rintegral_poly`, `bounded_range`, `within_compact_continuous_bounded`, `in_within_continuous`, `continuous_bounded`, `continuousM'`, `within_continuous_measurable_fun`, `in_continuous_measurable_fun`, `in_continuous_cst`, `in_continuousN`, `in_continuousB`, `in_continuousD`, `in_continuousM`, `in_continuous_horner`, `Rintegral_gt_0`, `wmeasurable`, `intgal_linear1`, `intgal_linear2`, `intgal_sum` | `quadrature.v` | Mathlib's interval integral, `ContinuousOn` and `fun_prop`, and SymLean's `polynomialIntegral` lemmas; `polynomialIntegral_square_pos` does the work of `Rintegral_gt_0`. |
| `fine_itv` | `quadrature2.v` | Mathlib's `Real.volume_Icc`. |
| `stewart_lemma_23_6`, `orthogonal_polynomials_upto`, `polySn_orthogonal_n`, `ortho_p_orthogonal_special'`, `ortho_p_orthogonal'` | `quadrature.v` | Orthogonality of `ortho_p` is proved by identifying it with SymLean's orthogonal family (`ortho_p_eq_integralOrthogonalPolynomial`). |
| `same_members_increasing_equal`, `zeros_of_ortho_p`, `extend_roots`, `extend_roots_injective`, `extend_rootsE`, `L` | `quadrature.v` | Mathlib's `StrictMono.range_inj_of_wellFoundedLT` for the uniqueness of sorted roots, the field `ROOTS_vals` for the roots, and Mathlib's `Lagrange.basis` over `Finset.univ`, which needs no extension of the roots to all natural numbers. |
| `intgal_linear1`, `intgal_linear1'`, `intgal_linear1''`, `intgal_linearN`, `intgal_linearN'`, `intgal_linear2`, `intgal_linear2'`, `intgal_linear`, `r_integral`, `intgal_X`, `intgal_0`, `intgal_1`, `intgal_C`, `intgal_X2`, `intgal_X3`, `intgal_X4`, `intgal_X5`, `intgal_X6`, `intgal_X7`, `intgal_X8`, `r_intgal`, `pull_left1`, `pull_left2`, `pull_left`, `pull_left1'`, `pull_left2'` | `quadrature.v` | These are in `Module Legendre`, which has its own `intgal_linear1` and `intgal_linear2`. The explicit weights are read off the interpolatory weights of SymLean's Gauss–Legendre rules, so no monomial integrals are rewritten by hand. |
| `Gauss_Legendre_quadrature'`, `GL_same` | `quadrature.v` | An unfolded form of `Gauss_Legendre_quadrature` and the proof that the two agree; ours is defined once. |
| `derive1M`, `everywhere_derivable`, `derive1M_`, `derive1_cst'`, `derive1_cos`, `derive1_sin`, `derive1_add`, `derive1_opp`, `opp_funK`, `ev_deriv_cos`, `ev_deriv_sin`, `range_Rabs`, `derivE_rev`, `ev_deriv_horner`, `ev_derivD`, `ev_derivB`, `ev_derivN`, `ev_derivM`, `ev_deriv_cst`, `r_deriv`, `r_derive1`, `true_andb_e1`, `true_andb_e2`, `conj'` | `quadrature2.v` | Mathlib's `HasDerivAt` lemmas and `fun_prop`. SymLean's interval tactic and `linarith` take real inequalities as they are, so no boolean constraints need converting. |
| `g_max_deriv_oneway` | `quadrature2.v` | Mathlib's mean value inequality on a convex set covers both signs of the step at once, in `g_max_deriv`. |
| `r_intgal_C`, `legendre_integral2`, `legendre_integral2_iseq`, `error_1_0_1`, `error_1_0_2` | `quadrature2.v` | The integrals of `(legendre n)²` normalize Rocq's `quadrature_error_bound`, and `error_1_0_1` and `error_1_0_2` are stated with it. Our `quadrature_error_bound` squares `legendre n` where theirs squares `legendre n.+1`, so we prove the errors of the cosine example directly, in `error_1_0_1'` and `two_point_bound`. |
| `testfun_b`, `n`, `testfun_quadrature_error_bound` | `quadmodel_accuracy.v` | These instantiate `error_1_0_2` for the cosine example, so the previous row applies. |
| `cos` | `quadmodel.v` | VSTlib's binary64 cosine, reified for VCFloat. Our `testfun_f` takes the binary64 cosine as an argument. |
| `float_near` | `quadmodel.v` | A relative error bound for a stored constant. Our certificates bound the absolute node and weight errors. |
| `gauss_pts_list`, `gauss_wts_list`, `gauss_point_f`, `gauss_weight_f` | `quadmodel.v` | The stored tables `oneStored` to `fourStored` in Rules/Basic, and `StoredRule.table` in Rules/Tables, decoded from the bits of the C tables with the same triangular offset. |
| `gauss_pt_range`, `gauss_wt_range`, `g_max_deriv`, `integrate_model_f` | `quadmodel_accuracy.v` | Restatements, inside the `FLOAT` section, of the declarations of the same names; each is listed once in the name table. |
| `testfun_r` | `C/spec_quadrules_highlevel.v` | A restatement of `testfun_r` from `quadmodel_accuracy.v`, listed once in the name table. |
| `BMULT_correct`, `Rabs_le_conversion`, `Rabs_le_pos`, `RrangeP`, `sumB`, `rev_list_rev`, `Forall2_forall`, `big_sum_const_seq`, `big_sum_const`, `Rle_big_compat`, `feq_FT2R` | `quadmodel_accuracy.v` | Mathlib's `Finset.sum` and absolute value lemmas, and FloatLib's rounding lemmas. |
| `finite`, `gauss_pts_accuracy`, `gauss_wts_accuracy`, `gauss_wt_f_range` | `quadmodel_accuracy.v` | The fields of `StoredRule.Certificate` and their consequence `sum_abs_weights_le`. |
| `parameter_limits`, `maxwf`, `fb_limit_simple`, `integrate_model_r`, `integrate_model_acc`, `gauss_pt_wt_limit_aux`, `gauss_pt_wt_acc`, `gauss_pt_wt_bound`, `dotprodF'`, `dotprodF_dotprodF'_feq`, `dotprodF_dotprodF'_finite`, `finite_integrate_condition`, `Fsum_gauss_wt_pt_finite`, `dotprodF_finite_from_bounded`, `integrate_model_f_alt`, `integrate_model_f_alt_eq`, `integrate_model_r_eq` | `quadmodel_accuracy.v` | Our proof goes through `samples_error`, the range budget and the reduction tree of the loop, and writes its bound out in the statement of `integrate_model_roundoff_err`; the range budget replaces `parameter_limits` and `finite_integrate_condition`. |
| `gauss_points_acc`, `gauss_weights_acc`, `gauss_point_f_acc`, `gauss_weight_f_acc`, `gauss_weight_f_range` | `quadmodel_accuracy.v` | `oneStored_certificate` to `fourStored_certificate` in Rules/Basic and `StoredRule.table_certificate` in Rules/Certificates. |
| `testfun_mcr`, `ler_pdist`, `testfun_mcr_deriv_bound`, `testfun_mcr_fbound`, `testfun_rE` | `quadmodel_accuracy.v` | `testfun_fbound` and `testfun_deriv_bound`, proved directly about `Real.cos`. |
| `_x`, `testfun_bmap`, `testfun_reified`, `testfun_vmap_list`, `testfun_vmap`, `testfun_f_acc`, `testfun_f_acc_simple`, `testfun_function_accuracy'` | `quadmodel_accuracy.v` | VCFloat's automatic rounding analysis. We bound the three rounded operations of the callback by hand in `testfun_error`, with the cosine's error as a hypothesis. |
| `testfun_parameter_limits` | `quadmodel_accuracy.v` | The two-point program proves every operation finite directly, in `two_point_roundoff`. |
| `f_i_cond` | `C/verif_quadrules.v` | `finite_integrate_condition` for the cosine example, which `two_point_roundoff` does not need for the same reason. |
| `CompSpecs`, `Vprog`, `InhR`, `init_data_tarray_tdouble`, `gauss_pts_pred`, `gauss_wts_pred`, `gauss_pts_match`, `gauss_wts_match` | `C/spec_quadrules.v` | VST's program environment and the separation-logic predicates for the two tables. Our execution theorems read the tables from memory through `TableCells` and the decoded table data. |
| `gauss_point_spec_lowlevel`, `gauss_weight_spec_lowlevel`, `floatfun_spec`, `integrate_spec_lowlevel`, `testfun_spec`, `integrate_testfun_spec_lowlevel` | `C/spec_quadrules.v` | The `body_*` theorems state their preconditions and conclusions directly; `CSource.C.SourceCallbackContract` plays the part of `floatfun_spec`. |
| `InhR`, `gauss_point_spec`, `sub_gauss_point`, `gauss_weight_spec`, `sub_gauss_weight`, `integrate_spec`, `sub_integrate`, `integrate_testfun_spec`, `quadrules_ASI` | `C/spec_quadrules_highlevel.v` | The same direct statements; Lean has no separate layer of high-level specifications and subsumption proofs. |
| `quadrules_E`, `quadrules_internal_specs`, `quadrules_imported_specs`, `quadrules_globals`, `Gprog`, `divs_repr` | `C/verif_quadrules.v` | VST's function environment and signed division. Our execution theorems name the functions they call, and the table offset is evaluated in the C semantics. |
| `integrate_upto`, `integrate_upto_n` | `C/verif_quadrules.v` | The loop invariant of `integrate`; ours is `CSource.C.IntegratorState`, used in `body_integrate`. |
| `gauss2d_npoint1d_spec`, `gauss2d_point_spec`, `gauss2d_weight_spec`, `hughes_points`, `hughes_point_spec`, `hughes_weight`, `hughes_weight_spec`, `body_gauss2d_npoint1d`, `body_gauss2d_point`, `body_gauss2d_weight`, `body_hughes_point`, `body_hughes_weight` | `C/spec_quadrules.v`, `C/spec_quadrules_highlevel.v`, `C/verif_quadrules.v` | The two-dimensional and triangle rules of the C file, which simple_cfem-lean does not verify. |

Lean-only declarations keep Lean names. Among them are the bridges to SymLean such as
`ortho_p_eq_integralOrthogonalPolynomial` and `roots_of_ortho_p.toGaussianRule`, the stored
tables and their certificates, the cosine example in Examples, and the end-to-end theorems about
the C programs.

The Rocq files in [`rocq/`](../rocq) use the same names for the declarations that have
simple_cfem counterparts: `function_accuracy`, `integrate_model_f`, `body_gauss_point`,
`body_gauss_weight`, `body_integrate` and `body_integrate_testfun`.
