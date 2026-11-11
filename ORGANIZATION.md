# Organization of the Lean and Rocq files

This repository proves in Lean the Gaussian quadrature of
[simple_cfem](https://github.com/VeriNum/simple_cfem): the mathematics of `proof/quadrature.v` and
`proof/quadrature2.v`, the floating-point model of `proof/quadmodel.v` and
`proof/quadmodel_accuracy.v`, and the C functions of `src/quadrules.c` that `proof/C/` verifies.
The Rocq files in `rocq/` carry the same programs through CompCert. The organization is as
follows:

simple_cfem-lean (root directory, name of git repository)
  - README.md  (what is proved, and how to build)
  - ORGANIZATION.md  (this outline)
  - LICENSE, NOTICE  (Apache 2.0, and the files that keep other terms)
  - lakefile.toml, lake-manifest.json, lean-toolchain  (Lean build; pins Mathlib, FloatLib and SymLean)
  - Quadrature.lean  (root module: imports every module; the layers of the proof and the notation)
  - Quadrature  (the Lean library, by subject)
    - Gaussian  (`quadrature.v`, Stewart's paragraphs 1 to 19, under the Rocq names; the theory itself is in SymLean)
      - Orthogonal.lean  (paragraphs 1 to 12: `intgal`, `orthogonal`, `three_term_recurrence`, `ortho_p`)
      - Rule.lean  (paragraphs 13 to 19: `roots_of_ortho_p`, `gauss_weight`, `G`, exactness, positivity, `quadrature_error`)
    - Legendre  (paragraph 21: the module `Legendre` of `quadrature.v`, and `quadrature2.v`)
      - Basic.lean  (`legendre`, `legendre_roots`, `gauss_weights`, `Legendre_poly_0` to `Legendre_poly_4`)
      - Rules.lean  (explicit roots and weights through four nodes, `Gauss_Legendre_quadrature`)
      - Bounds.lean  (`fbound`, `deriv_bound`, `g_max_deriv` of `quadrature2.v`)
    - Binary64  (FloatLib binary64 arithmetic: `quadmodel.v`'s `integrate_model_f` and its rounding errors)
    - Rules  (the stored tables of `quadrules.c`, their certificates, and the accuracy theorem of `quadmodel_accuracy.v`)
      - RootData.lean  (rational Legendre root brackets for orders 5 to 10, generated, checked by Lean)
    - Examples  (the integrand `testfun`: its bounds from `quadmodel_accuracy.v`, the errors of `quadrature2.v`, and the polynomial cosine)
    - CSource  (`quadrules.c` read and proved in an adaptation of CompCert 3.17's C semantics)
      - Frontend  (the source bytes, lexer, parser, elaboration to C and translation to Clight, checked against `clightgen`)
      - Semantics  (C syntax and small-step semantics; total correctness in every evaluation order)
      - Accessors, Integrator, Callback, Wrapper  (`gauss_point`, `gauss_weight`, `integrate`, `testfun`, `integrate_testfun`)
      - Cosine  (`cosine.c`, a C polynomial that replaces `cos`, and its execution)
      - Tables  (the decimal literals of the two C tables)
      - Library  (the initialized library: total correctness, accuracy, and preservation to Clight)
    - Clight  (the clightgen output, its table data, and the ten initialized Clight applications in CLean's semantics)
  - vendor/clean  (the modules of Certora's CLean, the Clight semantics in Lean, that our proofs use, with our changes listed in its README)
  - rocq  (the Rocq proofs, under the logical name `QuadratureC`; `_CoqProject` lists them in build order)
    - arithmetic  (range, rounding and exact values of CompCert's binary64 operations)
    - hermite  (real polynomials as lists, Hermite interpolation and its remainder by repeated Rolle)
    - clight  (`quadrules.v`, simple_cfem's clightgen output, and the Clight executions: `body_gauss_point`, `body_gauss_weight`, `body_integrate`, `body_integrate_testfun`, the applications)
    - accuracy  (table errors, roundoff and `function_accuracy` for the C results; the error of the two-point and ten polynomial applications)
    - analysis  (the remainder constants of the rules with one to four nodes, and integral accuracy of `integrate`)
    - compilation  (lowering to Cminor, CompCert's backend theorems, and every behavior of the compiled applications)
    - certification  (the CompCert configuration, explained at the top of `configuration.patch`, and the three assembly certificates)
  - scripts
    - check-lean.py, Audit.lean  (`lake build`, then the axiom audit of every theorem)
    - check-rocq.py, check-configured-compcert.py, rocqcheck.py  (the Rocq proofs in the pinned container, against CompCert 3.17 and against the configured CompCert)
    - check-rocq-names.py  (the name table of `docs/comparison.md` against simple_cfem and the Lean build)
    - import-c-source.py, import-clight-functions.py, import-clight-tables.py  (the generated source, Clight and table files; `--check` compares)
    - generate-legendre-root-data.py  (writes `Quadrature/Rules/RootData.lean`)
    - tests  (Python tests of the checkers: `python3 -m pytest scripts/tests`)
  - docs
    - comparison.md  (Stewart's paragraphs and the table of declaration names, against simple_cfem)

The Lean files follow Mathlib's style. `lake build` runs Mathlib's standard linters on
`Quadrature` and treats warnings as errors in both `Quadrature` and `CCLib`. A declaration that
restates one of simple_cfem keeps its name, and a generated file is changed through its
generator.
