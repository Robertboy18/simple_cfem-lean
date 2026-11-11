# simple_cfem-lean: the Gaussian quadrature of simple_cfem, proved in Lean down to the C code

I wanted to see whether the whole argument of simple_cfem's quadrature proofs can be carried out
in Lean, from Mathlib's real analysis down to a C semantics. So we proved the Gaussian quadrature
of [simple_cfem](https://github.com/VeriNum/simple_cfem) in Lean 4, all the way to the C code.
simple_cfem is the finite element code in C that Andrew Appel and David Bindel verify in Rocq with
VST and CompCert. Lean reads the text of their `quadrules.c` and links it with our
[`cosine.c`](Quadrature/CSource/Cosine/cosine.c), a degree-14 polynomial that stands in for the
platform `cos`. Then `integrate_testfun` returns a finite double within 0.00356 of the integral it
approximates, in every order of evaluation that C allows.

Lean's kernel checks every proof, with only the axioms `propext`, `Classical.choice` and
`Quot.sound`. To trust the result, you read the statements and the definitions they mention, and on
the C side you trust clightgen, as with VST, and our adaptation of CompCert's C semantics.

We follow Appel and Bindel's files and keep their names, so the two developments can be read side
by side. [`docs/comparison.md`](docs/comparison.md) says for each of our statements whether it is
the same as theirs, the same up to encoding, or different, and how. The Rocq proofs in
[`rocq/`](rocq) carry the same programs through CompCert to x86-64 assembly.

## Example

The end of `quadrules.c` is a small Gauss–Legendre program, with `cos` declared `extern`:

```c
double integrate (double (*f)(double), int n) {
  int i;
  double s = 0.0;
  for (i=0; i<n; i++)
    s += gauss_weight(i,n) * f(gauss_point(i,n));
  return s;
}

double testfun(double x) {
  return 0.5 * (1-x) * cos(x);
}

double integrate_testfun (void) {
  return integrate(&testfun, 2);
}
```

`gauss_point(i,n)` and `gauss_weight(i,n)` read node and weight `i` of the `n`-point rule from two
static tables of decimal literals, which hold ten Gauss–Legendre rules. This is what we prove, in
[`Quadrature/CSource/Library/Total.lean`](Quadrature/CSource/Library/Total.lean):

```lean
variable [ExternalCalls]

theorem parsed_wrapper_total_accuracy :
    ∃ library value,
      fromSources CSourceData.source Cosine.source = some library ∧
      library.InitializedCallCorrect _integrate_testfun [] (.Vfloat value) ∧
      value = Model.ofNatBits 0x3fead02c771c35ed ∧
      Model.isFinite value = true ∧
      |Model.toReal value - ∫ x in (-1 : ℝ)..1, Example.testfun_r x| ≤
        (356 : ℝ) / 100000
```

`CSourceData.source` is every byte of `quadrules.c` and `Cosine.source` is `cosine.c`.
`fromSources` parses and elaborates the five one-dimensional functions, the two tables and the
cosine. `InitializedCallCorrect` initializes the globals and calls `integrate_testfun`: every
execution of the call, in every order the C semantics permits, takes only silent steps, never gets
stuck, terminates with `value`, and leaves every block the caller had allocated as it was.

`testfun_r x` is `(1 / 2) * (1 - x) * Real.cos x`, whose integral over [−1, 1] is sin 1, about
0.8414709848. The returned double is 0.8379118276949932, so the error is 0.0035592, close to the
bound. No hypothesis about the cosine, the tables or the callback is left. `integral_total_accuracy`
says the same of `integrate` at each of the ten stored orders, with that order's bound.

## What we prove

The proof has four parts, following simple_cfem's `quadrature.v`, `quadrature2.v`, `quadmodel.v`,
`quadmodel_accuracy.v` and `proof/C/`.

1. Mathematics. For a continuous positive weight, the rule at the roots of the orthogonal
   polynomial is exact below degree `2n`, its weights are positive, and its error is the classical
   remainder, from Hermite interpolation and the generalized Rolle theorem. These are
   `quadrature_exact_for`, `gauss_weight_positive` and `quadrature_error`, in
   [`Quadrature/Gaussian/Rule.lean`](Quadrature/Gaussian/Rule.lean). Here `n` is the number of
   points, as in simple_cfem.
2. The tables. Lean decodes every decimal literal in `gauss_pts` and `gauss_wts` to binary64 and
   shows that the ten stored rules are within 6·10⁻¹⁶ (nodes) and 5·10⁻¹⁶ (weights) of the
   Gauss–Legendre rules.
3. Rounding. With FloatLib's model of IEEE 754, `integrate_model_err` shows that the binary64 loop
   `integrate_model_f` is finite and within an explicit bound of the integral, given bounds on the
   integrand and on the callback's error.
4. The C code. We parse `quadrules.c`, elaborate it to typed C and to Clight, and prove each call
   in an adaptation of CompCert's small-step semantics of C, with a total-correctness statement
   where VST has `semax_body`. C leaves the order of evaluation open, so the proof follows every
   step the semantics permits. Most of the work is here.

The C theorems above don't go through parts 1 to 3. Lean computes in the kernel the bits that the
loop returns at each stored order and compares them with an enclosure of sin 1, and part 4 shows
that the C code returns these bits. Part 3 reaches C in
`Binary64.Clight.stored_callback_execution_accuracy`, which bounds the call of each stored order for
a general callback.

## What you need to trust

- The statements and the definitions they mention, most of them in
  [`Quadrature/Gaussian/`](Quadrature/Gaussian) and [`Quadrature/Rules/`](Quadrature/Rules), and
  three definitions in [SymLean](https://github.com/Robertboy18/SymLean): `GaussianRule`,
  `polynomialIntegral` and `Legendre.Rule`.
- The C text. [`SourceData.lean`](Quadrature/CSource/Frontend/SourceData.lean) holds every byte of
  `quadrules.c`. Our C reader is not proved correct. Instead the kernel checks that its Clight output
  for each of the five functions equals clightgen's output in simple_cfem's `proof/C/quadrules.v`,
  kept unchanged in [`rocq/clight/quadrules.v`](rocq/clight/quadrules.v), and `parsed_refinement`
  proves that the typed C and Clight versions of each call return the same bits. So, as with VST,
  you trust clightgen.
- The C semantics. The files in [`Quadrature/CSource/Semantics/`](Quadrature/CSource/Semantics)
  adapt CompCert's `Csyntax.v`, `Csem.v` and `Cstrategy.v`. Under them is part of Certora's port of
  CompCert to Lean, in [`vendor/clean/`](vendor/clean), with FloatLib's arithmetic in place of
  native floats.
- Lean's kernel.

[`ORGANIZATION.md`](ORGANIZATION.md) outlines the files.

## Building and checking

Install Lean with [elan](https://github.com/leanprover/elan). Then download Mathlib's compiled
files and build:

```sh
lake exe cache get
lake build
```

The cache covers Mathlib only, so this also compiles SymLean, FloatLib, the CompCert port and this
library. Warnings are errors. Then check the axioms of the main theorems. Each line it prints ends
with `depends on axioms: [propext, Classical.choice, Quot.sound]`:

```sh
printf 'import Quadrature\n#print axioms Quadrature.quadrature_exact_for\n#print axioms Quadrature.gauss_weight_positive\n#print axioms Quadrature.quadrature_error\n#print axioms Quadrature.Binary64.StoredRule.table_certificate\n#print axioms Quadrature.Binary64.StoredRule.Certificate.integrate_model_err\n#print axioms Quadrature.CSource.Library.integral_total_accuracy\n#print axioms Quadrature.CSource.Library.parsed_wrapper_total_accuracy\n' | lake env lean --stdin
```

`python3 scripts/check-lean.py` checks every theorem at once, private and generated ones included,
and also fails if a file under `Quadrature/` is not imported by `Quadrature.lean`.

To look for ways around the kernel:

```sh
grep -rnwE 'implemented_by|extern|csimp|unsafe|partial|opaque|native_decide|sorry|axiom' --include='*.lean' Quadrature.lean Quadrature vendor/clean
```

None of the matches is a Lean attribute, declaration or tactic. They are the C keyword `extern` in
our C reader and its tests, and English words in comments. Our computations, such as decoding the
tables, run in the kernel through `decide +kernel`.

With a simple_cfem checkout next to this one, these commands check that our copies of its C text,
its clightgen output, its five functions and two tables, and the names in `docs/comparison.md` match
it:

```sh
python3 scripts/import-c-source.py ../simple_cfem/src/quadrules.c --check
cmp rocq/clight/quadrules.v ../simple_cfem/proof/C/quadrules.v
python3 scripts/import-clight-functions.py --check
python3 scripts/import-clight-tables.py --check
python3 scripts/check-rocq-names.py --simple-cfem ../simple_cfem
```

## The Rocq proofs

In [`rocq/`](rocq), CompCert 3.17 compiles twelve programs to x86-64 assembly, by evaluation inside
Rocq, with every optimization off. They are the two-point program with an external `cos`, the
two-point program with the polynomial cosine, and the program with the polynomial cosine for each
of the ten stored orders. Every behavior of each assembly program terminates and reports a finite
value within the bound that Lean proves for that order. The Rocq bound for a general integrand
covers the rules with one to four nodes and stops at Cminor.
[`rocq/hermite/`](rocq/hermite) proves Hermite interpolation and its remainder by repeated Rolle,
with Coquelicot.

Two scripts check the Rocq side. They run `coqc` in a pinned Docker image with no network, against
CompCert, MathComp and Coquelicot at the revisions the scripts pin:

```sh
python3 scripts/check-rocq.py --compcert-root ../CompCert --mathcomp-root ../math-comp \
    --coquelicot-root ../coquelicot --work-dir /tmp/check-rocq
python3 scripts/check-configured-compcert.py --compcert-root ../CompCert \
    --work-dir /tmp/check-configured
```

The first compiles the proofs against unmodified CompCert. The second applies
[`configuration.patch`](rocq/certification/configuration.patch), which fixes the backend choices
that CompCert leaves to OCaml, and compiles the assembly certificates. Both fail on `Admitted`, on a
declared axiom or parameter, and on any assumption beyond Rocq's classical axioms and CompCert's
axiomatized external functions.

## What is not proved

- The two-dimensional and triangle rules of `quadrules.c` (`gauss2d_*`, `hughes_*`), and any
  format but binary64. Our C reader covers only the C that `quadrules.c` and `cosine.c` use.
- The platform `cos`. With an external cosine, `body_integrate_testfun` assumes that the call returns
  a value within 10⁻¹⁵ of `cos` at the two nodes, and concludes one terminating execution, not every
  execution.
- A link between the Lean and Rocq semantics. The Lean proofs stop at Clight and the Rocq ones start
  from CompCert's Clight, so the two sides are separate results about corresponding programs. The
  `--check` commands compare the Lean copies of the functions and tables with `quadrules.v`.
- A link between FloatLib's binary64 and Flocq's.

## Credits

Thank you to Andrew Appel and David Bindel for simple_cfem: the C program, its tables and
specifications, and the names all come from it. Takafumi Saikawa's proofs there and his
MathComp-Analysis [pull request 2086](https://github.com/math-comp/analysis/pull/2086) are
credited in the modules that follow them. The mathematics follows Lecture 23 of G. W. Stewart's
*Afternotes on Numerical Analysis* (SIAM, 1996), as `quadrature.v` does. The general theory is in
[SymLean](https://github.com/Robertboy18/SymLean), our computer algebra system for Lean, the
binary64 arithmetic in [FloatLib](https://github.com/lean-dojo/FloatLib), and the Clight semantics
in Certora's [CLean](https://github.com/Certora/clean), adapted in [`vendor/clean`](vendor/clean).

## License

The license is Apache 2.0 ([LICENSE](LICENSE)), except for the files listed in [NOTICE](NOTICE),
which keep the terms of CompCert, CLean and simple_cfem.
