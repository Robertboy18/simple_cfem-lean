/-
Copyright (c) 2026 simple_cfem-lean Team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: simple_cfem-lean Team
-/
import Quadrature.CSource.Library.Preservation
import Quadrature.Clight.Main

/-!
# From initialized C returns to Clight application observations

The C library returns its result silently, while the Clight application of
`Quadrature.Clight.Main` reports the returned binary64 value in a `quadrature-result` annotation
and exits zero. So a return of `value` corresponds to the observation `resultTrace value` with
exit status zero. The cosine bodies of the two programs differ in syntax but compute the same
rounded polynomial.

## Main results

* `normalized_application_observations_iff`: a return of the integrator in the normalized Clight
  library gives exactly the final observations of the Clight application, for zero through ten
  nodes.
* `application_observations_iff`: the same for the initialized typed C integrator, in every
  operand evaluation order.

## How it works

Both ends are pinned to one value. `initialized_refinement` shows that every completed call of
the initialized integrator returns `Clight.StoredPolynomial.result n` with the empty trace, and
`Clight.Application.return_specification` shows that every completed run of the application
emits that value and exits zero. Both theorems assume deterministic external calls, as the
application theorem does.
-/

namespace Quadrature.CSource.Library

open CC Binary64 FloatLib.Floats.Formats.BinaryInterchange

/-- Reporting a return from the actual normalized library gives exactly the final observations
of the Clight application. This includes initialization on each side. -/
theorem normalized_application_observations_iff [calls : ExternalCalls]
    [ExternalCallsDeterministic calls] (n : Nat) (hn : n ≤ 10)
    (trace : Trace) (status : Integers.Int) :
    (∃ value : Value,
      ClightOutcome Normalized.program ClightSource._integrate
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        E0 (.Vfloat value) ∧
      trace = Clight.Application.resultTrace value ∧ status = Integers.Int.zero) ↔
    (∃ start memory, InitialState (Clight.Application.program n) start ∧
      Star (Step2 (Clight.Application.program n).globalenv) start trace
        (.Returnstate (.Vint status) .Kstop memory)) := by
  have hreturn (value : Value) :
      ClightOutcome Normalized.program ClightSource._integrate
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        E0 (.Vfloat value) ↔ value = Clight.StoredPolynomial.result n := by
    simpa using (initialized_refinement (.integrate n hn)).target_outcome_iff
      E0 (.Vfloat value)
  constructor
  · rintro ⟨value, hvalue, rfl, rfl⟩
    obtain rfl := (hreturn value).mp hvalue
    exact ⟨Clight.Application.initialState n, Clight.Application.entryMemory,
      Clight.Application.initial_state n, Clight.Application.execution n hn⟩
  · rintro ⟨start, memory, hinit, hrun⟩
    obtain ⟨htrace, hstatus, _⟩ := Clight.Application.return_specification n hn
      start trace (.Vint status) memory hinit hrun
    exact ⟨Clight.StoredPolynomial.result n, (hreturn _).mpr rfl,
      htrace, Val.Vint.inj hstatus⟩

/-- The same application observations come from the initialized typed C integrator, with every
operand evaluation order covered by its call-refinement theorem. -/
theorem application_observations_iff [calls : ExternalCalls]
    [ExternalCallsDeterministic calls] (n : Nat) (hn : n ≤ 10)
    (trace : Trace) (status : Integers.Int) :
    (∃ value : Value,
      polynomialLibrary.InitializedOutcome ClightSource._integrate
        [.Vptr (Positive.ofNat 6) Integers.Ptrofs.zero, .Vint (Integers.Int.repr n)]
        E0 (.Vfloat value) ∧
      trace = Clight.Application.resultTrace value ∧ status = Integers.Int.zero) ↔
    (∃ start memory, InitialState (Clight.Application.program n) start ∧
      Star (Step2 (Clight.Application.program n).globalenv) start trace
        (.Returnstate (.Vint status) .Kstop memory)) := by
  simp only [initialized_outcomes_iff (.integrate n hn)]
  exact normalized_application_observations_iff n hn trace status

end Quadrature.CSource.Library
