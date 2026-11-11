(* Copyright (c) 2026 simple_cfem-lean Team.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: simple_cfem-lean Team *)
(** * QuadratureC.compilation.AsmApplication: the two-point application in assembly *)

(** If CompCert's backend compiles the Cminor application to an assembly program then, under the
    contracts for [cos], every behavior of that program is the terminating one with the two-
    point result. *)

From Coq Require Import List.
From compcert Require Import Errors Integers Values Events Globalenvs Smallstep
  Behaviors Ctypes Clight Compiler Asm.
From QuadratureC.clight Require Import ClightExample ClightApplication.
From QuadratureC.compilation Require Import CminorApplication CompilerBackend.
From QuadratureC.clight Require Import AnnotatedBehavior.

Import ListNotations.
Module App := ClightApplication.

Section SuccessfulCompilation.
Variable assembly_program : Asm.program.
Hypothesis compiled :
  Compiler.transf_cminor_program CminorApplication.cminor_program =
    OK assembly_program.

Theorem application_forward_simulation :
  forward_simulation (Clight.semantics2 App.application)
    (Asm.semantics assembly_program).
Proof.
  eapply compose_forward_simulations.
  - exact CminorApplication.application_forward_simulation.
  - apply successful_cminor_compilation_forward. exact compiled.
Qed.

Section ExternalCosine.
Hypothesis cosine_left : external_call cosine_external App.ge [Vfloat left_node]
  App.initial_memory E0 (Vfloat cosine_value) App.initial_memory.
Hypothesis cosine_right : external_call cosine_external App.ge [Vfloat right_node]
  App.initial_memory E0 (Vfloat cosine_value) App.initial_memory.

Theorem application_terminates :
  program_behaves (Asm.semantics assembly_program)
    (Terminates App.result_trace Int.zero).
Proof.
  eapply CminorApplication.forward_simulation_termination.
  - exact application_forward_simulation.
  - exact App.main_initial_state.
  - exact (App.main_steps cosine_left cosine_right).
  - constructor.
Qed.

Theorem application_all_behaviors beh :
  program_behaves (Asm.semantics assembly_program) beh ->
  beh = Terminates App.result_trace Int.zero.
Proof.
  eapply annotation_terminating_behavior_unique.
  - apply Asm.semantics_determinate.
  - repeat constructor.
  - exact application_terminates.
Qed.

End ExternalCosine.
End SuccessfulCompilation.
