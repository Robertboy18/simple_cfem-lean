(* Copyright (c) 2026 simple_cfem-lean Team.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: simple_cfem-lean Team *)
(** * QuadratureC.compilation.ApplicationAccuracy: accuracy of the two-point application *)

(** Under the contracts for the two calls of [cos], every behavior of the two-point application,
    in Clight, in Cminor and in any assembly program that CompCert's backend produces from it,
    terminates with a finite result within [0.00356] of the integral. *)

From Coq Require Import List Reals String.
From Flocq Require Import IEEE754.Binary.
From compcert Require Import Errors Integers Floats Values Events Globalenvs Behaviors
  Clight Cminor Compiler Asm.
From QuadratureC.clight Require Import ClightExample ClightApplication.
From QuadratureC.compilation Require Import CminorApplication AsmApplication.
From QuadratureC.accuracy Require Import ValueAccuracy ExampleIntegral.

Import ListNotations.
Local Open Scope R_scope.
Local Open Scope string_scope.
Module App := ClightApplication.

(** A behavior is accurate when it terminates with the annotation of a finite result within
    [0.00356] of the integral. *)
Definition accurate_behavior (beh : program_behavior) : Prop :=
  exists result : float,
    beh = Terminates
      [Event_annot "quadrature-result" [EVfloat result]] Int.zero /\
    Binary.is_finite 53 1024 result = true /\
    Rabs (B2R 53 1024 result - RiemannInt integrand_integrable) <= 356 / 100000.

Lemma result_behavior_accurate :
  accurate_behavior (Terminates App.result_trace Int.zero).
Proof.
  exists cosine_value. split.
  - reflexivity.
  - split.
    + vm_compute. reflexivity.
    + rewrite integral_value. exact cosine_value_accuracy.
Qed.

Section ExternalCosine.
Hypothesis cosine_left : external_call cosine_external App.ge [Vfloat left_node]
  App.initial_memory E0 (Vfloat cosine_value) App.initial_memory.
Hypothesis cosine_right : external_call cosine_external App.ge [Vfloat right_node]
  App.initial_memory E0 (Vfloat cosine_value) App.initial_memory.

Theorem source_application_accuracy beh :
  program_behaves (Clight.semantics2 App.application) beh ->
  accurate_behavior beh.
Proof.
  intro H.
  rewrite (App.application_all_behaviors cosine_left cosine_right beh H).
  exact result_behavior_accurate.
Qed.

Theorem cminor_application_accuracy beh :
  program_behaves (Cminor.semantics CminorApplication.cminor_program) beh ->
  accurate_behavior beh.
Proof.
  intro H.
  rewrite (CminorApplication.application_all_behaviors
    cosine_left cosine_right beh H).
  exact result_behavior_accurate.
Qed.

Theorem assembly_application_accuracy (assembly_program : Asm.program)
    (compiled : Compiler.transf_cminor_program CminorApplication.cminor_program =
      OK assembly_program) beh :
  program_behaves (Asm.semantics assembly_program) beh ->
  accurate_behavior beh.
Proof.
  intro H.
  rewrite (AsmApplication.application_all_behaviors assembly_program compiled
    cosine_left cosine_right beh H).
  exact result_behavior_accurate.
Qed.

End ExternalCosine.
