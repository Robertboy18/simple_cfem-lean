(* Copyright (c) 2026 simple_cfem-lean Team.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: simple_cfem-lean Team *)
(** * QuadratureC.accuracy.ClightRepresentation: signs and values of the results of integrate *)

(** Every return of a call of [integrate] with one to four nodes is determined by the signed
    recurrence of [FiniteRepresentation.v]. *)

From Coq Require Import Reals List ZArith.
From compcert Require Import Integers Floats Values AST Memory Events
  Globalenvs Ctypes Clight ClightBigstep Smallstep.
From QuadratureC.clight Require Import quadrules ClightExample StoredRules ClightRules
  ClightDeterminism ClightSafety.
From QuadratureC.arithmetic Require Import FiniteArithmetic.
From QuadratureC.accuracy Require Import ClightRoundoff.
From QuadratureC.arithmetic Require Import FiniteRepresentation.

Import ListNotations Binary64Roundoff Binary64Representation.
Local Open Scope R_scope.
Local Transparent Float.zero.

(** The actual initialized weights and callback outputs determine both the
    real value and the sign of the result, including either zero encoding. *)
Theorem integrate_model_f_observe radius f r :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  finite (integrate_model_f f (rule_size r)) /\
  observe (integrate_model_f f (rule_size r)) = signed_sum f (rule_terms r) (0, false).
Proof.
  intros HM HF HB.
  destruct (integrate_model_f_bounded radius f r HM HF HB) as [HS [HFIN _]].
  split; [exact HFIN |].
  exact (observe_integrate_finite f (rule_terms r) Float.zero HS
    (rule_terms_finite f r HF)).
Qed.

Theorem integrate_model_f_eq_iff radius f r z :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  (integrate_model_f f (rule_size r) = z <->
    finite z /\ observe z = signed_sum f (rule_terms r) (0, false)).
Proof.
  intros HM HF HB.
  destruct (integrate_model_f_observe radius f r HM HF HB) as [HN HO].
  split.
  - intros <-. auto.
  - intros [HZ HE]. apply (observe_injective _ _ HN HZ).
    rewrite HO. symmetry. exact HE.
Qed.

Section Callback.

Variable r : rule_order.
Variable f : Floats.float -> Floats.float.
Variable b : block.
Variable fd : Clight.fundef.

Hypothesis callback_found : Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd.
Hypothesis callback_type :
  type_of_fundef fd = Tfunction [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default.
Hypothesis callback_contract :
  forall i, (i < rule_size r)%nat ->
    ClightBigstep.Clight2.eval_funcall ge initial_memory fd
      [Vfloat (rule_node r i)] E0 initial_memory (Vfloat (f (rule_node r i))).

Theorem integrate_rule_all_returns_observation radius t value m :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  star Clight.step2 ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    t (Returnstate (Vfloat value) Kstop m) ->
  t = E0 /\ m = initial_memory /\ finite value /\
  observe value = signed_sum f (rule_terms r) (0, false).
Proof.
  intros HM HF HB RUN.
  pose proof (integrate_rule_total_correct r f b fd
    callback_found callback_type callback_contract) as HTOTAL.
  destruct (integrate_model_f_observe radius f r HM HF HB) as [HFIN HOBS].
  destruct (call_unique_return _ _ _ _ HTOTAL _ _ _ RUN) as [HT [HV HMEM]].
  inversion HV; subst. auto.
Qed.

End Callback.
