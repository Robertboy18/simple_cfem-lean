(* Copyright (c) 2026 simple_cfem-lean Team.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: simple_cfem-lean Team *)
(** * QuadratureC.accuracy.ClightInteger: integer specifications of the results of integrate *)

(** Every return of a call of [integrate] with one to four nodes is computed by the integer
    recurrence of [FiniteInteger.v]. *)

From Coq Require Import Reals List ZArith.
From compcert Require Import Integers Floats Values AST Memory Events
  Globalenvs Ctypes Clight ClightBigstep Smallstep.
From QuadratureC.clight Require Import quadrules ClightExample StoredRules ClightRules
  ClightDeterminism ClightSafety.
From QuadratureC.arithmetic Require Import FiniteArithmetic.
From QuadratureC.accuracy Require Import ClightRoundoff.
From QuadratureC.arithmetic Require Import FiniteRepresentation.
From QuadratureC.accuracy Require Import ClightRepresentation.
From QuadratureC.arithmetic Require Import FiniteInteger.

Import ListNotations Binary64Roundoff.
Local Open Scope R_scope.

Theorem integrate_model_f_integer radius f r :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  Binary64Integer.represents (integrate_model_f f (rule_size r))
    (Binary64Integer.sum f (rule_terms r) ((0%Z, 0%Z), false)).
Proof.
  intros HM HF HB.
  rewrite Binary64Integer.represents_iff_observe, Binary64Integer.sum_real.
  assert (HI : Binary64Integer.state_real ((0%Z, 0%Z), false) = (0, false)).
  { unfold Binary64Integer.state_real, D.dyadic_real. cbn. f_equal. ring. }
  rewrite HI. exact (integrate_model_f_observe radius f r HM HF HB).
Qed.

Theorem integrate_model_f_integer_eq_iff radius f r z :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  (integrate_model_f f (rule_size r) = z <->
    Binary64Integer.represents z
      (Binary64Integer.sum f (rule_terms r) ((0%Z, 0%Z), false))).
Proof.
  intros HM HF HB.
  pose proof (integrate_model_f_integer radius f r HM HF HB) as HR.
  split; [intros <-; exact HR |].
  intros HZ. eapply Binary64Integer.represents_unique; eauto.
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

Theorem integrate_rule_all_returns_integer radius t value m :
  radius <= max_value ->
  (forall i, (i < rule_size r)%nat -> finite (f (rule_node r i))) ->
  product_mass f (rule_terms r) + 2 * INR (rule_size r) * epsilon radius <= radius ->
  star Clight.step2 ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    t (Returnstate (Vfloat value) Kstop m) ->
  t = E0 /\ m = initial_memory /\
  Binary64Integer.represents value
    (Binary64Integer.sum f (rule_terms r) ((0%Z, 0%Z), false)).
Proof.
  intros HM HF HB RUN.
  pose proof (integrate_rule_total_correct r f b fd
    callback_found callback_type callback_contract) as HTOTAL.
  pose proof (integrate_model_f_integer radius f r HM HF HB) as HINTEGER.
  destruct (call_unique_return _ _ _ _ HTOTAL _ _ _ RUN) as [HT [HV HMEM]].
  inversion HV; subst. auto.
Qed.

End Callback.
