(* Copyright (c) 2026 simple_cfem-lean Team.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: simple_cfem-lean Team *)
(** * QuadratureC.accuracy.ClightAccuracy: accuracy of the calls of integrate *)

(** The bound of [CallbackAccuracy.v] for every return of a call of [integrate] with one to four
    nodes and a callback that satisfies [function_accuracy]. *)

From Coq Require Import Reals List ZArith.
From compcert Require Import Integers Floats Values AST Memory Events
  Globalenvs Ctypes Clight ClightBigstep Smallstep.
From QuadratureC.clight Require Import quadrules ClightExample StoredRules ClightRules
  ClightDeterminism ClightSafety.
From QuadratureC.arithmetic Require Import FiniteArithmetic.
From QuadratureC.accuracy Require Import TableAccuracy CallbackAccuracy.

Import ListNotations Binary64Roundoff Binary64TableAccuracy Binary64CallbackAccuracy.
Local Open Scope R_scope.

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

Theorem integrate_rule_total_accuracy g error bound constant radius :
  function_accuracy f g error -> 0 <= error -> 0 <= bound -> 0 <= constant ->
  (forall x, -1 <= x <= 1 -> Rabs (g x) <= bound) ->
  lipschitz_on_interval g constant ->
  radius <= max_value ->
  (2 + INR (rule_size r) * weight_tolerance) * (bound + error) +
    2 * INR (rule_size r) * epsilon radius <= radius ->
  total_call_correct prog
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    (Vfloat (integrate_model_f f (rule_size r))) initial_memory /\
  finite (integrate_model_f f (rule_size r)) /\
  Rabs (real (integrate_model_f f (rule_size r)) - ideal_value g r) <=
    2 * INR (rule_size r) * epsilon radius +
    (2 + INR (rule_size r) * weight_tolerance) * (error + constant * node_tolerance) +
      INR (rule_size r) * weight_tolerance * bound.
Proof.
  intros HC HE HB HL HG HGL HM HR. split.
  - exact (integrate_rule_total_correct r f b fd
      callback_found callback_type callback_contract).
  - exact (integrate_model_f_accuracy f g error bound constant radius r
      HC HE HB HL HG HGL HM HR).
Qed.

(** Every returning small-step execution has the certified value, error,
    empty trace, and unchanged memory. *)
Theorem integrate_rule_all_returns_accuracy g error bound constant radius t value m :
  function_accuracy f g error -> 0 <= error -> 0 <= bound -> 0 <= constant ->
  (forall x, -1 <= x <= 1 -> Rabs (g x) <= bound) ->
  lipschitz_on_interval g constant ->
  radius <= max_value ->
  (2 + INR (rule_size r) * weight_tolerance) * (bound + error) +
    2 * INR (rule_size r) * epsilon radius <= radius ->
  star Clight.step2 ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    t (Returnstate (Vfloat value) Kstop m) ->
  t = E0 /\ m = initial_memory /\ finite value /\
  Rabs (real value - ideal_value g r) <=
    2 * INR (rule_size r) * epsilon radius +
    (2 + INR (rule_size r) * weight_tolerance) * (error + constant * node_tolerance) +
      INR (rule_size r) * weight_tolerance * bound.
Proof.
  intros HC HE HB HL HG HGL HM HR RUN.
  destruct (integrate_rule_total_accuracy g error bound constant radius
    HC HE HB HL HG HGL HM HR) as [HTOTAL [HFIN HERR]].
  destruct (call_unique_return _ _ _ _ HTOTAL _ _ _ RUN) as [HT [HV HMEM]].
  inversion HV; subst. auto.
Qed.

End Callback.
