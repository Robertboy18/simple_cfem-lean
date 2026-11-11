(* Copyright (c) 2026 simple_cfem-lean Team.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: simple_cfem-lean Team *)
(** * QuadratureC.analysis.ClightIntegralAccuracy: integral accuracy of the calls of integrate *)

(** For [n] from one to four nodes, every return [a] of a call of [integrate] with a callback
    that satisfies [function_accuracy] with error [eta] is within

    [c_n M + 2 n epsilon(r) + (2 + n delta_w) (eta + L delta_x) + n delta_w B]

    of the integral of [g] over [[-1, 1]]. Here [B], [L] and [M] bound [g], its derivative and
    its derivative of order [2n], [c_n] is the constant of [SharpAccuracy.v], [delta_x] and
    [delta_w] are the table errors of [TableAccuracy.v], and the range budget of
    [FiniteArithmetic.v] holds at radius [r]. The derivatives through order [2n] must exist at
    every point of [[-1, 1]], the endpoints included; integrability and the Lipschitz bound
    follow from them. *)

From Coq Require Import Reals List ZArith Lia Psatz.
From Coquelicot Require Import Coquelicot.
From compcert Require Import Integers Floats Values AST Memory Events
  Globalenvs Ctypes Clight ClightBigstep Smallstep.
From QuadratureC.clight Require Import quadrules ClightExample StoredRules ClightRules
  ClightDeterminism ClightSafety.
From QuadratureC.arithmetic Require Import FiniteArithmetic.
From QuadratureC.accuracy Require Import TableAccuracy CallbackAccuracy ClightAccuracy.
From QuadratureC.analysis Require Import TaylorAccuracy SharpAccuracy.

Import ListNotations Binary64Roundoff Binary64TableAccuracy Binary64CallbackAccuracy
  GaussianTaylorAccuracy GaussianSharpAccuracy.
Local Open Scope R_scope.

Definition integral_error_budget r error bound constant radius derivative_bound :=
  sharp_constant r * derivative_bound +
  2 * INR (rule_size r) * epsilon radius +
  (2 + INR (rule_size r) * weight_tolerance) * (error + constant * node_tolerance) +
  INR (rule_size r) * weight_tolerance * bound.

(** The derivative hypotheses give integrability and the Lipschitz bound at the perturbed
    nodes. *)
Lemma integrate_model_f_integral_accuracy f g error bound constant radius derivative_bound r :
  function_accuracy f g error ->
  0 <= error -> 0 <= bound -> 0 <= constant -> 0 <= derivative_bound ->
  (forall x, -1 <= x <= 1 -> Rabs (g x) <= bound) ->
  (forall x, -1 <= x <= 1 -> forall k,
    (k <= 2 * rule_size r)%nat -> ex_derive_n g k x) ->
  (forall x, -1 <= x <= 1 -> Rabs (Derive g x) <= constant) ->
  (forall x, -1 <= x <= 1 -> Rabs (Derive_n g (2 * rule_size r) x) <= derivative_bound) ->
  radius <= max_value ->
  (2 + INR (rule_size r) * weight_tolerance) * (bound + error) +
    2 * INR (rule_size r) * epsilon radius <= radius ->
  ex_RInt g (-1) 1 /\ finite (integrate_model_f f (rule_size r)) /\
  Rabs (real (integrate_model_f f (rule_size r)) - RInt g (-1) 1) <=
    integral_error_budget r error bound constant radius derivative_bound.
Proof.
  intros HC HE HB HL HM HG HD HL' HM' HMAX HR.
  assert (HN : (S (2 * rule_size r - 1) = 2 * rule_size r)%nat)
    by (destruct r; reflexivity).
  assert (HGL : lipschitz_on_interval g constant).
  { apply (lipschitz_of_derivative_bound g (Derive g) constant); [|exact HL'].
    intros x HX. apply is_derive_Reals, Derive_correct.
    exact (HD x HX 1%nat (ltac:(lia))). }
  destruct (integrate_model_f_accuracy f g error bound constant radius r
    HC HE HB HL HG HGL HMAX HR) as [HFIN HERR].
  pose proof (ideal_rule_sharp_accuracy g r derivative_bound HM HD HM') as HINT.
  split.
  - apply (derivative_integrable g (2 * rule_size r - 1)). rewrite HN. exact HD.
  - split; [exact HFIN |].
    replace (real (integrate_model_f f (rule_size r)) - RInt g (-1) 1) with
      ((real (integrate_model_f f (rule_size r)) - ideal_value g r) +
        (ideal_value g r - RInt g (-1) 1)) by ring.
    eapply Rle_trans; [apply Rabs_triang |].
    rewrite (Rabs_minus_sym (ideal_value g r) (RInt g (-1) 1)).
    unfold integral_error_budget. lra.
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

Theorem integrate_rule_total_integral_accuracy g error bound constant radius derivative_bound :
  function_accuracy f g error ->
  0 <= error -> 0 <= bound -> 0 <= constant -> 0 <= derivative_bound ->
  (forall x, -1 <= x <= 1 -> Rabs (g x) <= bound) ->
  (forall x, -1 <= x <= 1 -> forall k,
    (k <= 2 * rule_size r)%nat -> ex_derive_n g k x) ->
  (forall x, -1 <= x <= 1 -> Rabs (Derive g x) <= constant) ->
  (forall x, -1 <= x <= 1 -> Rabs (Derive_n g (2 * rule_size r) x) <= derivative_bound) ->
  radius <= max_value ->
  (2 + INR (rule_size r) * weight_tolerance) * (bound + error) +
    2 * INR (rule_size r) * epsilon radius <= radius ->
  total_call_correct prog
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    (Vfloat (integrate_model_f f (rule_size r))) initial_memory /\
  ex_RInt g (-1) 1 /\ finite (integrate_model_f f (rule_size r)) /\
  Rabs (real (integrate_model_f f (rule_size r)) - RInt g (-1) 1) <=
    integral_error_budget r error bound constant radius derivative_bound.
Proof.
  intros HC HE HB HL HM HG HD HL' HM' HMAX HR. split.
  - exact (integrate_rule_total_correct r f b fd
      callback_found callback_type callback_contract).
  - exact (integrate_model_f_integral_accuracy f g error bound constant radius
      derivative_bound r HC HE HB HL HM HG HD HL' HM' HMAX HR).
Qed.

Theorem integrate_rule_all_returns_integral_accuracy
    g error bound constant radius derivative_bound t value m :
  function_accuracy f g error ->
  0 <= error -> 0 <= bound -> 0 <= constant -> 0 <= derivative_bound ->
  (forall x, -1 <= x <= 1 -> Rabs (g x) <= bound) ->
  (forall x, -1 <= x <= 1 -> forall k,
    (k <= 2 * rule_size r)%nat -> ex_derive_n g k x) ->
  (forall x, -1 <= x <= 1 -> Rabs (Derive g x) <= constant) ->
  (forall x, -1 <= x <= 1 -> Rabs (Derive_n g (2 * rule_size r) x) <= derivative_bound) ->
  radius <= max_value ->
  (2 + INR (rule_size r) * weight_tolerance) * (bound + error) +
    2 * INR (rule_size r) * epsilon radius <= radius ->
  star Clight.step2 ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      Kstop initial_memory)
    t (Returnstate (Vfloat value) Kstop m) ->
  t = E0 /\ m = initial_memory /\ ex_RInt g (-1) 1 /\ finite value /\
  Rabs (real value - RInt g (-1) 1) <=
    integral_error_budget r error bound constant radius derivative_bound.
Proof.
  intros HC HE HB HL HM HG HD HL' HM' HMAX HR RUN.
  destruct (integrate_rule_total_integral_accuracy g error bound constant radius derivative_bound
    HC HE HB HL HM HG HD HL' HM' HMAX HR) as [HTOTAL [HINT [HFIN HERR]]].
  destruct (call_unique_return _ _ _ _ HTOTAL _ _ _ RUN) as [HT [HV HMEM]].
  inversion HV; subst. auto.
Qed.
End Callback.
