(* Copyright (c) 2026 simple_cfem-lean Team.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: simple_cfem-lean Team *)
(** * QuadratureC.clight.ClightRules: the rules with one to four nodes in the original program *)

(** The accuracy proofs of [accuracy/] and [analysis/] treat the rules with one to four nodes,
    for which [analysis/SharpAccuracy.v] computes the Gaussian remainder constants. This file
    names those four rules and specializes the loop of [RuleLibrary.v] to the original program
    [prog] and its initial memory. *)

From Coq Require Import List ZArith Lia.
From compcert Require Import Coqlib Integers Floats Values AST Memory Events
  Globalenvs Ctypes Clight ClightBigstep Smallstep.
From QuadratureC.clight Require Import quadrules ClightExample StoredRules RuleLibrary.

Import ListNotations.

Inductive rule_order := One | Two | Three | Four.
Definition rule_size (r : rule_order) : nat :=
  match r with One => 1 | Two => 2 | Three => 3 | Four => 4 end.
Definition rule_node r i := stored_node (rule_size r) i.
Definition rule_weight r i := stored_weight (rule_size r) i.
Definition rule_terms r : list (float * float) :=
  map (fun i => (rule_weight r i, rule_node r i)) (seq 0 (rule_size r)).

(** Split a goal about an index [i] below a small bound into one goal per value. *)
Ltac enumerate_index i :=
  first [lia | destruct i as [| i]; [idtac | enumerate_index i]].

(** The original program, with its tables and accessors, is a context of [RuleLibrary.v]. *)
Definition original_context : RuleLibrary.context := {|
  RuleLibrary.context_program := prog;
  RuleLibrary.context_memory := initial_memory;
  RuleLibrary.context_initializes := initial_memory_exists;
  RuleLibrary.context_symbols := fun _ _ => eq_refl;
  RuleLibrary.context_points := points_block_info;
  RuleLibrary.context_weights := weights_block_info;
  RuleLibrary.context_point_function := ltac:(vm_compute; reflexivity);
  RuleLibrary.context_weight_function := ltac:(vm_compute; reflexivity)
|}.

Section Callback.

Variable r : rule_order.
Variable f : float -> float.
Variable b : block.
Variable fd : Clight.fundef.

Hypothesis callback_found : Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd.
Hypothesis callback_type :
  type_of_fundef fd = Tfunction [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default.
Hypothesis callback_contract :
  forall i, (i < rule_size r)%nat ->
    ClightBigstep.Clight2.eval_funcall ge initial_memory fd
      [Vfloat (rule_node r i)] E0 initial_memory (Vfloat (f (rule_node r i))).

(** A call of [integrate] with a callback that returns [f] at the stored nodes runs, in the
    small-step semantics, silently to [integrate_model_f f (rule_size r)]. *)
Theorem integrate_rule_steps (k : cont) (hk : is_call_cont k) :
  star Clight.step2 ge
    (Callstate (Internal f_integrate)
      [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
      k initial_memory)
    E0 (Returnstate (Vfloat (integrate_model_f f (rule_size r))) k initial_memory).
Proof.
  eapply (RuleLibrary.stored_integrate_steps original_context (rule_size r)).
  all: try eassumption.
  destruct r; cbn; lia.
Qed.

End Callback.
