(* Copyright (c) 2026 simple_cfem-lean Team.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: simple_cfem-lean Team *)
(** * QuadratureC.compilation.CminorSafety: total correctness of the library calls in Cminor *)

(** The calls of [integrate] with one to four nodes are totally correct in Cminor, from
    CompCert's determinacy of Cminor and [SilentTermination.v]. *)

From Coq Require Import List ZArith.
From compcert Require Import Integers Floats Values AST Memory Events
  Globalenvs Ctypes Clight ClightBigstep Smallstep Cminor.
From QuadratureC.clight Require Import quadrules ClightExample StoredRules ClightRules.
From QuadratureC.clight Require Import SilentTermination.
From QuadratureC.compilation Require Import CsharpminorExample CminorExample.

Import ListNotations.

(** The compiled call may allocate and free stack blocks, so its final memory is related to the
    initial one by a memory injection. *)
Module CminorTotalCorrectness.
Module ST := SilentTermination.SilentTermination.
Module CM := CminorExample.
Module CS := CsharpminorExample.

Lemma return_Kstop_nostep p value m :
  nostep Cminor.step (Genv.globalenv p)
    (Cminor.Returnstate value Cminor.Kstop m).
Proof. intros t next H. inversion H. Qed.

Record total_call_correct p s value m : Prop := {
  call_execution : star Cminor.step (Genv.globalenv p) s E0
    (Cminor.Returnstate value Cminor.Kstop m);
  call_accessible : Acc (ST.successor (Cminor.semantics p)) s;
  call_reachable_safe : forall t next,
    star Cminor.step (Genv.globalenv p) s t next ->
    t = E0 /\ (next = Cminor.Returnstate value Cminor.Kstop m \/
      exists next', Cminor.step (Genv.globalenv p) next E0 next');
  call_unique_return : forall t value' m',
    star Cminor.step (Genv.globalenv p) s t
      (Cminor.Returnstate value' Cminor.Kstop m') ->
    t = E0 /\ value' = value /\ m' = m
}.

Theorem silent_total_call_correct p s value m :
  star Cminor.step (Genv.globalenv p) s E0
    (Cminor.Returnstate value Cminor.Kstop m) ->
  total_call_correct p s value m.
Proof.
  intros RUN.
  pose proof (Cminor.semantics_determinate p) as DET.
  pose proof (return_Kstop_nostep p value m) as LAST.
  constructor.
  - exact RUN.
  - exact (@ST.termination_accessible (Cminor.semantics p) DET _ _ RUN LAST).
  - exact (@ST.termination_safe (Cminor.semantics p) DET _ _ RUN LAST).
  - intros t value' m' PREFIX.
    destruct (@ST.terminal_unique (Cminor.semantics p) DET _ _ RUN LAST
      _ _ PREFIX (return_Kstop_nostep p value' m')) as [HT HE].
    inversion HE; subst. auto.
Qed.

Theorem integrate_rule_total_correct r f b fd
  (HF : Genv.find_funct ge (Vptr b Ptrofs.zero) = Some fd)
  (HT : type_of_fundef fd =
    Tfunction [Tfloat F64 noattr] (Tfloat F64 noattr) cc_default)
  (HC : forall i, (i < rule_size r)%nat ->
    ClightBigstep.Clight2.eval_funcall ge initial_memory fd
      [Vfloat (rule_node r i)] E0 initial_memory (Vfloat (f (rule_node r i)))) :
  exists tfd tm inj,
    Genv.find_symbol (Genv.globalenv CM.tprog) _integrate = Some CS.integrate_block /\
    Genv.find_funct_ptr (Genv.globalenv CM.tprog) CS.integrate_block = Some tfd /\
    total_call_correct CM.tprog
      (Cminor.Callstate tfd
        [Vptr b Ptrofs.zero; Vint (Int.repr (Z.of_nat (rule_size r)))]
        Cminor.Kstop initial_memory)
      (Vfloat (integrate_model_f f (rule_size r))) tm /\
    Mem.inject inj initial_memory tm.
Proof.
  destruct (CM.body_integrate_compiled r f b fd HF HT HC)
    as [tfd [tm [inj [HS [HF' [RUN HI]]]]]].
  exists tfd, tm, inj. split; [exact HS |]. split; [exact HF' |].
  split; [apply silent_total_call_correct; exact RUN | exact HI].
Qed.
End CminorTotalCorrectness.
