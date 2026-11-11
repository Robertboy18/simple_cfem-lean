(* Copyright (c) 2026 simple_cfem-lean Team.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: simple_cfem-lean Team *)
(** * QuadratureC.accuracy.ValueAccuracy: the error of the two-point result *)

(** The two-point result [cosine_value] is within [0.00356] of [sin 1]. *)

From Coq Require Import Reals Lra.
From Flocq Require Import Core.Zaux Core.Raux IEEE754.Binary.
From compcert Require Import Floats.
From QuadratureC.clight Require Import ClightExample.

Local Open Scope R_scope.

Lemma cosine_value_real :
  B2R 53 1024 cosine_value = 7547238789953005 / 9007199254740992.
Proof.
  change (IZR 7547238789953005 * bpow radix2 (-53) =
    7547238789953005 / 9007199254740992).
  change (7547238789953005 * / 9007199254740992 =
    7547238789953005 / 9007199254740992).
  reflexivity.
Qed.

Lemma factorial_real_step n :
  INR (fact (S n)) = INR (S n) * INR (fact n).
Proof.
  change (INR (S n * fact n) = INR (S n) * INR (fact n)).
  apply mult_INR.
Qed.

(** Sixteen digits of [sin 1], from the alternating Taylor series. *)
Lemma sin_one_enclosure :
  8414709848078965 / 10000000000000000 <= sin 1 <=
  8414709848078966 / 10000000000000000.
Proof.
  assert (H0 : 0 <= 1) by lra.
  assert (H4 : 1 <= 4) by lra.
  pose proof (pre_sin_bound 1 4 H0 H4) as H.
  change (sin_approx 1 9 <= sin 1 <= sin_approx 1 10) in H.
  replace (sin_approx 1 9) with (102360822438075317 / 121645100408832000) in H.
  2: {
    unfold sin_approx, sin_term.
    cbn [sum_f_R0 Nat.mul Nat.add].
    rewrite !factorial_real_step.
    cbn [fact pow INR]. field.
  }
  replace (sin_approx 1 10) with (42991545423991633141 / 51090942171709440000) in H.
  2: {
    unfold sin_approx, sin_term.
    cbn [sum_f_R0 Nat.mul Nat.add].
    rewrite !factorial_real_step.
    cbn [fact pow INR]. field.
  }
  lra.
Qed.

Theorem cosine_value_accuracy :
  Rabs (B2R 53 1024 cosine_value - sin 1) <= 356 / 100000.
Proof.
  rewrite cosine_value_real.
  pose proof sin_one_enclosure.
  apply Rabs_le. lra.
Qed.
