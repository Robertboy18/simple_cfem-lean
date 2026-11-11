(* Copyright (c) 2026 simple_cfem-lean Team.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: simple_cfem-lean Team *)
(** * QuadratureC.clight.StoredRules: the stored tables and integrate_model_f *)

(** The tables [gauss_pts] and [gauss_wts] of [quadrules.c], read from the initializers of
    [prog], and the functional model [integrate_model_f] of simple_cfem's [proof/quadmodel.v] in
    CompCert's arithmetic. *)

From Coq Require Import List Arith.
From compcert Require Import AST Floats.
From QuadratureC.clight Require Import quadrules.

Import ListNotations.

(** Read the tables from the initializers [v_gauss_pts] and [v_gauss_wts] of the generated
    [quadrules.v]. *)
Definition initializer_float (d : init_data) : float :=
  match d with Init_float64 f => f | _ => Float.zero end.
Definition nodes := map initializer_float (gvar_init v_gauss_pts).
Definition weights := map initializer_float (gvar_init v_gauss_wts).

Lemma nodes_initializer : map Init_float64 nodes = gvar_init v_gauss_pts.
Proof. reflexivity. Qed.

Lemma weights_initializer : map Init_float64 weights = gvar_init v_gauss_wts.
Proof. reflexivity. Qed.

(** All stored slices of the original tables. The execution theorems separately
    require at most ten nodes; these functional definitions also describe zero. *)
Definition stored_table_index (n i : nat) : nat := n * (n - 1) / 2 + i.
Definition stored_node n i := nth (stored_table_index n i) nodes Float.zero.
Definition stored_weight n i := nth (stored_table_index n i) weights Float.zero.
Definition stored_terms n : list (float * float) :=
  map (fun i => (stored_weight n i, stored_node n i)) (seq 0 n).

(** The functional model [integrate_model_f] of simple_cfem's [proof/quadmodel.v], in CompCert's
    own floating-point operations. *)
Definition integrate_model_f (f : float -> float) n :=
  fold_left (fun acc term => Float.add acc (Float.mul (fst term) (f (snd term))))
    (stored_terms n) Float.zero.
