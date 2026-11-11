(* Copyright (c) 2026 simple_cfem-lean Team.
   Released under Apache 2.0 license as described in the file LICENSE.
   Authors: simple_cfem-lean Team *)
(** * QuadratureC.clight.ClightExample: the program of quadrules.c and its initial memory *)

(** The program [prog] is clightgen's output for [quadrules.c] in simple_cfem's
    [proof/C/quadrules.v]. This file computes the two-point values of the cosine example in
    CompCert's binary64 arithmetic, builds the initial memory of [prog] and reads the first
    stored entries, and provides the tactics that evaluate closed Clight expressions. *)

From Coq Require Import List ZArith.
From compcert Require Import Coqlib Maps Integers Floats Values AST Memory Events
  Globalenvs Ctypes Cop Clight ClightBigstep.
From QuadratureC.clight Require Import quadrules.

Import ListNotations.
Local Open Scope Z_scope.

(** ** The two-point values *)

(** Concrete arithmetic in CompCert's floating-point semantics. *)
Definition left_node := Float.of_bits (Int64.repr 13826747565314421532).
Definition right_node := Float.of_bits (Int64.repr 4603375528459645724).
Definition cosine_value := Float.of_bits (Int64.repr 4605722458335229421).
Definition one := Float.of_bits (Int64.repr 4607182418800017408).
Definition half := Float.of_bits (Int64.repr 4602678819172646912).

Lemma int_one_float : Float.of_int (Int.repr 1) = one.
Proof.
  rewrite Float.of_int_from_words.
  match goal with |- ?x = _ => rewrite <- (Float.of_to_bits x) end.
  vm_compute. reflexivity.
Qed.

Definition callback (x : float) :=
  Float.mul (Float.mul half (Float.sub one x)) cosine_value.

Definition quadrature_value :=
  Float.add (Float.add Float.zero (Float.mul one (callback left_node)))
    (Float.mul one (callback right_node)).

Theorem quadrature_value_bits :
  Float.to_bits quadrature_value = Int64.repr 4605722458335229421.
Proof. vm_compute. reflexivity. Qed.

Theorem quadrature_value_exact : quadrature_value = cosine_value.
Proof.
  rewrite <- (Float.of_to_bits quadrature_value), quadrature_value_bits.
  reflexivity.
Qed.

(** ** The initial memory *)

(** The memory used below is the actual initialized memory of the pinned AST. *)
Definition ge := globalenv prog.

Lemma program_initializes : exists m, Genv.init_mem prog = Some m.
Proof.
  apply Genv.init_mem_exists.
  intros id v H.
  change (In (id, Gvar v) global_definitions) in H.
  cbn [global_definitions In] in H.
  repeat match type of H with
  | _ \/ _ => destruct H as [H | H]; [inversion H; subst; clear H |]
  end; try contradiction;
  split.
  all: try (intros i o H; simpl in H; intuition discriminate).
  all: cbn [v___stringlit_1 v___stringlit_2 v___stderrp v_gauss_pts v_gauss_wts
    gvar_init Genv.init_data_list_aligned Genv.init_data_alignment init_data_size].
  all: repeat match goal with |- _ /\ _ => split end.
  all: try exact I.
  all: apply Z.mod_divide; [discriminate | reflexivity].
Qed.

Definition initialized_memory : { m : mem | Genv.init_mem prog = Some m }.
Proof.
  destruct (Genv.init_mem prog) as [m |] eqn:H.
  - exists m. reflexivity.
  - exfalso. destruct program_initializes as [m Hm]. congruence.
Qed.

Definition initial_memory := proj1_sig initialized_memory.

Theorem initial_memory_exists : Genv.init_mem prog = Some initial_memory.
Proof. exact (proj2_sig initialized_memory). Qed.

Definition points_block :=
  match Genv.find_symbol ge _gauss_pts with Some b => b | None => 1%positive end.

Lemma points_block_info :
  Genv.find_var_info (Genv.globalenv prog) points_block = Some v_gauss_pts.
Proof. reflexivity. Qed.

Lemma point_loads :
  Mem.load Mfloat64 initial_memory points_block 8 = Some (Vfloat left_node) /\
  Mem.load Mfloat64 initial_memory points_block 16 = Some (Vfloat right_node).
Proof.
  pose proof (Genv.init_mem_characterization prog points_block
    points_block_info initial_memory_exists) as [_ [_ [H _]]].
  specialize (H eq_refl).
  cbn [Genv.load_store_init_data gvar_init] in H.
  exact (conj (proj1 (proj2 H)) (proj1 (proj2 (proj2 H)))).
Qed.

Definition weights_block :=
  match Genv.find_symbol ge _gauss_wts with Some b => b | None => 1%positive end.

Lemma weights_block_info :
  Genv.find_var_info (Genv.globalenv prog) weights_block = Some v_gauss_wts.
Proof. reflexivity. Qed.

Lemma weight_loads :
  Mem.load Mfloat64 initial_memory weights_block 8 = Some (Vfloat one) /\
  Mem.load Mfloat64 initial_memory weights_block 16 = Some (Vfloat one).
Proof.
  pose proof (Genv.init_mem_characterization prog weights_block
    weights_block_info initial_memory_exists) as [_ [_ [H _]]].
  specialize (H eq_refl).
  cbn [Genv.load_store_init_data gvar_init] in H.
  exact (conj (proj1 (proj2 H)) (proj1 (proj2 (proj2 H)))).
Qed.

(** ** Closed expressions *)

(** Subsequent proofs use the initialization lemmas instead of reducing memory. *)
Local Opaque initial_memory.

Ltac solve_closed_operation :=
  lazymatch goal with
  | |- sem_binary_operation _ Osub (Vint ?i) _ (Vfloat ?x) _ _ = Some ?v =>
      change (Some (Vfloat (Float.sub (Float.of_int i) x)) = Some v);
      rewrite int_one_float; reflexivity
  | |- sem_binary_operation _ Omul (Vfloat ?x) _ (Vfloat ?y) _ _ = Some ?v =>
      change (Some (Vfloat (Float.mul x y)) = Some v); reflexivity
  | |- sem_binary_operation _ Oadd (Vfloat ?x) _ (Vfloat ?y) _ _ = Some ?v =>
      change (Some (Vfloat (Float.add x y)) = Some v); reflexivity
  | |- sem_cast (Vfloat ?x) _ _ _ = Some ?v =>
      change (Some (Vfloat x) = Some v); reflexivity
  | _ => vm_compute; reflexivity
  end.

Ltac eval_closed_expr :=
  lazymatch goal with
  | |- eval_expr _ _ _ _ (Econst_int _ _) _ => constructor
  | |- eval_expr _ _ _ _ (Econst_float _ _) _ => constructor
  | |- eval_expr _ _ _ _ (Etempvar _ _) _ =>
      apply eval_Etempvar; reflexivity
  | |- eval_expr _ _ _ _ (Ebinop _ _ _ _) _ =>
      eapply eval_Ebinop;
        [eval_closed_expr | eval_closed_expr | solve_closed_operation]
  | |- eval_expr _ _ _ _ (Eaddrof _ _) _ =>
      eapply eval_Eaddrof; eapply eval_Evar_global; vm_compute; reflexivity
  | |- eval_expr _ _ _ _ (Evar _ _) _ =>
      eapply eval_Elvalue;
        [eapply eval_Evar_global; vm_compute; reflexivity |
         apply deref_loc_reference; reflexivity]
  | |- eval_expr _ _ _ _ (Ederef _ _) _ =>
      eapply eval_Elvalue;
        [eapply eval_Ederef; eval_closed_expr |
         eapply deref_loc_value;
           [reflexivity |
            first [exact (proj1 point_loads) | exact (proj2 point_loads) |
              exact (proj1 weight_loads) | exact (proj2 weight_loads)]]]
  end.

Definition cosine_external :=
  EF_external "cos"
    (mksignature [AST.Xfloat] AST.Xfloat cc_default).

Definition testfun_block :=
  match Genv.find_symbol ge _testfun with Some b => b | None => 1%positive end.
