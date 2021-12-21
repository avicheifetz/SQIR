Require Import UnitaryOps.
Require Import Utilities.
Require Import QWIRE.Dirac.
Require Import QWIRE.Quantum.
Require Import QWIRE.Proportional.
Require DensitySem.
Require NDSem.
Require UnitarySem.
Import NDSem.
(* mechanizing LCU from this paper https://arxiv.org/pdf/1202.5822.pdf *)

(* Note: this file requires the version of Ratan in Coq >= 8.12.0 *)
Require Import Coq.Reals.Ratan. 

Local Open Scope ucom_scope.

Local Coercion Nat.b2n : bool >-> nat.

Module LCU.

(* Definition *)
  Definition LCU {n} (k : R) (Ua Ub: base_ucom (n - 1)) : base_ucom n :=
    Ry (2 * acos(√ (k /(k + 1)))) 0; 
    cast (UnitaryOps.control 0 (map_qubits S Ua)) n; 
    X 0; 
    cast (UnitaryOps.control 0 (map_qubits S Ub)) n; 
    Ry (2 * acos( √ (k /(k + 1)))) 0.
  
(** Proof **)
Local Open Scope C_scope.
Local Open Scope R_scope.

Lemma uc_well_typed_cast_change_dim : forall m n o (u : base_ucom m),
  (n <= o)%nat ->
  uc_well_typed (cast u n) ->
  uc_well_typed (cast u o).
Proof.
  intros.
  induction u.
  simpl. 
  inversion H0; subst.
  constructor; auto.
  inversion H0; subst.
  constructor; lia.
  inversion H0; subst.
  constructor; lia.
  inversion H0; subst.
  constructor; lia.
Qed.

Lemma sqrt_helper:
  forall {k:R},
     (k >= 0) ->
    -1 <= √ (k / (k + 1)) <= 1.
Proof.
  intros k H. split.
  -apply Rle_trans with 0.  apply Ropp_le_cancel. rewrite Ropp_0.    replace (- (-1)) with (1). apply Rle_0_1. rewrite <- Ropp_involutive with 1. reflexivity.
   apply sqrt_pos. 
  -rewrite <- sqrt_1. apply sqrt_le_1_alt.
  induction H.
   +rewrite sqrt_1. apply Rle_trans with ((k +  1) / (k + 1)). auto. rewrite Rdiv_plus_distr. rewrite Rplus_comm with (k / (k + 1))  (1 / (k + 1)).  apply Rle_minus_l. rewrite Rminus_eq_0.  apply Rlt_le.  apply Rdiv_lt_0_compat. apply Rlt_0_1. apply Rlt_trans with k. apply H. apply Rlt_n_Sn. auto. autorewrite with R_db. apply Rle_refl.
   +rewrite H. rewrite sqrt_1.  rewrite Rplus_0_l.  autorewrite with R_db. apply Rle_0_1.
Qed.

Lemma LCU_helper00:
  forall {n : nat} (k : R) (Ua Ub : base_ucom (n - 1)),
    (n > 0)%nat ->
    uc_well_typed Ua ->
    (k >= 0) -> 
  uc_well_typed Ub ->
    y_rotation (2 * acos ( √ (k / (k + 1)))) × ∣0⟩⟨0∣ = √(k / (k + 1)) .* ∣0⟩⟨0∣ .+ ( √(1 /(k + 1)) .* ∣1⟩⟨0∣).
Proof. 
  intros. unfold y_rotation. solve_matrix.
  -simpl.  replace (2 * acos (√ (k / (k + 1))) / 2) with (acos (√ (k / (k + 1)))). 
   +rewrite cos_acos. auto. apply sqrt_helper. apply H1.
   +  rewrite Rmult_comm with  (2) ( acos (√ (k / (k + 1)))). simpl. auto. 
      rewrite <- Rmult_div_assoc. replace (2 / 2) with 1. rewrite Rmult_1_r. auto.
      autorewrite with R_db. auto.
  -simpl. replace (2 * acos (√ (k / (k + 1))) / 2) with (acos (√ (k / (k + 1)))).
   + rewrite sin_acos.  rewrite Rsqr_sqrt.  replace (1 - k / (k + 1)) with (1 / (k + 1)).
     autorewrite with R_db. auto.  replace (1 - k / (k + 1)) with ((k + 1) / (k + 1) - k / (k + 1) ).
     rewrite <- Rdiv_minus_distr. rewrite Rplus_comm. replace ( 1 + k - k) with 1.
     reflexivity. autorewrite with R_db. rewrite Rplus_assoc.  rewrite <- Rminus_unfold.
     rewrite Rminus_eq_0. autorewrite with R_db.
     reflexivity.  autorewrite with R_db. reflexivity.
     destruct H1.
     * apply Rlt_le.  apply Rdiv_lt_0_compat. apply H1. apply Rlt_trans with k. apply H1.
       apply Rlt_n_Sn.
     * rewrite H1. autorewrite with R_db. apply Rle_refl.
     * apply sqrt_helper. apply H1.
   + rewrite Rmult_comm with  (2) ( acos (√ (k / (k + 1)))). simpl. auto. rewrite <- Rmult_div_assoc. replace (2 / 2) with 1. rewrite Rmult_1_r. auto. autorewrite with R_db. auto.
Qed.
Lemma LCU_helperRotate:
  forall {n : nat} (k : R) (Ua Ub : base_ucom (n - 1)),
    (n > 0)%nat ->
    uc_well_typed Ua ->
    (k >= 0) -> 
  uc_well_typed Ub ->
    y_rotation (2 * acos ( √ (k / (k + 1)))) = √(k / (k + 1)) .* ∣0⟩⟨0∣ .+ (- √/( (k + 1))) .* ∣0⟩⟨1∣ .+ ( √(1 /(k + 1)) .* ∣1⟩⟨0∣)  .+ ( √(k /(k + 1)) .* ∣1⟩⟨1∣).
Proof. 
  intros. unfold y_rotation. solve_matrix.
  -simpl.  replace (2 * acos (√ (k / (k + 1))) / 2) with (acos (√ (k / (k + 1)))). 
   +rewrite cos_acos. auto. apply sqrt_helper. apply H1.
   +  rewrite Rmult_comm with  (2) ( acos (√ (k / (k + 1)))). simpl. auto. 
      rewrite <- Rmult_div_assoc. replace (2 / 2) with 1. rewrite Rmult_1_r. auto.
      autorewrite with R_db. auto.
   -simpl. replace (2 * acos (√ (k / (k + 1))) / 2) with (acos (√ (k / (k + 1)))).
   + rewrite sin_acos.  rewrite Rsqr_sqrt.  replace (1 - k / (k + 1)) with (1 / (k + 1)).
     autorewrite with R_db. auto.  replace (1 - k / (k + 1)) with ((k + 1) / (k + 1) - k / (k + 1) ).
     rewrite <- Rdiv_minus_distr. rewrite Rplus_comm. replace ( 1 + k - k) with 1.
     reflexivity. autorewrite with R_db. rewrite Rplus_assoc.  rewrite <- Rminus_unfold.
     rewrite Rminus_eq_0. autorewrite with R_db.
     reflexivity.  autorewrite with R_db. reflexivity.
     destruct H1.
     * apply Rlt_le.  apply Rdiv_lt_0_compat. apply H1. apply Rlt_trans with k. apply H1.
       apply Rlt_n_Sn.
     * rewrite H1. autorewrite with R_db. apply Rle_refl.
     * apply sqrt_helper. apply H1.
   + rewrite Rmult_comm with  (2) ( acos (√ (k / (k + 1)))). simpl. auto. rewrite <- Rmult_div_assoc. replace (2 / 2) with 1. rewrite Rmult_1_r. auto. autorewrite with R_db. auto.
  -simpl. replace (2 * acos (√ (k / (k + 1))) / 2) with (acos (√ (k / (k + 1)))).
   + rewrite sin_acos.  rewrite Rsqr_sqrt.  replace (1 - k / (k + 1)) with (1 / (k + 1)).
     autorewrite with R_db. auto.  replace (1 - k / (k + 1)) with ((k + 1) / (k + 1) - k / (k + 1) ).
     rewrite <- Rdiv_minus_distr. rewrite Rplus_comm. replace ( 1 + k - k) with 1.
     reflexivity. autorewrite with R_db. rewrite Rplus_assoc.  rewrite <- Rminus_unfold.
     rewrite Rminus_eq_0. autorewrite with R_db.
     reflexivity.  autorewrite with R_db. reflexivity.
     destruct H1.
     * apply Rlt_le.  apply Rdiv_lt_0_compat. apply H1. apply Rlt_trans with k. apply H1.
       apply Rlt_n_Sn.
     * rewrite H1. autorewrite with R_db. apply Rle_refl.
     * apply sqrt_helper. apply H1.
   + rewrite Rmult_comm with  (2) ( acos (√ (k / (k + 1)))). simpl. auto. rewrite <- Rmult_div_assoc. replace (2 / 2) with 1. rewrite Rmult_1_r. auto. autorewrite with R_db. auto.
     - simpl.  replace (2 * acos (√ (k / (k + 1))) / 2) with (acos (√ (k / (k + 1)))). 
   +rewrite cos_acos. auto. apply sqrt_helper. apply H1.
   +  rewrite Rmult_comm with  (2) ( acos (√ (k / (k + 1)))). simpl. auto. 
      rewrite <- Rmult_div_assoc. replace (2 / 2) with 1. rewrite Rmult_1_r. auto.
      autorewrite with R_db. auto.
Qed.

Lemma LCU_helper01:
  forall {n : nat} (k : R) (Ua Ub : base_ucom (n - 1)),
    (n > 0)%nat ->
    uc_well_typed Ua ->
    (k >= 0) -> 
  uc_well_typed Ub ->
    y_rotation (2 * acos ( √ (k / (k + 1)))) × ∣0⟩⟨1∣ = √(k / (k + 1)) .* ∣0⟩⟨1∣ .+ √(1 /(k + 1)) .* ∣1⟩⟨1∣.
Proof. 
  intros. unfold y_rotation. solve_matrix.
  -simpl.  replace (2 * acos (√ (k / (k + 1))) / 2) with (acos (√ (k / (k + 1)))).
   +rewrite cos_acos. auto. apply sqrt_helper. apply H1.
   +  rewrite Rmult_comm with  (2) ( acos (√ (k / (k + 1)))). simpl. auto. 
      rewrite <- Rmult_div_assoc. replace (2 / 2) with 1. rewrite Rmult_1_r. auto.
      autorewrite with R_db. auto.
  -simpl. replace (2 * acos (√ (k / (k + 1))) / 2) with (acos (√ (k / (k + 1)))).
   + rewrite sin_acos.  rewrite Rsqr_sqrt.  replace (1 - k / (k + 1)) with (1 / (k + 1)).
     autorewrite with R_db. auto.  replace (1 - k / (k + 1)) with ((k + 1) / (k + 1) - k / (k + 1) ).
     rewrite <- Rdiv_minus_distr. rewrite Rplus_comm. replace ( 1 + k - k) with 1.
     reflexivity. autorewrite with R_db. rewrite Rplus_assoc.  rewrite <- Rminus_unfold.
     rewrite Rminus_eq_0. autorewrite with R_db.
     reflexivity.  autorewrite with R_db. reflexivity.
     destruct H1.
     * apply Rlt_le.  apply Rdiv_lt_0_compat. apply H1. apply Rlt_trans with k. apply H1.
       apply Rlt_n_Sn.
     * rewrite H1. autorewrite with R_db. apply Rle_refl.
     * apply sqrt_helper. apply H1.
   + rewrite Rmult_comm with  (2) ( acos (√ (k / (k + 1)))). simpl. auto. rewrite <- Rmult_div_assoc. replace (2 / 2) with 1. rewrite Rmult_1_r. auto. autorewrite with R_db. auto.
Qed.

Lemma LCU_helper10:
  forall {n : nat} (k : R) (Ua Ub : base_ucom (n - 1)),
    (n > 0)%nat ->
    uc_well_typed Ua ->
    (k >= 0) -> 
  uc_well_typed Ub ->
    y_rotation (2 * acos ( √ (k / (k + 1)))) × ∣1⟩⟨0∣ = (- √/( (k + 1))) .* ∣0⟩⟨0∣ .+ ( √(k /(k + 1)) .* ∣1⟩⟨0∣).
Proof. 
  intros. unfold y_rotation. solve_matrix.
  2:{simpl.  replace (2 * acos (√ (k / (k + 1))) / 2) with (acos (√ (k / (k + 1)))). 
   +rewrite cos_acos. auto. apply sqrt_helper. apply H1.
   +  rewrite Rmult_comm with  (2) ( acos (√ (k / (k + 1)))). simpl. auto. 
      rewrite <- Rmult_div_assoc. replace (2 / 2) with 1. rewrite Rmult_1_r. auto.
      autorewrite with R_db. auto. }
  -simpl. replace (2 * acos (√ (k / (k + 1))) / 2) with (acos (√ (k / (k + 1)))).
   + rewrite sin_acos.  rewrite Rsqr_sqrt.  replace (1 - k / (k + 1)) with (1 / (k + 1)).
     autorewrite with R_db. auto.  replace (1 - k / (k + 1)) with ((k + 1) / (k + 1) - k / (k + 1) ).
     rewrite <- Rdiv_minus_distr. rewrite Rplus_comm. replace ( 1 + k - k) with 1.
     reflexivity. autorewrite with R_db. rewrite Rplus_assoc.  rewrite <- Rminus_unfold.
     rewrite Rminus_eq_0. autorewrite with R_db.
     reflexivity.  autorewrite with R_db. reflexivity.
     destruct H1.
     * apply Rlt_le.  apply Rdiv_lt_0_compat. apply H1. apply Rlt_trans with k. apply H1.
       apply Rlt_n_Sn.
     * rewrite H1. autorewrite with R_db. apply Rle_refl.
     * apply sqrt_helper. apply H1.
   + rewrite Rmult_comm with  (2) ( acos (√ (k / (k + 1)))). simpl. auto. rewrite <- Rmult_div_assoc. replace (2 / 2) with 1. rewrite Rmult_1_r. auto. autorewrite with R_db. auto.
Qed.
Lemma LCU_helper11:
  forall {n : nat} (k : R) (Ua Ub : base_ucom (n - 1)),
    (n > 0)%nat ->
    uc_well_typed Ua ->
    (k >= 0) -> 
  uc_well_typed Ub ->
    y_rotation (2 * acos ( √ (k / (k + 1)))) × ∣1⟩⟨1∣ =  (- √/( (k + 1))) .* ∣0⟩⟨1∣ .+ ( √(k /(k + 1)) .* ∣1⟩⟨1∣).
Proof. 
  intros. unfold y_rotation. solve_matrix.
  2 :{simpl.  replace (2 * acos (√ (k / (k + 1))) / 2) with (acos (√ (k / (k + 1)))). 
   +rewrite cos_acos. auto. apply sqrt_helper. apply H1.
   +  rewrite Rmult_comm with  (2) ( acos (√ (k / (k + 1)))). simpl. auto. 
      rewrite <- Rmult_div_assoc. replace (2 / 2) with 1. rewrite Rmult_1_r. auto.
      autorewrite with R_db. auto. }
  -simpl. replace (2 * acos (√ (k / (k + 1))) / 2) with (acos (√ (k / (k + 1)))).
   + rewrite sin_acos.  rewrite Rsqr_sqrt.  replace (1 - k / (k + 1)) with (1 / (k + 1)).
     autorewrite with R_db. auto.  replace (1 - k / (k + 1)) with ((k + 1) / (k + 1) - k / (k + 1) ).
     rewrite <- Rdiv_minus_distr. rewrite Rplus_comm. replace ( 1 + k - k) with 1.
     reflexivity. autorewrite with R_db. rewrite Rplus_assoc.  rewrite <- Rminus_unfold.
     rewrite Rminus_eq_0. autorewrite with R_db.
     reflexivity.  autorewrite with R_db. reflexivity.
     destruct H1.
     * apply Rlt_le.  apply Rdiv_lt_0_compat. apply H1. apply Rlt_trans with k. apply H1.
       apply Rlt_n_Sn.
     * rewrite H1. autorewrite with R_db. apply Rle_refl.
     * apply sqrt_helper. apply H1.
   + rewrite Rmult_comm with  (2) ( acos (√ (k / (k + 1)))). simpl. auto. rewrite <- Rmult_div_assoc. replace (2 / 2) with 1. rewrite Rmult_1_r. auto. autorewrite with R_db. auto.
Qed.
(* uc_eval LCU simplifies to this expression (which can be further simplified...
   but it'll take a little work). -KH *)
Lemma LCU_simplify (k : R) : forall {n : nat} (Ua Ub : base_ucom (n - 1)),
  (n > 0)%nat -> (k >= 0) -> 
  uc_well_typed Ua ->
  uc_well_typed Ub ->
  uc_eval (LCU k Ua Ub) =
    y_rotation (2 * acos (√ (k / (k + 1)))) × ∣0⟩⟨1∣
      × y_rotation (2 * acos (√ (k / (k + 1)))) ⊗ uc_eval Ua
    .+ y_rotation (2 * acos ( √ (k / (k + 1)))) × ∣1⟩⟨0∣
      × y_rotation (2 * acos (√ (k / (k + 1)))) ⊗ uc_eval Ub.
Proof.
  intros n Ua Ub Hn Hk HUa HUb.
  unfold LCU.
  simpl uc_eval.
  autorewrite with eval_db.
  rewrite 2 cast_control_commute.
  rewrite 2 control_correct.

  specialize (pad_dims_l Ub (S O)) as Htmp.
  simpl in Htmp. 
  replace (fun q : nat => S q) with S in Htmp by reflexivity.
  replace (S (n - 1))%nat with n in Htmp by lia.
  rewrite <- Htmp.
  clear Htmp.

  specialize (pad_dims_l Ua (S O)) as Htmp.
  simpl in Htmp. 
  replace (fun q : nat => S q) with S in Htmp by reflexivity.
  replace (S (n - 1))%nat with n in Htmp by lia.
  rewrite <- Htmp.
  clear Htmp.

  unfold proj, pad.
  bdestruct_all. 
  replace (n - (0 + 1))%nat with (n - 1)%nat by lia.
  simpl.
  Msimpl.
  distribute_plus.
  Msimpl.
  distribute_plus.
  Msimpl.

  remember (∣ 0 ⟩ × (∣ 0 ⟩) †) as ψ00.
  remember (∣ 1 ⟩ × (∣ 1 ⟩) †)as ψ11.
  repeat rewrite <- Mmult_assoc.
  rewrite (Mmult_assoc (y_rotation _) ψ00).
  rewrite 2 (Mmult_assoc (y_rotation _) (ψ00 × _)).
  rewrite (Mmult_assoc (y_rotation _) ψ11).
  rewrite 2 (Mmult_assoc (y_rotation _) (ψ11 × _)).
  replace (ψ00 × σx × ψ00) with (@Zero 2 2).
  replace (ψ00 × σx × ψ11) with (∣0⟩⟨1∣).
  replace (ψ11 × σx × ψ00) with (∣1⟩⟨0∣).
  replace (ψ11 × σx × ψ11) with (@Zero 2 2).
  2-5: subst; solve_matrix.
  Msimpl.
  repeat rewrite Mmult_assoc.
  reflexivity.

  apply y_rotation_unitary.
  replace (map_qubits S Ua) with (map_qubits (fun q => 1 + q)%nat Ua) by reflexivity.
  apply map_qubits_fresh. lia.
  replace (map_qubits S Ua) with (map_qubits (fun q => 1 + q)%nat Ua) by reflexivity.
  apply uc_well_typed_cast_change_dim with (n:=(1 + (n - 1))%nat).
  lia.
  apply uc_well_typed_map_qubits.
  assumption.
  replace (map_qubits S Ub) with (map_qubits (fun q => 1 + q)%nat Ub) by reflexivity.
  apply map_qubits_fresh. lia.
  replace (map_qubits S Ub) with (map_qubits (fun q => 1 + q)%nat Ub) by reflexivity.
  apply uc_well_typed_cast_change_dim with (n:=(1 + (n - 1))%nat).
  lia.
  apply uc_well_typed_map_qubits.
  assumption.
   Qed.



Lemma LCU_simplify_rotation (k : R) : forall {n : nat} (Ua Ub : base_ucom (n - 1)),
  (n > 0)%nat -> (k >= 0) -> 
  uc_well_typed Ua ->
  uc_well_typed Ub ->
    y_rotation (2 * acos (√ (k / (k + 1)))) × ∣0⟩⟨1∣
      × y_rotation (2 * acos (√ (k / (k + 1)))) ⊗ uc_eval Ua
    .+ y_rotation (2 * acos ( √ (k / (k + 1)))) × ∣1⟩⟨0∣
    × y_rotation (2 * acos (√ (k / (k + 1)))) ⊗ uc_eval Ub =
     (√( k/ (k + 1)) .* ∣0⟩⟨1∣ .+ √(1 /(k + 1)) .* ∣1⟩⟨1∣)
     ×  y_rotation (2 * acos (√ (k / (k + 1)))) ⊗ uc_eval Ua
    .+  (- √( / (k + 1)) .* ∣0⟩⟨0∣ .+ √(k /(k + 1)) .* ∣1⟩⟨0∣)
   ×  y_rotation (2 * acos (√ (k / (k + 1)))) ⊗ uc_eval Ub.
   Proof.
     intros.
     rewrite LCU_helperRotate with k Ua Ub; try reflexivity; try  assumption. solve_matrix.
   Qed.


Lemma LCU_success_probability (k : R) :
   forall {n : nat} (Ua Ub : base_ucom (n - 1)),
  (n > 0)%nat -> (k >= 0) -> 
  uc_well_typed Ua ->
  uc_well_typed Ub ->
   @prob_partial_meas 1 n ∣1⟩ (uc_eval (LCU k Ua Ub)) <=
    (4 * k) / (k + 1)^2.
Proof.

  intros n Ua Ub Hn Hk HUa HUb.
  rewrite LCU_simplify by assumption.
  rewrite LCU_helperRotate with k Ua Ub; try reflexivity; try  assumption. solve_matrix.
    autorewrite with R_db C_db ket_db eval_db.
     specialize (@partial_meas_tensor 1 n) as H1.
  repeat rewrite Nat.pow_1_r in H1.
  rewrite H1; clear H1.
Admitted.
  

End LCU.

