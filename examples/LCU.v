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
    Ry (acos(√ (k /(k + 1)))) 0; 
    cast (UnitaryOps.control 0 (map_qubits S Ua)) n; 
    X 0; 
    cast (UnitaryOps.control 0 (map_qubits S Ub)) n; 
    Ry (acos(√ (k /(k + 1)))) 0.
  
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

(* uc_eval LCU simplifies to this expression (which can be further simplified...
   but it'll take a little work). -KH *)
Lemma LCU_simplify (k : R) : forall {n : nat} (Ua Ub : base_ucom (n - 1)),
  (n > 0)%nat -> (k >= 0) -> 
  uc_well_typed Ua ->
  uc_well_typed Ub ->
  uc_eval (LCU k Ua Ub) =
    y_rotation (acos (√ (k / (k + 1)))) × ∣0⟩⟨1∣
      × y_rotation (acos (√ (k / (k + 1)))) ⊗ uc_eval Ua
    .+ y_rotation (acos (√ (k / (k + 1)))) × ∣1⟩⟨0∣
      × y_rotation (acos (√ (k / (k + 1)))) ⊗ uc_eval Ub.
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
  rewrite prob_partial_meas_alt. 
 
  (* now it's a matter of simplifying the expression... *)

Admitted.
  

End LCU.

