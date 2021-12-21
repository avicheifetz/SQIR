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
  Definition LCU {n} (k : R) (Ua Ub: base_ucom (n)) : base_ucom ( n) :=
    Ry (acos(√ (k /(k + 1)))) 0; UnitaryOps.control 0 Ua; X 0; UnitaryOps.control 0 Ub; Ry (acos(√ (k /(k + 1)))) 0.
  
(** Proof **)
Local Open Scope C_scope.
Local Open Scope R_scope.

Lemma LCU_success_probability (k : R) :
   forall {n : nat} (Ua Ub : base_ucom (n)),
  (n > 0)%nat -> (k >= 0) -> 
   @prob_partial_meas 1 n (1 ⨂ ∣1⟩) (uc_eval (LCU k Ua Ub)) <=
    (4 * k) / (k + 1)^2.
Proof.
  intros n Ua Ub Hn Hk.
  unfold LCU.
  simpl uc_eval.
  autorewrite with eval_db.
  bdestruct_all.
  replace (n - (0 + 1))%nat with (n - 1)%nat by lia.
  Msimpl_light.
  simpl.
  repeat (rewrite Mmult_assoc; restore_dims).
  Qsimpl. 
  2: {apply y_rotation_unitary.}
  rewrite control_correct.
  rewrite control_correct.
  simpl.
  rewrite prob_partial_meas_alt. 

  (*specialize (@partial_meas_tensor 1 n) as H1.
  repeat rewrite Nat.pow_1_r in H1.
 rewrite H1; clear H1.
*)
  simpl.
  (*induction Hk.
  Search R. 
  2: { rewrite H0. auto. replace (0 + 1)%R with 1. simpl.  replace (√(0 / 1))%R with 0. Search acos. rewrite acos_0. simpl. replace (4 * 0 / (1 * (1 * 1))) with 0. . 
} *)
Qed.
  

End LCU.

