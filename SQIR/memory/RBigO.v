Require Import Reals.
Require Import Psatz.
Require Import Program.
Require Import BigO.

Local Open Scope R_scope.

Notation "w <= x <= y <= z" := (w <= x <= y /\ y <= z)
  (at level 70, x at next level, y at next level, no associativity) : R_scope.

Local Open Scope nat_scope.

Definition nat_R_Big_Theta g :=
  fun f => exists (c1 c2 : posreal) n0, forall n, n >= n0 ->
  0 <= c1 * g n <= f n <= c2 * g n.

Definition nat_R_Big_O (g : nat -> R) :=
  fun f : nat -> R => exists (c : posreal) n0, forall n, n >= n0 ->
  (0 <= f n <= c * g n)%R.

Lemma successor_posreal :
  forall n, (INR n + 1 > 0)%R.
Proof. intros. rewrite <- S_INR. apply lt_0_INR. lia. Qed.

Lemma archimed_nat : forall x : R, exists n, (x < INR n)%R.
Proof.
  intros x. exists (Z.to_nat (up x)).
  rewrite INR_IZR_INZ. rewrite ZifyInst.of_nat_to_nat_eq.
  apply Rlt_le_trans with (IZR (up x)).
  - apply archimed.
  - apply IZR_le. apply Z.le_max_r.
Qed.

Lemma nat_R_Big_O_iff :
  forall f g,
  f is Big_O g <-> nat_R_Big_O (compose INR g) (compose INR f).
Proof.
  intros f g. split.
  - intros [c [n0 H]].
    exists (mkposreal (INR c + 1)%R (successor_posreal c)), n0. simpl.
    intros n Hn. unfold compose. specialize (H n Hn). split.
    + apply pos_INR.
    + rewrite <- S_INR. rewrite <- mult_INR. apply le_INR. lia.
  - intros [[c] [n0 H]]. unfold compose in H. simpl in *.
    destruct (archimed_nat c) as [c' Hc]. exists c', n0.
    intros n Hn. specialize (H n Hn) as [Hp H].
    apply Rle_trans with (r3 := (INR c' * INR (g n))%R) in H.
    + rewrite <- mult_INR in H. apply INR_le. assumption.
    + nra.
Qed.

Definition nat_R_Big_Omega (g : nat -> R) :=
  fun f => exists (c : posreal) n0, forall n, n >= n0 ->
  (0 <= c * g n <= f n)%R.

Lemma nat_R_Big_Omega_iff :
  forall f g,
  f is Big_Omega g <-> nat_R_Big_Omega (compose INR g) (compose INR f).
Proof.
  intros f g. split.
  - intros [c [n0 H]].
    remember (RinvN c) as pos_c' eqn:E.
    exists pos_c', n0. intros n Hn.
    destruct pos_c' as [c' Hc]. simpl. injection E as E.
    assert (0 <= INR c)%R. { apply pos_INR. }
    unfold compose. specialize (H n Hn). split.
    + apply Rmult_le_pos.
      * lra.
      * apply pos_INR.
    + apply Rmult_le_reg_l with (INR c + 1)%R.
      * lra.
      * rewrite <- Rmult_assoc. subst. rewrite Rinv_r.
        -- apply Rle_trans with (INR c * INR (f n))%R.
           ++ rewrite <- mult_INR. rewrite Rmult_1_l.
              apply le_INR. assumption.
           ++ apply Rmult_le_compat_r; try lra. apply pos_INR.
        -- lra.
  - intros [[c H0] [n0 H]]. unfold compose in H. simpl in H. unfold Big_Omega.
    destruct (archimed_nat (/ c)) as [c' Hc]. exists c', n0.
    intros n Hn. specialize (H n Hn) as [Hp H].
    apply Rmult_le_compat_l with (r := / c) in H.
    + rewrite <- Rmult_assoc in H. rewrite Rinv_l in H. rewrite Rmult_1_l in H.
      apply Rle_trans with (r3 := INR (c' * f n)) in H.
      * apply INR_le. lra.
      * rewrite mult_INR. apply Rmult_le_compat_r; try lra. apply pos_INR.
      * lra.
    + left. apply Rinv_0_lt_compat. assumption.
Qed.

Lemma nat_R_Big_Theta_equiv :
  forall f g,
  nat_R_Big_Theta g f <-> nat_R_Big_O g f /\ nat_R_Big_Omega g f.
Proof.
  split.
  - intros [c1 [c2 [n0 H]]]. split.
    + exists c2, n0. intros n Hn. specialize (H n Hn). lra.
    + exists c1, n0. intros. apply H. assumption.
  - intros [[c2 [n2 H2]] [c1 [n1 H1]]].
    exists c1, c2, (n1 + n2). split.
    + apply H1. lia.
    + apply H2. lia.
Qed.

Lemma nat_R_Big_Theta_iff :
  forall f g,
  f is Big_Theta g <-> nat_R_Big_Theta (compose INR g) (compose INR f).
Proof.
  intros f g. split.
  - intros. apply nat_R_Big_Theta_equiv.
    rewrite <- nat_R_Big_O_iff, <- nat_R_Big_Omega_iff.
    apply Big_Theta_iff. assumption.
  - intros. apply Big_Theta_iff.
    rewrite nat_R_Big_O_iff, nat_R_Big_Omega_iff.
    apply nat_R_Big_Theta_equiv. assumption.
Qed.

Definition R_Big_O g :=
  fun f => exists (c n0 : posreal), forall n, (n >= n0)%R ->
  (0 <= f n <= c * g n)%R.

Definition step (f : nat -> nat) : R -> R :=
  fun x => INR (f (Z.to_nat (Int_part x))).

Lemma R_Big_O_iff :
  forall f g,
  f is Big_O g <-> R_Big_O (step g) (step f).
Proof.
  intros f g. split.
  - intros H. apply nat_R_Big_O_iff in H. destruct H as [c [n0 H]].
    remember (INR n0 + 1)%R as n0'.
    assert (n0' > 0)%R as H0. { subst. rewrite <- S_INR. apply lt_0_INR. lia. }
    exists c, (mkposreal n0' H0). simpl.
    intros n Hn. remember (Z.to_nat(Int_part n)) as n'.
    assert (0 <= INR n0)%R. { apply pos_INR. }
    assert (n >= 1)%R. { lra. }
    assert (n' >= n0) as Hn'.
    { subst. apply INR_le. rewrite (INR_IZR_INZ (Z.to_nat _)).
      rewrite Z2Nat.id.
      - apply Rplus_le_reg_r with (-n). apply Rle_trans with (-1)%R; try lra.
        left. apply base_Int_part.
      - apply le_IZR. apply Rle_trans with (n - 1)%R.
        + lra.
        + apply Rplus_le_reg_r with (-n)%R. left.
          replace (n - 1 + - n)%R  with (- 1)%R by lra.
          apply base_Int_part. }
    specialize (H n' Hn') as H. subst. unfold compose in H.
    unfold step. split; apply H.
  - intros [c [n0 H]]. apply nat_R_Big_O_iff.
    destruct (archimed_nat n0) as [n0' H0].
    exists c, n0'.
    intros n Hn. unfold compose.
    assert (INR n >= n0)%R as Hi.
    { apply Rge_trans with (INR n0').
      - apply Rle_ge. apply le_INR. assumption.
      - left. assumption. }
    assert (n = Z.to_nat (Int_part (INR n))) as Hz.
    { rewrite Int_part_INR. rewrite Nat2Z.id. reflexivity. }
    specialize (H (INR n) Hi) as H. unfold step in H. rewrite Hz. assumption.
Qed.

