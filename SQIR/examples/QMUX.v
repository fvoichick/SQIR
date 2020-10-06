Require Import UnitaryOps.

Local Open Scope nat_scope.
Local Open Scope ucom_scope.

Definition control0 {dim} (q : nat) (p : base_ucom dim) : base_ucom dim :=
  X q ; control q p ; X q.

Lemma typed_control0 :
  forall (dim q : nat) (p : base_ucom dim),
  q < dim -> is_fresh q p -> uc_well_typed p ->
  uc_well_typed (control0 q p).
Proof.
  intros. apply WT_seq.
  - apply WT_seq.
    + apply uc_well_typed_X. assumption.
    + apply uc_well_typed_control; assumption.
  - apply uc_well_typed_X. assumption.
Qed.

Lemma control0_correct :
  forall (dim q : nat) (p : base_ucom dim),
  q < dim -> is_fresh q p -> uc_well_typed p ->
  uc_eval (control0 q p) =
  Mmult (proj q dim false) (uc_eval p) .+ proj q dim true.
Proof.
  intros. unfold control0. simpl.
  rewrite control_correct; try assumption.
  rewrite denote_X.
  rewrite Mmult_plus_distr_r. rewrite Mmult_plus_distr_l.
  unfold proj. simpl.
  rewrite Mmult_assoc.
  rewrite <- pad_fresh_commutes; try auto with wf_db.
  repeat rewrite <- Mmult_assoc.
  repeat rewrite pad_mult.
  unfold ket. simpl.
  replace (Mmult _ _) with (Mmult qubit1 (adjoint qubit1)).
  - replace (Mmult _ σx) with (Mmult qubit0 (adjoint qubit0)).
    + apply Mplus_comm.
    + lma.
  - lma.
Qed.

Definition QMUX {dim} (q : nat) (p0 p1 : base_ucom dim) : base_ucom dim :=
  control0 q p0 ; control q p1.

Lemma typed_QMUX :
  forall (dim q : nat) (p0 p1: base_ucom dim),
  q < dim ->
  is_fresh q p0 -> is_fresh q p1 ->
  uc_well_typed p0 -> uc_well_typed p1 ->
  uc_well_typed (QMUX q p0 p1).
Proof.
  intros. apply WT_seq.
  - apply WT_seq.
    + apply WT_seq.
      * apply uc_well_typed_X. apply H.
      * apply (uc_well_typed_control _ _ _ H H0 H2).
    + apply uc_well_typed_X. apply H.
  - apply (uc_well_typed_control _ _ _ H H1 H3).
Qed.

Definition qmux {dim} (c : nat) (u0 u1 : Square (2 ^ dim)) : Square (2 ^ dim)
  := Mmult (proj c dim false) u0 .+ Mmult (proj c dim true) u1.

Lemma WF_qmux :
  forall (dim c : nat) (u0 u1 : Square (2 ^ dim)),
  WF_Matrix u0 -> WF_Matrix u1 ->
  WF_Matrix (qmux c u0 u1).
Proof.
  intros. unfold qmux. auto with wf_db.
Qed.
Hint Resolve WF_qmux : wf_db.

Lemma QMUX_correct :
  forall (dim q : nat) (p0 p1 : base_ucom dim),
  q < dim ->
  is_fresh q p0 -> is_fresh q p1 ->
  uc_well_typed p0 -> uc_well_typed p1 ->
  uc_eval (QMUX q p0 p1) = qmux q (uc_eval p0) (uc_eval p1).
Proof.
  intros. unfold QMUX.
  assert (uc_eval (control0 q p0; control q p1) =
      Mmult (uc_eval (control q p1)) (uc_eval (control0 q p0))).
      { reflexivity. }
  rewrite H4. clear H4.
  rewrite control0_correct; try assumption.
  rewrite control_correct; try assumption.
  unfold qmux.
  rewrite Mmult_plus_distr_r. repeat rewrite Mmult_plus_distr_l.
  rewrite proj_twice_neq by discriminate. rewrite Mplus_0_r.
  repeat rewrite <- Mmult_assoc. rewrite proj_twice_eq.
  assert (Mmult (Mmult (proj q dim true) (uc_eval p1)) (proj q dim true) =
      Mmult (proj q dim true) (uc_eval p1)).
      { rewrite Mmult_assoc. rewrite <- proj_fresh_commutes; try assumption.
        rewrite <- Mmult_assoc. rewrite proj_twice_eq. reflexivity. }
  rewrite H4. clear H4.
  replace (Mmult _ (proj _ _ false)) with (Zero : Square (2 ^ dim)).
  - rewrite Mmult_0_l. lma.
  - rewrite Mmult_assoc. rewrite <- proj_fresh_commutes; try assumption.
    rewrite <- Mmult_assoc. rewrite proj_twice_neq; try discriminate.
    symmetry. apply Mmult_0_l.
Qed.

