Require Import Nat Bool Arith List Basics Psatz.
Require Import MSetList MSetProperties OrdersEx.
Require Import FunctionalExtensionality.
Import ListNotations.
Require Import SQIR.

Module Import S := MSetList.Make Nat_as_OT.
Module Import SProperties := Properties(S).

Open Scope bool_scope.
Open Scope nat_scope.
Open Scope ucom_scope.

Fixpoint gates { U dim } (p : ucom U dim) : nat :=
  match p with
  | p1 ; p2 => gates p1 + gates p2
  | uapp1 _ _ => 1
  | uapp2 _ _ _ => 1
  | uapp3 _ _ _ _ => 1
  end.

Fixpoint gates1 { U dim } (p : ucom U dim) : nat :=
  match p with
  | p1 ; p2 => gates1 p1 + gates1 p2
  | uapp1 _ _ => 1
  | uapp2 _ _ _ => 0
  | uapp3 _ _ _ _ => 0
  end.

Fixpoint gates2 { U dim } (p : ucom U dim) : nat :=
  match p with
  | p1 ; p2 => gates2 p1 + gates2 p2
  | uapp1 _ _ => 0
  | uapp2 _ _ _ => 1
  | uapp3 _ _ _ _ => 0
  end.

Fixpoint gates3 { U dim } (p : ucom U dim) : nat :=
  match p with
  | p1 ; p2 => gates3 p1 + gates3 p2
  | uapp1 _ _ => 0
  | uapp2 _ _ _ => 0
  | uapp3 _ _ _ _ => 1
  end.

Fact gates_sum :
  forall U dim (p : ucom U dim), gates p = gates1 p + gates2 p + gates3 p.
Proof.
  intros U dim p. induction p; simpl; lia.
Qed.

Fact base_gates_sum :
  forall dim (p : base_ucom dim), gates p = gates1 p + gates2 p.
Proof.
  intros dim p. induction p as [| | | u]; simpl; try lia. inversion u.
Qed.

Fixpoint usedb { U dim } (p : ucom U dim) w :=
  match p with
  | p1 ; p2 => usedb p1 w || usedb p2 w
  | uapp1 _ i => i =? w
  | uapp2 _ i1 i2 => (i1 =? w) || (i2 =? w)
  | uapp3 _ i1 i2 i3 => (i1 =? w) || (i2 =? w) || (i3 =? w)
  end.

Inductive used { U dim } : ucom U dim -> nat -> Prop :=
  | used_useq_1 (p1 p2 : ucom U dim) (w : nat) : used p1 w -> used (p1 ; p2) w
  | used_useq_2 (p1 p2 : ucom U dim) (w : nat) : used p2 w -> used (p1 ; p2) w
  | used_uapp1 (u : U 1) (i : nat) : used (uapp1 u i) i
  | used_uapp2_1 (u : U 2) (i1 i2 : nat) : used (uapp2 u i1 i2) i1
  | used_uapp2_2 (u : U 2) (i1 i2 : nat) : used (uapp2 u i1 i2) i2
  | used_uapp3_1 (u : U 3) (i1 i2 i3 : nat) : used (uapp3 u i1 i2 i3) i1
  | used_uapp3_2 (u : U 3) (i1 i2 i3 : nat) : used (uapp3 u i1 i2 i3) i2
  | used_uapp3_3 (u : U 3) (i1 i2 i3 : nat) : used (uapp3 u i1 i2 i3) i3.

Fact usedb_iff_used :
  forall U dim (p : ucom U dim) w, usedb p w = true <-> used p w.
Proof.
  intros U dim p w. split; intros H.
  - induction p; simpl in *;
        repeat try (rewrite orb_true_iff in H; destruct H);
        try (rewrite Nat.eqb_eq in H; subst);
        auto using @used.
  - induction H; simpl;
        repeat try rewrite orb_true_iff; auto using Nat.eqb_refl.
Qed.

Fixpoint useds { U dim } (p : ucom U dim) : t :=
  match p with
  | p1 ; p2 => union (useds p1) (useds p2)
  | uapp1 _ i => singleton i
  | uapp2 _ i1 i2 => add i1 (singleton i2)
  | uapp3 _ i1 i2 i3 => add i1 (add i2 (singleton i3))
  end.

Fact in_useds_iff_used :
  forall U dim (p : ucom U dim) w, In w (useds p) <-> used p w.
Proof.
  intros U dim p w. split; intros H.
  - induction p; simpl in H;
        try (apply union_spec in H; destruct H);
        repeat (apply add_spec in H; destruct H; subst);
        try (apply singleton_spec in H; subst);
        auto using @used.
  - induction H; simpl;
        try (apply union_spec);
        repeat (rewrite add_spec);
        try (rewrite singleton_spec);
        auto.
Qed.

Definition qubits { U dim } (p : ucom U dim) :=
  cardinal (useds p).

Lemma add_cardinal_le :
  forall x s, cardinal (add x s) <= S (cardinal s).
Proof.
  intros x s. destruct (mem x s) eqn:E.
  - apply mem_spec in E. rewrite add_cardinal_1; auto.
  - apply FM.not_mem_iff in E. rewrite add_cardinal_2; auto.
Qed.

Fact qubits_le_3gates :
  forall U dim (p : ucom U dim), qubits p <= 3 * gates p.
Proof.
  intros U dim p. unfold qubits.
  induction p; eauto using le_trans, add_cardinal_le, le_n_S.
  simpl. eapply le_trans.
  - apply union_cardinal_le.
  - lia.
Qed.

Fact qubits_le_2gates :
  forall dim (p : base_ucom dim), qubits p <= 2 * gates p.
Proof.
  intros dim p. unfold qubits.
  induction p as [| | | u]; simpl.
  - simpl. eapply le_trans.
    + apply union_cardinal_le.
    + lia.
  - auto.
  - eauto using le_trans, add_cardinal_le.
  - inversion u.
Qed.

Lemma well_typed_used :
  forall U dim (p : ucom U dim), uc_well_typed p ->
  For_all (fun w => w < dim) (useds p).
Proof.
  intros U dim p H i Hi.
  induction H; simpl in *;
      try (apply union_spec in Hi; destruct Hi);
      repeat (apply add_spec in Hi; destruct Hi as [| Hi]; subst);
      try (apply singleton_spec in Hi; subst);
      auto.
Qed.

Lemma pigeonhole :
  forall (s : t) m, For_all (fun x => x < m) s -> cardinal s <= m.
Proof.
  intros s m. generalize dependent s. induction m as [| m IH].
  - intros s H.
    assert (Empty s). { intros x Hx. specialize (H x Hx). simpl in H. lia. }
    assert (cardinal s = 0). { auto with set. }
    lia.
  - intros s H.
    assert (For_all (fun x => x < m) (remove m s)).
    { intros x Hx. apply Nat.le_neq. split.
      - apply FM.remove_3 in Hx. apply H in Hx. lia.
      - apply remove_spec in Hx. apply Hx. }
    specialize (IH (remove m s) H0).
    destruct (mem m s) eqn:E.
    + apply mem_spec in E.
      rewrite <- remove_cardinal_1 with (x := m); auto using le_n_S.
    + apply FM.not_mem_iff in E.
      rewrite <- remove_cardinal_2 with (x := m); auto.
Qed.

Fact qubits_le_dim :
  forall U dim (p : ucom U dim), uc_well_typed p -> qubits p <= dim.
Proof.
  intros U dim p H. unfold qubits.
  apply well_typed_used in H. apply pigeonhole. assumption.
Qed.

Inductive uapp (U : nat -> Set) (dim : nat) : Set :=
  | uapp_1 (u : U 1) (i : nat) : uapp U dim
  | uapp_2 (u : U 2) (i1 i2 : nat) : uapp U dim
  | uapp_3 (u : U 3) (i1 i2 i3 : nat) : uapp U dim.

Arguments uapp_1 { U dim }.
Arguments uapp_2 { U dim }.
Arguments uapp_3 { U dim }.

Definition uapp_to_ucom { U dim } (p : uapp U dim) : ucom U dim :=
  match p with
  | uapp_1 u i => uapp1 u i
  | uapp_2 u i1 i2 => uapp2 u i1 i2
  | uapp_3 u i1 i2 i3 => uapp3 u i1 i2 i3
  end.

(* reverse order *)
Fixpoint sequence { U dim } (p : ucom U dim) : list (uapp U dim) :=
  match p with
  | p1 ; p2 => sequence p2 ++ sequence p1
  | uapp1 u i => [ uapp_1 u i ]
  | uapp2 u i1 i2 => [ uapp_2 u i1 i2 ]
  | uapp3 u i1 i2 i3 => [ uapp_3 u i1 i2 i3 ]
  end.

Lemma sequence_gates :
  forall U dim (p : ucom U dim), gates p = length (sequence p).
Proof.
  intros U dim p. induction p; simpl; try reflexivity. rewrite app_length. lia.
Qed.

Fixpoint suseds { U dim } (ps : list (uapp U dim)) :=
  match ps with
  | [ ] => empty
  | p :: ps' => union (useds (uapp_to_ucom p)) (suseds ps')
  end.

Lemma suseds_concat :
  forall U dim (ps1 ps2 : list (uapp U dim)), 
  Equal (suseds (ps1 ++ ps2)) (union (suseds ps1) (suseds ps2)).
Proof.
  intros U dim ps1 ps2. induction ps1; simpl; auto with set.
  rewrite union_assoc. apply union_equal_2. assumption.
Qed.

Lemma suseds_useds :
  forall U dim (p : ucom U dim), Equal (useds p) (suseds (sequence p)).
Proof.
  intros U dim p.
  induction p as [p1 IH1 p2 IH2 | | |]; symmetry; simpl; auto with set.
  rewrite IH1, IH2. rewrite union_sym. apply suseds_concat.
Qed.

Definition susedb { U dim } (p : uapp U dim) w :=
  match p with
  | uapp_1 _ i => i =? w
  | uapp_2 _ i1 i2 => (i1 =? w) || (i2 =? w)
  | uapp_3 _ i1 i2 i3 => (i1 =? w) || (i2 =? w) || (i3 =? w)
  end.

Lemma susedb_usedb :
  forall U dim (p : uapp U dim) w,
  susedb p w = usedb (uapp_to_ucom p) w.
Proof.
  intros U dim p w. destruct p; reflexivity.
Qed.

Definition wires := nat -> bool.

Definition wunion (w1 w2 : wires) i := w1 i || w2 i.

Lemma wunion_diag :
  forall w, wunion w w = w.
Proof.
  intros w. apply functional_extensionality.
  intros x. unfold wunion. apply orb_diag.
Qed.

Lemma wunion_assoc :
  forall w1 w2 w3, wunion (wunion w1 w2) w3 = wunion w1 (wunion w2 w3).
Proof.
  intros w1 w2 w3. apply functional_extensionality.
  unfold wunion. auto using orb_assoc.
Qed.

Lemma wunion_comm :
  forall w w',
  wunion w w' = wunion w' w.
Proof.
  intros w w'. apply functional_extensionality. intros i.
  unfold wunion. auto with bool.
Qed.

Definition wsubset (w' w : wires) :=
  forall i, w' i = true -> w i = true.

Lemma wsubset_refl :
  forall w, wsubset w w.
Proof.
  unfold wsubset. auto.
Qed.

Lemma wunion_wsubset_1 :
  forall w w' w0, 
  wsubset w w' -> wsubset w (wunion w0 w').
Proof.
  unfold wsubset, wunion. intros w w' w0 H i Hi.
  apply H in Hi. rewrite Hi. apply orb_true_r.
Qed.

Lemma wunion_wsubset_2 :
  forall w w' w0,
  wsubset w w' -> wsubset (wunion w0 w) (wunion w0 w').
Proof.
  unfold wsubset, wunion. intros w w' w0 H i Hi.
  rewrite orb_true_iff in Hi.
  destruct Hi as [Hi | Hi]; try apply H in Hi; try rewrite Hi; auto using orb_true_r.
Qed.

Definition wusedb { U dim } (p : uapp U dim) (w : wires) :=
  match p with
  | uapp_1 _ i => w i
  | uapp_2 _ i1 i2 => w i1 || w i2
  | uapp_3 _ i1 i2 i3 => w i1 || w i2 || w i3
  end.

Lemma wusedb_susedb :
  forall U dim (p : uapp U dim) w,
  wusedb p (Nat.eqb w) = susedb p w.
Proof.
  assert (forall a1 a2 b1 b2, a1 = a2 -> b1 = b2 -> a1 || b1 = a2 || b2).
  { intros. subst. reflexivity. }
  intros U dim p w. destruct p; simpl; auto using Nat.eqb_sym.
Qed.

Lemma wusedb_refl :
  forall U dim (p : uapp U dim),
  wusedb p (susedb p) = true.
Proof.
  intros U dim p. destruct p; simpl; rewrite Nat.eqb_refl; auto.
Qed.

Lemma wusedb_wsubset :
  forall U dim (p : uapp U dim) w' w, wsubset w' w ->
  wusedb p w' = true -> wusedb p w = true.
Proof.
  intros U dim p w' w H.
  destruct p; simpl; repeat rewrite orb_true_iff;
  intros Hu; repeat destruct Hu as [Hu | Hu]; auto.
Qed.

Lemma wusedb_wunion :
  forall U dim (p : uapp U dim) w w',
  wusedb p w = true -> wusedb p (wunion w w') = true.
Proof.
  intros U dim p w w' H.
  destruct p; simpl in *; unfold wunion; repeat rewrite orb_assoc;
  repeat rewrite orb_true_iff in H;
  repeat destruct H as [H | H]; rewrite H; try rewrite orb_true_r; reflexivity.
Qed.

Definition all_wires : wires := const true.

Lemma wusedb_all :
  forall U dim (p : uapp U dim), wusedb p all_wires = true.
Proof.
  intros U dim p. destruct p; reflexivity.
Qed.

Lemma wunion_all :
  forall w, wunion w all_wires = all_wires.
Proof.
  intros ws. apply functional_extensionality. intros x.
  unfold wunion, all_wires, const. apply orb_true_r.
Qed.

Fixpoint dependencies' { U dim } (ps : list (uapp U dim)) w :=
  match ps with
  | [] => []
  | p :: ps' =>
      if wusedb p w
      then p :: dependencies' ps' (wunion (susedb p) w)
      else dependencies' ps' w
  end.

Definition dependencies { U dim } (p : uapp U dim) (ps : list (uapp U dim)) :=
  dependencies' ps (susedb p).

Lemma dependencies'_length_le :
  forall U dim (ps : list (uapp U dim)) w,
  length (dependencies' ps w) <= length ps.
Proof.
  intros U dim ps.
  induction ps; try reflexivity.
  intros w. simpl. destruct (wusedb _ _); simpl; auto using le_n_S.
Qed.

Lemma dependencies_length_le :
  forall U dim (p : uapp U dim) ps,
  length (dependencies p ps) <= length ps.
Proof.
  intros U dim p ps. unfold dependencies. apply dependencies'_length_le.
Qed.

Lemma dependencies_all :
  forall U dim (ps : list (uapp U dim)),
  dependencies' ps all_wires = ps.
Proof.
  intros U dim ps.
  induction ps as [| p ps IH]; try reflexivity.
  simpl. rewrite wusedb_all. rewrite wunion_all. rewrite IH. reflexivity.
Qed.

Lemma dependencies_wunion :
  forall U dim (ps : list (uapp U dim)) w w',
  dependencies' (dependencies' ps (wunion w w')) w = dependencies' ps w.
Proof.
  intros U dim ps.
  induction ps as [| p ps IH]; try reflexivity.
  intros w w'.
  simpl. destruct (wusedb p w) eqn:Eu.
  - eapply wusedb_wunion in Eu as Eu'. rewrite Eu'. simpl. rewrite Eu.
    rewrite <- wunion_assoc.
    assert (forall a b, a = b -> p :: a = p :: b) as H.
    { intros. subst. reflexivity. }
    auto.
  - destruct (wusedb p (wunion w w')) eqn:Eu'; auto.
    simpl. rewrite Eu.
    rewrite wunion_comm. rewrite wunion_assoc.
    auto.
Qed.

Lemma dependencies_wunion_2 :
  forall U dim (ps : list (uapp U dim)) w w',
  dependencies' ps w = ps -> dependencies' ps (wunion w w') = ps.
Proof.
  intros U dim ps.
  induction ps as [| p ps IH]; try reflexivity.
  simpl. intros w w' H.
  destruct (wusedb p w) eqn:E.
  - eapply wusedb_wunion in E as E'. rewrite E'.
    injection H as H.
    replace (dependencies' _ _) with ps; try reflexivity.
    rewrite <- wunion_assoc. symmetry. auto.
  - assert (length (dependencies' ps w) <= length ps) as Hc.
    { apply dependencies'_length_le. }
    rewrite H in Hc. simpl in Hc. lia.
Qed.

Lemma dependencies_wsubset :
  forall U dim (ps : list (uapp U dim)) w' w,
  wsubset w' w ->
  length (dependencies' ps w') <= length (dependencies' ps w).
Proof.
  intros U dim ps. induction ps as [| p ps IH]; try reflexivity.
  intros w' w H. simpl.
  destruct (wusedb p w') eqn:E.
  - eapply wusedb_wsubset in E; try apply H. rewrite E.
    simpl. auto using le_n_S, wunion_wsubset_2.
  - destruct (wusedb p w) eqn:E2; auto.
    simpl. auto using Nat.le_le_succ_r, wunion_wsubset_1.
Qed.

Fixpoint sdepth' { U dim } (ps : list (uapp U dim)) l :=
  match ps, l with
  | p :: ps', S l' => max (S (sdepth' (dependencies p ps') l')) (sdepth' ps' l')
  | _, _=> 0
  end.

Definition sdepth { U dim } (ps : list (uapp U dim)) :=
  sdepth' ps (length ps).

Definition gdepth { U dim } (p : uapp U dim) ps :=
  S (sdepth (dependencies p ps)).

Remark sdepth_spec :
  forall U dim (ps : list (uapp U dim)),
  sdepth ps = match ps with
              | [] => 0
              | p :: ps' => max (gdepth p ps') (sdepth ps')
              end.
Proof.
  intros U dim ps.
  unfold sdepth.
  remember (length ps) as l eqn:E. assert (length ps <= l). { lia. }
  clear E. generalize dependent ps.
  induction l as [l IH] using lt_wf_ind.
  intros ps H. destruct ps as [| p ps]; try (destruct l; reflexivity).
  simpl in H. rewrite Nat.le_succ_l in H.
  destruct l as [| l]; try lia.
  cbn - [ max ].
  assert (length (dependencies p ps) <= length ps).
  { apply dependencies_length_le. }
  unfold gdepth, sdepth.
  assert (forall a b c d, a = b -> c = d -> max a c = max b d) as Hm.
  { intros. subst. reflexivity. }
  apply Hm; repeat rewrite IH; lia.
Qed.

Definition depth { U dim } (p : ucom U dim) :=
  sdepth (sequence p).

Lemma sdepth_zero :
  forall U dim (ps : list (uapp U dim)),
  sdepth ps = 0 <-> ps = [].
Proof.
  intros U dim ps. split; intros H.
  - destruct ps.
    + reflexivity.
    + rewrite sdepth_spec in H. unfold gdepth in H. lia.
  - subst. reflexivity.
Qed.

Lemma sdepth_cons :
  forall U dim (p : uapp U dim) ps,
  sdepth (p :: ps) = max (gdepth p ps) (sdepth ps).
Proof.
  intros U dim p ps. rewrite sdepth_spec. reflexivity.
Qed.

Lemma sdepth_le_dependencies :
  forall U dim (p : uapp U dim) ps,
  sdepth (dependencies p ps) <= sdepth ps.
Proof.
  intros U dim p ps. unfold dependencies.
  remember (susedb p) as w eqn:E. clear E p.
  remember ps as ps' eqn:E. rewrite E at 1.
  assert (sdepth ps <= sdepth ps'). { subst. reflexivity. }
  clear E.
  remember (length ps) as l eqn:E. symmetry in E.
  generalize dependent w. generalize dependent ps'. generalize dependent ps.
  induction l as [l IH] using lt_wf_ind.
  intros ps E. destruct ps as [| p ps]; simpl; try lia.
  intros ps' H w.
  simpl in E. assert (length ps < l) as E'. { lia. }
  rewrite sdepth_spec in H. apply Nat.max_lub_iff in H. destruct H as [Hg Hs].
  destruct (wusedb p w); eauto.
  rewrite sdepth_spec.
  apply Nat.max_lub; eauto.
  apply le_trans with (m := gdepth p ps); try assumption.
  unfold gdepth. apply le_n_S. unfold dependencies.
  rewrite dependencies_wunion. reflexivity.
Qed.

Lemma sdepth_dependencies_wunion :
  forall U dim (ps : list (uapp U dim)) w w',
  sdepth (dependencies' ps w) <= sdepth (dependencies' ps (wunion w w')).
Proof.
  intros U dim ps.
  induction ps as [| p ps IH]; try reflexivity.
  intros w w'.
  simpl. destruct (wusedb p w) eqn:E.
  - rewrite wusedb_wunion; try assumption.
    repeat rewrite sdepth_cons.
    assert (forall a b c d, a <= b -> c <= d -> max a c <= max b d) as Hm.
    { lia. }
    apply Hm.
    + unfold gdepth. apply le_n_S.
      unfold dependencies. repeat rewrite dependencies_wunion. reflexivity.
    + rewrite <- wunion_assoc. auto.
  - destruct (wusedb p (wunion w w')); auto.
    specialize (IH w (wunion w' (susedb p))).
    rewrite sdepth_cons. rewrite Nat.max_comm.
    rewrite wunion_comm. rewrite wunion_assoc. lia.
Qed.

Fixpoint all_depths { U dim } (ps : list (uapp U dim)) :=
  match ps with
  | [] => []
  | p :: ps' => (p, sdepth ps) :: all_depths ps'
  end.

(*
Lemma all_depths_le :
  forall U dim (ps : list (uapp U dim)),
  list_max (map snd (all_depths ps)) <= sdepth ps.
Proof.
  intros U dim ps.
  induction ps as [| p ps IH]; try reflexivity.
  rewrite sdepth_spec. apply list_max_le. Search Forall. rewrite Forall_forall.
  intros d Hd. simpl in Hd. destruct Hd.
  cbn - [ max sdepth ]. Search list_max.
  *)

Definition overlap { U dim } (p p' : uapp U dim) :=
  wusedb p (susedb p').

Lemma overlap_sym :
  forall U dim (p p' : uapp U dim),
  overlap p p' = overlap p' p.
Proof.
  intros U dim p p'. unfold overlap.
  destruct p, p'; simpl;
  apply eq_true_iff_eq; split;
  repeat rewrite orb_true_iff; repeat rewrite Nat.eqb_eq;
  intros H; repeat (try destruct H as [H|H]); subst; auto.
Qed.

Lemma susedb_same_implies_overlap :
  forall U dim (p p' : uapp U dim) w,
  susedb p w = true -> susedb p' w = true ->
  overlap p p' = true.
Proof.
  intros U dim p p' w H H'.
  unfold overlap. destruct p; simpl in H;
  repeat rewrite orb_true_iff in H; repeat destruct H as [H | H];
  apply Nat.eqb_eq in H; subst;
  unfold wusedb; rewrite H'; repeat rewrite orb_true_r; auto.
Qed.

Lemma dependencies_no_overlap :
  forall U dim (p p' : uapp U dim) ps,
  overlap p p' = false <-> dependencies p ps = dependencies p (p' :: ps).
Proof.
  intros U dim p p' ps. split; intros H.
  - unfold dependencies. simpl.
    replace (wusedb _ _) with (overlap p' p) by reflexivity.
    rewrite overlap_sym. rewrite H. reflexivity.
  - unfold dependencies in H. simpl in H.
    replace (wusedb _ _) with (overlap p' p) in H by reflexivity.
    rewrite overlap_sym in H. destruct (overlap p p'); try reflexivity.
    assert (length (dependencies' ps (susedb p)) <
        length (p' :: dependencies' ps (wunion (susedb p') (susedb p)))) as Hl.
    { simpl. apply le_lt_n_Sm. apply dependencies_wsubset.
      apply wunion_wsubset_1. apply wsubset_refl. }
    rewrite H in Hl. lia.
Qed.

Fixpoint remove_wire { U dim } (ps : list (uapp U dim)) w :=
  match ps with
  | [] => ([], [])
  | p :: ps' =>
      match remove_wire ps' w with
      | (k, r) => if susedb p w then (k, p :: r) else (p :: k, r)
      end
  end.

Lemma remove_wire_r :
  forall U dim (ps k r : list (uapp U dim)) w r0,
  remove_wire ps w = (k, r) ->
  List.In r0 r -> susedb r0 w = true.
Proof.
  intros U dim ps.
  induction ps as [| p ps IH].
  - intros k r w r0 H. injection H as H. subst. contradiction.
  - intros k r w r0 H Hi.
    simpl in H. destruct (remove_wire ps w) as [k' r'] eqn:E.
    destruct (susedb p w) eqn:Eu; injection H as H; subst; eauto.
    destruct Hi as [Hi | Hi]; subst; eauto.
Qed.

Lemma remove_wire_all :
  forall U dim (ps k r : list (uapp U dim)) r0 w,
  remove_wire ps w = (k, r0 :: r) ->
  remove_wire r w = ([], r).
Proof.
  intros U dim ps k r r0 w H0.
  assert (forall r1, List.In r1 (r0 :: r) -> susedb r1 w = true) as H1.
  { intros r1. eapply remove_wire_r. apply H0. }
  assert (forall r1, List.In r1 r -> susedb r1 w = true) as H.
  { intros r1 Hi. apply H1. right. assumption. }
  clear ps k r0 H0 H1.
  induction r as [| r0 r IH]; try reflexivity.
  assert (remove_wire r w = ([], r)) as Hr.
  { apply IH. intros r1 H'. apply H. right. assumption. }
  simpl. rewrite Hr.
  assert (susedb r0 w = true) as H0. { apply H. left. reflexivity. }
  rewrite H0. reflexivity.
Qed.

Lemma remove_wire_sdepth_r :
  forall U dim (ps k r : list (uapp U dim)) w,
  remove_wire ps w = (k, r) ->
  sdepth r = length r.
Proof.
  intros U dim ps.
  induction ps as [| p ps IH].
  - intros k r w H. injection H as H. subst. reflexivity.
  - intros k r w H.
    simpl in H. destruct (remove_wire ps w) as [k' r'] eqn:E.
    specialize (IH k' r' w E).
    destruct (susedb p w) eqn:Eu; injection H as H; subst; eauto.
    simpl. rewrite sdepth_spec. unfold gdepth.
    replace (dependencies p r') with r'; try (rewrite IH; lia).
    unfold dependencies.
    clear IH. generalize dependent k. generalize dependent ps.
    induction r' as [| r0 r IHr]; try reflexivity.
    intros ps k H.
    simpl. 
    assert (List.In r0 (r0 :: r)) as H0. { simpl. auto. }
    assert (wusedb r0 (susedb p) = true) as Hu.
    { specialize (remove_wire_r U dim ps k (r0 :: r) w r0 H H0) as Hr.
      Search overlap.
      specialize (susedb_same_implies_overlap U dim r0 p w Hr Eu) as Ho.
      unfold overlap in Ho. assumption. }
    rewrite Hu.
    assert (remove_wire r w = ([], r)). { eauto using remove_wire_all. }
    specialize (IHr r [] H1).
    symmetry in IHr. eapply dependencies_wunion_2 in IHr. 
    rewrite wunion_comm. rewrite IHr. reflexivity.
Qed.

Lemma remove_wire_sdepth_r_le :
  forall U dim (ps k r : list (uapp U dim)) w,
  remove_wire ps w = (k, r) ->
  forall ws,
  sdepth (dependencies' r ws) <= sdepth (dependencies' ps ws).
Proof.
  intros U dim ps.
  induction ps as [| p ps IH].
  - intros k r w H. injection H as. subst. reflexivity.
  - intros k r w H ws.
    simpl in H. destruct (remove_wire ps w) as [k' r'] eqn:E.
    specialize (IH k' r' w E).
    destruct (susedb p w) eqn:Eu; injection H as; subst.
    + simpl. destruct (wusedb p ws) eqn:Ew; auto.
      repeat rewrite sdepth_cons.
      assert (forall a b c d, a <= b -> c <= d -> max a c <= max b d) as Hm.
      { lia. }
      apply Hm; auto.
      unfold gdepth. apply le_n_S.
      unfold dependencies. repeat rewrite dependencies_wunion. auto.
    + simpl. destruct (wusedb p ws); auto.
      rewrite sdepth_cons.
      eapply le_trans; try apply IH.
      assert (forall a b c, a <= b -> a <= max c b) as Hm. { lia. }
      apply Hm.
      rewrite wunion_comm.
      apply sdepth_dependencies_wunion.
Qed.

(* TODO remove duplication *)
Lemma remove_wire_sdepth_k_le :
  forall U dim (ps k r : list (uapp U dim)) w,
  remove_wire ps w = (k, r) ->
  forall ws,
  sdepth (dependencies' k ws) <= sdepth (dependencies' ps ws).
Proof.
  intros U dim ps.
  induction ps as [| p ps IH].
  - intros k r w H. injection H as. subst. reflexivity.
  - intros k r w H ws.
    simpl in H. destruct (remove_wire ps w) as [k' r'] eqn:E.
    specialize (IH k' r' w E).
    destruct (susedb p w) eqn:Eu; injection H as; subst.
    + simpl. destruct (wusedb p ws) eqn:Ew; auto.
      rewrite sdepth_cons.
      eapply le_trans; try apply IH.
      assert (forall a b c, a <= b -> a <= max c b) as Hm. { lia. }
      apply Hm.
      rewrite wunion_comm.
      apply sdepth_dependencies_wunion.
    + simpl. destruct (wusedb p ws); auto.
      repeat rewrite sdepth_cons.
      assert (forall a b c d, a <= b -> c <= d -> max a c <= max b d) as Hm.
      { lia. }
      apply Hm; auto.
      unfold gdepth. apply le_n_S.
      unfold dependencies. repeat rewrite dependencies_wunion. auto.
Qed.

Lemma remove_wire_total :
  forall U dim (ps k r : list (uapp U dim)) w,
  remove_wire ps w = (k, r) ->
  length ps = length k + length r.
Proof.
  intros U dim ps.
  induction ps as [| p ps IH].
  - intros k r w H. injection H as H. subst. reflexivity.
  - intros k r w H. simpl.
    simpl in H. destruct (remove_wire ps w) as [k' r'] eqn:E.
    specialize (IH k' r' w E).
    destruct (susedb p w); injection H as H; subst; simpl; lia.
Qed.

Lemma remove_wire_count :
  forall U dim (ps k r : list (uapp U dim)) w,
  remove_wire ps w = (k, r) ->
  length ps <= length k + sdepth ps.
Proof.
  intros U dim ps k r w H.
  erewrite remove_wire_total; try apply H.
  apply plus_le_compat_l.
  erewrite <- remove_wire_sdepth_r; try apply H.
  specialize (dependencies_all U dim r) as Hr.
  specialize (dependencies_all U dim ps) as Hp.
  rewrite <- Hr. rewrite <- Hp. eauto using remove_wire_sdepth_r_le.
Qed.

Lemma remove_union :
  forall x s t,
  Equal (remove x (union s t)) (union (remove x s) (remove x t)).
Proof.
  intros x s t i. split; intros H.
  - repeat rewrite union_spec, remove_spec in *.
    destruct H as [[H | H] H']; auto.
  - repeat rewrite union_spec, remove_spec in *.
    destruct H as [[H H'] | [H H']]; auto.
Qed.

Lemma remove_wire_qubits_subset :
  forall U dim (ps k r : list (uapp U dim)) w, remove_wire ps w = (k, r) ->
  Subset (suseds k) (remove w (suseds ps)).
Proof.
  intros U dim ps.
  induction ps as [| p ps IH].
  - intros k r w H. injection H as. subst. auto with set.
  - intros k r w H.
    simpl in H. destruct (remove_wire ps w) as [k' r'] eqn:E.
    specialize (IH k' r' w E).
    destruct (susedb p w) eqn:Eu.
    + injection H as. subst. simpl.
      rewrite remove_union.
      intros i Hi. specialize (IH i Hi). auto with set.
    + injection H as. subst.
      simpl. rewrite remove_union.
      intros i Hi. rewrite union_spec in Hi.
      destruct Hi as [Hi | Hi]; auto with set.
      assert (i <> w).
      { intros H. subst.
        rewrite in_useds_iff_used in Hi. apply usedb_iff_used in Hi.
        rewrite <- susedb_usedb in Hi. rewrite Eu in Hi. discriminate. }
      rewrite union_spec. left.
      rewrite remove_spec. split; try assumption.
Qed.

Fact gates_le_qubits_depth :
  forall U dim (p : ucom U dim), gates p <= qubits p * depth p.
Proof.
  intros U dim p.
  unfold depth. rewrite sequence_gates. unfold qubits. rewrite suseds_useds.
  remember (sequence p) as ps eqn:E. clear E p.
  remember (cardinal (suseds ps)) as q eqn:E. symmetry in E.
  generalize dependent ps.
  induction q as [q IH] using lt_wf_ind.
  intros ps H.
  destruct (elements (suseds ps)) as [| w e] eqn:E.
  - assert (q = 0) as H0.
    { rewrite <- elements_Empty in E. rewrite cardinal_Empty in E. lia. }
    subst.
    destruct ps as [| p ps]; simpl; try lia.
    exfalso.
    simpl in H0. rewrite <- cardinal_Empty in H0. unfold Empty in H0.
    destruct p as [u i | u i | u i]; specialize (H0 i);
        apply H0; simpl; auto with set.
  - assert (In w (suseds ps)) as He.
    { rewrite <- elements_spec1. rewrite E. auto. }
    remember (remove_wire ps w) as ps' eqn:Ek. symmetry in Ek. 
    destruct ps' as [k r].
    assert (S(cardinal (remove w (suseds ps))) = cardinal (suseds ps)) as Hs.
    { auto using remove_cardinal_1. }
    assert (cardinal (suseds k) < q) as Hc.
    { eapply le_lt_trans.
      - apply subset_cardinal. eapply remove_wire_qubits_subset. apply Ek.
      - rewrite <- H. lia. }
    specialize (IH (cardinal (suseds k)) Hc k eq_refl).
    specialize (remove_wire_count U dim ps k r w Ek) as Hr.
    eapply le_trans; try apply Hr.
    destruct q as [| q]; try lia.
    rewrite Nat.mul_succ_l. apply plus_le_compat_r.
    eapply le_trans; try apply IH.
    apply lt_n_Sm_le in Hc.
    apply Nat.mul_le_mono; try assumption.
    assert (k = dependencies' k all_wires) as Hk.
    { rewrite dependencies_all. reflexivity. }
    assert (ps = dependencies' ps all_wires) as Hp.
    { rewrite dependencies_all. reflexivity. }
    rewrite Hk. rewrite Hp.
    eauto using remove_wire_sdepth_k_le.
Qed.

