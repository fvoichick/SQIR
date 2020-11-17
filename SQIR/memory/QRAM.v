Require Import RCIR VectorStates.
Require Import Bvector Vector.
Require Import Arith.
Require Import Psatz.
Require Import Eqdep_dec.
Require Import Equivalence Morphisms.
Require Import Decidable.
Require Import Wires.

Import Nat (eq_dec).

Open Scope vector_scope.
Open Scope nat_scope.
Open Scope bccom_scope.

(*
Lemma no_overlap_sym :
  forall ws ws', no_overlap ws ws' -> no_overlap ws' ws.
Proof.
  unfold no_overlap. intros. rewrite inter_sym. assumption.
Qed.

Lemma no_overlap_impl :
  forall ws ws', (forall q, In q ws -> ~ In q ws') <-> no_overlap ws ws'.
Proof.
  intros ws ws'. split.
  - intros H q. rewrite inter_spec. intros [Hc H']. apply (H q); assumption.
  - intros H q Hi H'. apply (H q). rewrite inter_spec. auto.
Qed.

Instance no_overlap_Symmetric :
  Symmetric no_overlap :=
  no_overlap_sym.

Instance no_overlap_Proper :
  Proper (Subset ==> Subset ==> flip impl) no_overlap.
Proof.
  unfold no_overlap.
  intros ws1 ws2 H ws3 ws4 He. rewrite H, He. reflexivity.
Qed.

Lemma no_overlap_or :
  forall ws ws',
  no_overlap ws ws' <-> forall q, ~ In q ws \/ ~ In q ws'.
Proof.
  unfold no_overlap. intros ws ws'. split; intros H q.
  - specialize (H q). rewrite inter_spec in H.
    auto using not_and, Dec.MSetDecideAuxiliary.dec_In.
  - rewrite inter_spec. destruct (H q); tauto.
Qed.*)

Definition addr (n : nat) := nat.

Definition addr_hd {n} (a : addr (S n)) : nat := a.

Definition addr_tl {n} (a : addr (S n)) : addr n := S a.

Definition addr_index {n} (a : addr n) i : nat := a + i.

Fixpoint addr_wires {n} : addr n -> wires :=
  match n with
  | 0 => fun a => empty
  | S n' => fun a => add (addr_hd a) (addr_wires (addr_tl a))
  end.

Lemma addr_wires_hd :
  forall n (a : addr (S n)), In (addr_hd a) (addr_wires a).
Proof.
  simpl. intros n a. autorewrite with simpl_wires. auto.
Qed.

Lemma addr_wires_tl :
  forall n (a : addr (S n)),
  Subset (addr_wires (addr_tl a)) (addr_wires a).
Proof.
  simpl. intros n a q. autorewrite with simpl_wires. auto.
Qed.

Lemma addr_wires_ineq :
  forall n (a : addr n),
  Equal (addr_wires a) (fun q => a <= q < a + n).
Proof.
  intros n. induction n as [| n IH]; simpl.
  - intros a q. autorewrite with simpl_wires. unfold In. lia.
  - unfold addr_hd, addr_tl.
    intros a q. autorewrite with simpl_wires. rewrite IH. unfold In. lia.
Qed.

Lemma addr_wires_tl_no_hd :
  forall n (a : addr (S n)),
  ~ In (addr_hd a) (addr_wires (addr_tl a)).
Proof.
  unfold addr_hd, addr_tl.
  intros n a Hc. apply addr_wires_ineq in Hc. unfold In in Hc. lia.
Qed.

Lemma hd_not_In_different_tl :
  forall n (a a' : addr (S n)),
  all_different (addr_wires a) (addr_wires a') -> 
  ~ In (addr_hd a) (addr_wires (addr_tl a')).
Proof.
  intros n a a' H Hc. eapply H.
  - apply addr_wires_hd.
  - apply addr_wires_tl. apply Hc.
Qed.

(* Sometimes convenient for proofs involving types dependent on a nat *)

Lemma injection_existT :
  forall n (P : nat -> Type) (v v' : P n),
  existT P n v = existT P n v' <->
  v = v'.
Proof.
  split; intros H.
  - auto using inj_pair2_eq_dec, eq_dec.
  - subst. reflexivity.
Qed.

Fixpoint bits_at_addr (f : nat -> bool) {n} : addr n -> Bvector n :=
  match n with
  | 0 => fun _ => []
  | S n' => fun a => f (addr_hd a) :: bits_at_addr f (addr_tl a)
  end.

(* Is there a tactic that splits goals like this automatically? *)

Lemma hd_tl_separately :
  forall n h1 (t1 : Bvector n) h2 t2, h1 = h2 -> t1 = t2 -> h1 :: t1 = h2 :: t2.
Proof.
  intros. subst. reflexivity.
Qed.

(*
Lemma bits_at_addr_update :
  forall n f (a : addr n) q b,
  ~ In q (addr_wires a) ->
  bits_at_addr (q :-> b $ f) a = bits_at_addr f a.
Proof.
  intros n. induction n as [| n IH]; try reflexivity.
  intros. simpl.
  apply hd_tl_separately.
  - rewrite update_index_neq; try reflexivity.
    intros Hc. subst. auto using addr_wires_hd.
  - apply IH. intros Hc. apply H. apply addr_wires_tl. assumption.
Qed.
*)

Inductive addr_zero f : forall {n}, addr n -> Prop :=
  | addr_zero_0 (a : addr 0) : addr_zero f a
  | addr_zero_S {n} (a : addr (S n)) :
  f (addr_hd a) = false -> addr_zero f (addr_tl a) -> addr_zero f a.

Lemma addr_zero_spec :
  forall f n (a : addr n),
  addr_zero f a <-> Subset (addr_wires a) (fun q => f q = false).
Proof.
  intros f n a. split; intros H.
  - induction H; simpl.
    + apply empty_Subset.
    + intros q Hi. rewrite add_spec in Hi. destruct Hi; subst; auto.
  - induction n as [| n IH]; constructor.
    + apply H. apply addr_wires_hd.
    + eauto using Subset_trans, addr_wires_tl.
Qed.

Lemma addr_zero_bits :
  forall f n (a : addr n),
  addr_zero f a <-> bits_at_addr f a = Bvect_false n.
Proof.
  intros f n a. split; intros H.
  - induction H; try reflexivity.
    simpl in *. auto using hd_tl_separately.
  - induction n as [| n IH]; constructor; simpl in H;
    injection H as Hh Ht; try assumption.
    apply injection_existT in Ht. apply IH. apply Ht.
Qed.

Fixpoint used_wires p : wires :=
  match p with
  | bcskip => empty
  | bcx q => singleton q
  | bccont q p' => add q (used_wires p')
  | bcseq p1 p2 => union (used_wires p1) (used_wires p2)
  end.

Lemma inv_used :
  forall p, Equal (used_wires (bcinv p)) (used_wires p).
Proof.
  intros p. induction p as [| | q p IH | p1 IH1 p2 IH2]; simpl; try reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH1, IH2. rewrite union_sym. reflexivity.
Qed.

Fixpoint usedb p i :=
  match p with
  | bcskip => false
  | bcx q => i =? q
  | bccont q p' => (i =? q) || usedb p' i
  | bcseq p1 p2 => usedb p1 i || usedb p2 i
  end.

Lemma used_wires_usedb :
  forall p,
  Equal (used_wires p) (fun q => usedb p q = true).
Proof.
  intros p q.
  induction p as [| | i p IH | p IH p' IH']; simpl;
      autorewrite with simpl_wires.
  - unfold In. split.
    + contradiction.
    + discriminate.
  - unfold In. split.
    + intros. subst. apply Nat.eqb_refl.
    + apply beq_nat_true.
  - rewrite IH. unfold In. rewrite <- Nat.eqb_eq, orb_true_iff. reflexivity.
  - rewrite IH, IH'. unfold In. rewrite orb_true_iff. reflexivity.
Qed.

Lemma dec_used :
  forall p q, decidable (In q (used_wires p)).
Proof.
  intros p q. destruct (usedb p q) eqn:E.
  - left. apply used_wires_usedb. assumption.
  - right. rewrite used_wires_usedb. unfold In.
    apply not_true_iff_false. assumption.
Qed.

Inductive well_formed : bccom -> Prop :=
  | well_formed_skip : well_formed bcskip
  | well_formed_x q : well_formed (bcx q)
  | well_formed_ctrl q p :
      ~ In q (used_wires p) -> well_formed p -> well_formed (bccont q p)
  | well_formed_seq p1 p2 :
      well_formed p1 -> well_formed p2 -> well_formed (p1; p2).

Lemma cnot_wf :
  forall q q', q <> q' <-> well_formed (bccnot q q').
Proof.
  intros q q'. split.
  - intros H. unfold bccnot. constructor; try constructor. simpl.
    autorewrite with simpl_wires. assumption.
  - intros H Hc. inversion_clear H. apply H0. simpl. 
    autorewrite with simpl_wires. assumption.
Qed.

Lemma inv_wf :
  forall p, well_formed p -> well_formed (bcinv p).
Proof.
  intros p H.
  induction H; simpl; constructor; auto. rewrite inv_used. assumption.
Qed.

Definition changed_wires (p : bccom) : wires :=
  fun q => exists f, bcexec p f q <> f q.

Lemma bcexec_unchanged :
  forall p f q, ~ In q (changed_wires p) -> bcexec p f q = f q.
Proof.
  intros p f q H. unfold changed_wires, In in H.
  destruct (bool_dec (bcexec p f q) (f q)).
  - assumption.
  - exfalso. apply H. exists f. assumption.
Qed.

Lemma bcexec_seq_unchanged :
  forall p1 p2 f q,
  ~ In q (changed_wires p2) ->
  bcexec (p1 ; p2) f q = bcexec p1 f q.
Proof.
  intros p1 p2 f q H.
  destruct (bool_dec (bcexec (p1; p2) f q) (bcexec p1 f q)) as [| Hd];
      try assumption.
  exfalso. apply H. unfold changed_wires, In. exists (bcexec p1 f). assumption.
Qed.

Lemma bcexec_bits_unchanged :
  forall p f n (a : addr n),
  all_different (addr_wires a) (changed_wires p) ->
  bits_at_addr (bcexec p f) a = bits_at_addr f a.
Proof.
  intros f p n a H. induction n as [| n IH]; try reflexivity. simpl.
  apply hd_tl_separately.
  - eauto using bcexec_unchanged, addr_wires_hd.
  - apply IH. rewrite addr_wires_tl. assumption.
Qed.

Lemma bcexec_update_unused :
  forall p f q b,
  ~ In q (used_wires p) -> bcexec p (f [q |-> b]) = (bcexec p f) [q |-> b].
Proof.
  intros p. induction p as [| | i | p1 IH1 p2 IH2]; simpl;
      intros f q b H; autorewrite with simpl_wires in H.
  - reflexivity.
  - rewrite update_index_neq, update_twice_neq; auto.
  - apply not_or in H as []. rewrite update_index_neq; destruct (f i); auto.
  - apply not_or in H as []. rewrite IH1, IH2; auto.
Qed.

Lemma changed_wires_used :
  forall p, Subset (changed_wires p) (used_wires p).
Proof.
  intros p.
  induction p as [| q | q p IH | p1 IH1 p2 IH2]; intros i [f H]; simpl in *;
      autorewrite with simpl_wires.
  - contradiction.
  - destruct (eq_dec i q); try assumption.
    rewrite update_index_neq in H; congruence.
  - destruct (f q) eqn:E; try contradiction.
    destruct (eq_dec i q); auto. right.
    apply IH. exists f. assumption.
  - destruct (bool_dec (bcexec p1 f i) (f i)).
    + right. apply IH2. exists (bcexec p1 f). congruence.
    + left. apply IH1. exists f. assumption.
Qed.

Lemma unused_wires_unchanged :
  forall p q, ~ In q (used_wires p) -> ~ In q (changed_wires p).
Proof.
  intros p q H Hc. apply H, changed_wires_used. assumption.
Qed.

Lemma changed_Subset :
  forall p,
  Subset (changed_wires p) 
         (match p with
          | bcskip => empty
          | bcx q => singleton q
          | bccont q p' => changed_wires p'
          | p1; p2 => union (changed_wires p1) (changed_wires p2)
          end).
Proof.
  intros p.
  destruct p as [| q | q p | p1 p2]; 
      intros i [f H]; simpl in H; autorewrite with simpl_wires.
  - contradiction.
  - destruct (eq_dec i q); try assumption. exfalso. apply H.
    apply update_index_neq. auto.
  - destruct (f q); try contradiction. exists f. assumption.
  - destruct (bool_dec (bcexec p1 f i) (f i)).
    + right. exists (bcexec p1 f). congruence.
    + left. exists f. assumption.
Qed.

Lemma skip_changed :
  Equal (changed_wires bcskip) empty.
Proof.
  apply Equal_Subset. split; try apply changed_Subset.
  apply empty_Subset.
Qed.

Lemma x_changed :
  forall q, Equal (changed_wires (bcx q)) (singleton q).
Proof.
  intros q. apply Equal_Subset. split; try apply changed_Subset.
  intros i H. autorewrite with simpl_wires in H. subst.
  exists (fun _ => false). simpl. rewrite update_index_eq. discriminate.
Qed.

Lemma ctrl_changed :
  forall q p, 
  well_formed (bccont q p) ->
  Equal (changed_wires (bccont q p)) (changed_wires p).
Proof.
  intros q p H i. inversion_clear H. split; intros [f Hf].
  - simpl in Hf. destruct (f q); try contradiction.
    exists f. assumption.
  - exists (f [q |-> true]). simpl. 
    rewrite update_index_eq. destruct (eq_dec i q).
    + subst. rewrite bcexec_unchanged in Hf; try contradiction.
      rewrite changed_wires_used. assumption.
    + rewrite update_index_neq; auto.
      rewrite bcexec_update_unused; try assumption.
      rewrite update_index_neq; auto.
Qed.

Lemma cnot_changed :
  forall c q, Equal (changed_wires (bccnot c q)) (singleton q).
Proof.
  intros c q. rewrite Equal_Subset. split.
  - unfold bccnot. rewrite changed_Subset, x_changed. reflexivity.
  - intros i Hi. autorewrite with simpl_wires in Hi. subst.
    unfold changed_wires, In. simpl.
    exists (fun _ => true). rewrite update_index_eq. discriminate.
Qed.
 
Lemma p_inv_p_unchanged :
  forall p, well_formed p -> Equal (changed_wires (p; bcinv p)) empty.
Proof.
  intros p H i. autorewrite with simpl_wires. split; try contradiction.
  intros [f Hf]. apply Hf. clear Hf. simpl. 
  apply equal_f. clear i. generalize dependent f.
  induction H as [| q | q p Hc Hw IH | p1 p2 Hw1 IH1 Hw2 IH2]; 
      intros f; apply functional_extensionality; intros i; simpl.
  - reflexivity.
  - destruct (eq_dec q i).
    + subst. repeat rewrite update_index_eq. apply negb_involutive.
    + repeat rewrite update_index_neq; auto.
  - rewrite <- changed_wires_used in Hc.
    destruct (f q) eqn:E; try (rewrite E; reflexivity).
    rewrite bcexec_unchanged; try assumption. rewrite E, IH. reflexivity.
  - rewrite IH2, IH1. reflexivity.
Qed.

Lemma bcexec_p_inv_p :
  forall p f, well_formed p -> bcexec (bcinv p) (bcexec p f) = f.
Proof.
  intros p f H. apply functional_extensionality. intros q.
  destruct (bool_dec (bcexec (p; bcinv p) f q) (f q)); try assumption.
  exfalso. eapply p_inv_p_unchanged.
  - apply H.
  - exists f. apply n.
Qed.

Lemma bcexec_inv_p_p :
  forall p f, well_formed p -> bcexec p (bcexec (bcinv p) f) = f.
Proof.
  intros p f H.
  replace p with (bcinv (bcinv p)) at 1;
  auto using bcinv_involutive, bcexec_p_inv_p, inv_wf.
Qed.

Lemma inv_changed :
  forall p,
  well_formed p ->
  Equal (changed_wires (bcinv p)) (changed_wires p).
Proof.
  intros p H q. split; intros [f Hf].
  - exists (bcexec (bcinv p) f). rewrite bcexec_inv_p_p; auto.
  - exists (bcexec p f). rewrite bcexec_p_inv_p; auto.
Qed.

Lemma bool_eq_dec :
  forall (a b : bool), decidable (a = b).
Proof.
  unfold decidable. intros a b. destruct (bool_dec a b); auto.
Qed.

Lemma no_conflict_commute :
  forall p p',
  all_different (used_wires p) (used_wires p') ->
  bcexec (p; p') = bcexec (p'; p).
Proof.
  intros p p' H. apply functional_extensionality.
  induction p as [| q | q p IH | p1 IH1 p2 IH2 ]; simpl in *; intros f.
  - reflexivity.
  - rewrite bcexec_update_unused.
    + rewrite bcexec_unchanged; try reflexivity.
      specialize (H q). autorewrite with simpl_wires in H.
      specialize (H eq_refl).
      intros Hc. apply H. apply changed_wires_used. assumption.
    + intros Hc. specialize (H q). autorewrite with simpl_wires in H.
      specialize (H eq_refl Hc). contradiction.
  - rewrite bcexec_unchanged.
    + destruct (f q); try reflexivity. apply IH. rewrite add_Subset. apply H.
    + intros Hc. eapply H.
      * autorewrite with simpl_wires. left. reflexivity.
      * apply changed_wires_used. assumption.
  - rewrite IH2, IH1.
    + reflexivity.
    + rewrite union_Subset. apply H.
    + rewrite union_Subset. rewrite union_sym. apply H.
Qed.

Lemma seq_no_conflict_changed :
  forall p1 p2,
  all_different (used_wires p1) (used_wires p2) ->
  Equal (changed_wires (p1; p2)) (union (changed_wires p1) (changed_wires p2)).
Proof.
  intros p1 p2 H i. split; try apply changed_Subset.
  intros [Hc | Hc]; apply changed_wires_used in Hc as Hu;
      destruct Hc as [f Hf]; exists f.
  - simpl. apply H in Hu.
    rewrite bcexec_unchanged; auto using unused_wires_unchanged.
  - rewrite no_conflict_commute; try assumption. 
    simpl. rewrite bcexec_unchanged; try assumption.
    intros Hc. eapply H; try apply Hu.
    apply changed_wires_used; assumption.
Qed.

Fixpoint share {w} : addr w -> addr w -> bccom :=
  match w with
  | 0 => fun _ _ => bcskip
  | S _ =>
      fun from to =>
      share (addr_tl from) (addr_tl to); bccnot (addr_hd from) (addr_hd to)
  end.

Lemma share_used :
  forall w (from to : addr w),
  Equal (used_wires (share from to)) (union (addr_wires from) (addr_wires to)).
Proof.
  induction w as [| w IH]; intros from to q; simpl;
      try rewrite IH; autorewrite with simpl_wires; tauto.
Qed.

Lemma share_wf :
  forall w (from to : addr w),
  all_different (addr_wires from) (addr_wires to) ->
  well_formed (share from to).
Proof.
  intros w. induction w as [| w IH]; simpl; intros from to H; constructor.
  - apply IH. repeat rewrite <- add_Subset in H. assumption.
  - apply cnot_wf. intros Hc. eapply H; autorewrite with simpl_wires; auto.
Qed.

Lemma share_changed :
  forall w (from to : addr w),
  Subset (changed_wires (share from to)) (addr_wires to).
Proof.
  intros w. induction w as [| w IH]; simpl.
  - intros. rewrite skip_changed. apply empty_Subset.
  - intros from to q H.
    rewrite changed_Subset in H. autorewrite with simpl_wires in H.
    rewrite IH, cnot_changed in H. autorewrite with simpl_wires in *. tauto.
Qed.

Lemma cnot_share :
  forall from to f,
  f to = false ->
  bcexec (bccnot from to) f to = f from.
Proof.
  intros. simpl. destruct (f from); try assumption.
  rewrite update_index_eq. rewrite H. reflexivity.
Qed.

Lemma share_bits :
  forall w (from to : addr w) f,
  all_different (addr_wires from) (addr_wires to) ->
  addr_zero f to ->
  bits_at_addr (bcexec (share from to) f) to = bits_at_addr f from.
Proof.
  intros w. induction w as [| w IH]; try reflexivity. cbn - [ bcexec ].
  intros from to f Ho H. apply hd_tl_separately.
  - rewrite no_conflict_commute.
    + rewrite bcexec_seq_unchanged.
      * apply cnot_share. inversion H. assumption.
      * intros Hc. apply share_changed in Hc.
        apply addr_wires_tl_no_hd in Hc. contradiction.
    + rewrite share_used. simpl.
      intros q Hu Ha. autorewrite with simpl_wires in Hu, Ha.
      destruct Hu as [Hu | Hu], Ha as [Ha | Ha]; subst.
      * apply addr_wires_tl_no_hd in Hu. contradiction.
      * eapply hd_not_In_different_tl.
        -- symmetry. apply Ho.
        -- assumption.
      * eapply hd_not_In_different_tl; eauto.
      * apply addr_wires_tl_no_hd in Hu. contradiction.
  - cbn - [ bccnot ]. rewrite bcexec_bits_unchanged.
    + apply IH.
      * repeat rewrite addr_wires_tl. assumption.
      * inversion H. assumption.
    + intros q Ht Hh.
      rewrite cnot_changed in Hh. autorewrite with simpl_wires in Hh. subst.
      apply addr_wires_tl_no_hd in Ht. contradiction.
Qed.

Lemma same_input_same_output :
  forall p f f',
  well_formed p ->
  (forall q, In q (used_wires p) -> f q = f' q) ->
  forall q, In q (used_wires p) -> bcexec p f q = bcexec p f' q.
Proof.
  intros p.
  induction p as [| q | q p IH | p1 IH1 p2 IH2]; intros f f' Hw H i Hi;
      simpl in *; autorewrite with simpl_wires in *; inversion_clear Hw.
  - contradiction.
  - subst. repeat rewrite update_index_eq. rewrite H; try reflexivity.
    simpl. autorewrite with simpl_wires. reflexivity.
  - assert (f q = f' q) as H'. { apply H. autorewrite with simpl_wires. auto. }
    rewrite <- H'. destruct Hi as [Hq | Hi].
    + subst. destruct (f q) eqn:E; try congruence.
      repeat rewrite bcexec_unchanged; auto using unused_wires_unchanged.
      congruence. 
    + destruct (f q); try (apply IH; try assumption; intros);
      apply H; autorewrite with simpl_wires; auto.
  - destruct (dec_used p2 i).
    + apply IH2; try assumption.
      intros q Hq. destruct (dec_used p1 q).
      * apply IH1; try assumption.
        intros q' H'. apply H. autorewrite with simpl_wires. auto.
      * repeat rewrite bcexec_unchanged; auto using unused_wires_unchanged.
        apply H. autorewrite with simpl_wires. auto.
    + rewrite bcexec_unchanged; auto using unused_wires_unchanged. symmetry.
      rewrite bcexec_unchanged; auto using unused_wires_unchanged. symmetry.
      destruct (dec_used p1 i).
      * apply IH1; try assumption.
        intros. apply H. autorewrite with simpl_wires. auto.
      * repeat rewrite bcexec_unchanged; auto using unused_wires_unchanged.
Qed.

Lemma remove_unchanged :
  forall p1 p2 f q,
  well_formed p2 ->
  all_different (changed_wires p1) (used_wires p2) ->
  ~ In q (changed_wires p1) ->
  bcexec p2 (bcexec p1 f) q = bcexec p2 f q.
Proof.
  intros p1 p2 f q Hw Hd Hc. 
  destruct (dec_used p2 q).
  - apply same_input_same_output; try assumption.
    intros i Hi.
    destruct (bool_dec (bcexec p1 f i) (f i)); try assumption. exfalso.
    eapply Hd; try apply Hi.
    exists f. assumption.
  - symmetry. rewrite bcexec_unchanged; auto using unused_wires_unchanged.
    symmetry. rewrite bcexec_unchanged; auto using unused_wires_unchanged.
    destruct (bool_dec (bcexec p1 f q) (f q)); try assumption. exfalso.
    apply Hc. exists f. assumption.
Qed.

Lemma bcexec_seq_assoc :
  forall p1 p2 p3, bcexec ((p1; p2); p3) = bcexec (p1; (p2; p3)).
Proof. reflexivity. Qed.

Definition seq_inv p1 p2 :=
  p1; p2; bcinv p1.

Lemma seq_inv_used :
  forall p1 p2,
  Equal (used_wires (seq_inv p1 p2)) (union (used_wires p1) (used_wires p2)).
Proof.
  intros p1 p2. unfold seq_inv. simpl.
  rewrite inv_used, union_sym. autorewrite with simpl_wires. reflexivity.
Qed.

Lemma seq_inv_wf :
  forall p1 p2, 
  well_formed p1 -> well_formed p2 ->
  well_formed (seq_inv p1 p2).
Proof.
  unfold seq_inv. intros p1 p2 H1 H2.
  constructor.
  - constructor; assumption.
  - apply inv_wf. assumption.
Qed.

Lemma seq_inv_changed_Subset :
  forall p1 p2,
  well_formed p1 -> well_formed p2 ->
  all_different (used_wires p1) (changed_wires p2) ->
  Subset (changed_wires (seq_inv p1 p2)) (changed_wires p2).
Proof.
  unfold seq_inv. intros p1 p2 H1 H2 Hd q [f Hf]. simpl in Hf.
  destruct (dec_used p1 q) as [H | H].
  - exfalso. apply Hf. clear Hf.
    rewrite remove_unchanged.
    + rewrite bcexec_p_inv_p; auto.
    + auto using inv_wf.
    + rewrite inv_used. symmetry. assumption.
    + eauto.
  - exists (bcexec p1 f). intros Hc. apply Hf.
    rewrite bcexec_unchanged.
    + rewrite Hc. rewrite bcexec_unchanged; auto using unused_wires_unchanged.
    + rewrite inv_changed; auto using unused_wires_unchanged.
Qed.

Lemma seq_inv_changed :
  forall p1 p2,
  well_formed p1 -> well_formed p2 ->
  all_different (used_wires p1) (changed_wires p2) ->
  Equal (changed_wires (seq_inv p1 p2)) (changed_wires p2).
Proof.
  intros. rewrite Equal_Subset. 
  split; try (apply seq_inv_changed_Subset; assumption).
  remember (seq_inv p1 p2) as p3.
  assert (Subset (changed_wires (seq_inv (bcinv p1) p3)) (changed_wires p3))
      as Hs.
  { subst. apply seq_inv_changed_Subset.
    - apply inv_wf. assumption.
    - apply seq_inv_wf; assumption.
    - rewrite seq_inv_changed_Subset; try rewrite inv_used; auto. }
  subst. intros q [f Hf]. apply Hs. exists f. unfold seq_inv. simpl.
  rewrite bcexec_inv_p_p, bcinv_involutive, bcexec_inv_p_p; assumption.
Qed.

Lemma bcexec_seq_inv :
  forall p1 p2 f q,
  well_formed p1 ->
  ~ In q (used_wires p1) ->
  bcexec (seq_inv p1 p2) f q = bcexec (p1; p2) f q.
Proof.
  intros p1 p2 f q Hw Hu. unfold seq_inv. simpl.
  rewrite bcexec_unchanged; try rewrite inv_changed;
  auto using unused_wires_unchanged.
Qed.

Lemma seq_inv_bits :
  forall n p1 p2 f (a : addr n),
  well_formed p1 ->
  all_different (used_wires p1) (addr_wires a) ->
  bits_at_addr (bcexec (seq_inv p1 p2) f) a =
  bits_at_addr (bcexec (p1; p2) f) a.
Proof.
  intros n. induction n as [| n IH]; try reflexivity.
  intros p1 p2 f a Hw Hd. cbn - [ seq_inv ]. apply hd_tl_separately.
  - apply bcexec_seq_inv; try assumption.
    intros Hc. eapply Hd; try apply Hc. apply addr_wires_hd.
  - apply IH; try assumption. rewrite addr_wires_tl. assumption.
Qed.

Definition ctrl0 q p : bccom := seq_inv (bcx q) (bccont q p).

Lemma ctrl0_used :
  forall q p,
  Equal (used_wires (ctrl0 q p)) (add q (used_wires p)).
Proof.
  intros q p. simpl. autorewrite with simpl_wires. reflexivity.
Qed.

Lemma ctrl0_wf :
  forall q p, ~ In q (used_wires p) -> well_formed p -> well_formed (ctrl0 q p).
Proof.
  intros q p Hu Hw.
  apply seq_inv_wf; auto using well_formed.
Qed.

Lemma ctrl0_changed :
  forall q p,
  well_formed (ctrl0 q p) ->
  Equal (changed_wires (ctrl0 q p)) (changed_wires p).
Proof.
  unfold ctrl0. intros q p H. inversion_clear H. inversion_clear H0.
  rewrite seq_inv_changed; try apply ctrl_changed; auto using well_formed.
  simpl. intros i Hx Hc. autorewrite with simpl_wires in Hx. subst.
  rewrite ctrl_changed in Hc; try assumption.
  inversion_clear H2. apply H0. apply changed_wires_used. apply Hc.
Qed.

Lemma bcexec_ctrl0 :
  forall q p f,
  ~ In q (used_wires p) ->
  bcexec (ctrl0 q p) f = if f q then f else bcexec p f.
Proof.
  intros q p f H. simpl.
  destruct (f q) eqn:E; simpl; repeat rewrite update_index_eq.
  - simpl. rewrite <- E. rewrite update_twice_eq.
    apply update_same. reflexivity.
  - apply functional_extensionality. intros i.
    rewrite bcexec_update_unused, update_twice_eq, update_index_eq;
    try assumption.
    destruct (eq_dec q i).
    + subst.
      rewrite update_index_eq, bcexec_unchanged;
      auto using unused_wires_unchanged.
    + rewrite update_index_neq; auto.
Qed.

Inductive wheap w : nat -> Type :=
  | heap_cell (a : addr w) : wheap w 0
  | heap_node {n} (l : wheap w n) (c : addr 2) (r : wheap w n) (e : addr w) :
      wheap w (S n).
Arguments heap_cell {w}.
Arguments heap_node {w n}.

Definition heap n := wheap n n.

Definition wheap_addr {w} (h : wheap w 0) : addr w :=
  match h with
  | heap_cell a => a
  end.

Definition wheap_left {w n} (h : wheap w (S n)) : wheap w n :=
  match h with
  | heap_node l _ _ _ => l
  end.

Definition wheap_ctrl {w n} (h : wheap w (S n)) : addr 2 :=
  match h with
  | heap_node _ c _ _ => c
  end.

Definition wheap_right {w n} (h : wheap w (S n)) : wheap w n :=
  match h with
  | heap_node _ _ r _ => r
  end.

Definition wheap_extra {w n} (h : wheap w (S n)) : addr w :=
  match h with
  | heap_node _ _ _ e => e
  end.

Fixpoint cell_in_wheap {w n} : wheap w n -> Bvector n -> addr w :=
  match n with
  | 0 => fun h _ => wheap_addr h
  | S n' =>
      fun h v =>
      let v' := tl v in
      if hd v
      then cell_in_wheap (wheap_right h) v'
      else cell_in_wheap (wheap_left h) v'
  end.

Fixpoint wheap_size w n :=
  match n with
  | 0 => w
  | S n' => 2 * wheap_size w n' + w + 2
  end.

Definition heap_size n := wheap_size n n.

Lemma wheap_size_simpl :
  forall w n, wheap_size w n = 2 ^ S n * S w - (2 + w).
Proof.
  intros w n. cbn - [ "*" ].
  (*assert (1 <= 2 ^ n) as H2. { induction n; simpl; lia. }
  assert (forall w, w <= w * 2 * 2 ^ n). { intros. nia. }*)
  induction n as [| n IH].
  - simpl. lia.
  - assert (1 <= 2 ^ n) as H2. { clear IH. induction n; simpl; lia. }
    cbn - [ "*" ]. rewrite IH. nia.
Qed.

Fixpoint mk_wheap { w n } : addr (wheap_size w n) -> wheap w n :=
  match n return addr (wheap_size w n) -> wheap w n with
  | 0 => fun a => heap_cell a
  | S n' =>
      fun a =>
      let size := wheap_size w n' in
      heap_node (mk_wheap (addr_index a 0))
                (addr_index a size)
                (mk_wheap (addr_index a (size + 2)))
                (addr_index a (2 * size + 2))
  end.

Definition mk_heap {n} : addr (heap_size n) -> heap n := mk_wheap.

Fixpoint wheap_wires {w n} : wheap w n -> wires :=
  match n with
  | 0 => fun h => addr_wires (wheap_addr h)
  | S n' =>
      fun h =>
      union (union (union (wheap_wires (wheap_left h))
                          (addr_wires (wheap_ctrl h)))
                   (wheap_wires (wheap_right h)))
            (addr_wires (wheap_extra h))
  end.

Fixpoint wheap_cell_wires {w n} (h : wheap w n) : wires :=
  match h with
  | heap_cell a => addr_wires a
  | heap_node l c r e =>
      union (wheap_cell_wires l) (wheap_cell_wires r)
  end.

Lemma cell_in_cell_wires :
  forall w n (h : wheap w n) v,
  Subset (addr_wires (cell_in_wheap h v)) (wheap_cell_wires h).
Proof.
  intros w n h. induction h as [a | n l IHl c r IHr e]; simpl; try reflexivity.
  intros v. destruct (hd v).
  - rewrite IHr, union_sym. apply union_Subset.
  - rewrite IHl. apply union_Subset.
Qed.

Fixpoint wheap_ctrl_wires {w n} (h : wheap w n) : wires :=
  match h with
  | heap_cell a => empty
  | heap_node l c r e =>
      union (union (wheap_ctrl_wires l)
                   (addr_wires c))
            (wheap_ctrl_wires r)
  end.

Lemma ctrl_wires_Subset :
  forall w n (h : wheap w n),
  Subset (wheap_ctrl_wires h) (wheap_wires h).
Proof.
  intros w n h. induction h as [| n l IHl c r IHr e]; auto using empty_Subset.
  intros q. simpl. autorewrite with simpl_wires. rewrite IHl, IHr. tauto.
Qed.

Fixpoint wheap_extra_wires {w n} (h : wheap w n) : wires :=
  match h with
  | heap_cell a => empty
  | heap_node l c r e =>
      union (union (wheap_extra_wires l)
                   (addr_wires e))
            (wheap_extra_wires r)
  end.

Inductive wheap_wf {w} : forall {n}, wheap w n -> Prop :=
  | wheap_wf_cell (a : addr w) : wheap_wf (heap_cell a)
  | wheap_wf_node {n} (l : wheap w n) c r e :
  wheap_wf l -> wheap_wf r ->
  all_different_multi
  (wheap_wires l :: addr_wires c :: wheap_wires r :: addr_wires e :: []) ->
  wheap_wf (heap_node l c r e).

Lemma wheap_wire_groups_different :
  forall w n (h : wheap w n),
  wheap_wf h ->
  all_different_multi
  (wheap_cell_wires h :: wheap_ctrl_wires h :: wheap_extra_wires h :: []).
Proof.
  intros w n h H. induction H as [a | n l IHl c r IHr e]; simpl.
  - constructor.
    + constructor.
      * constructor; constructor.
      * constructor; try constructor. intros q Hq. contradiction.
    + constructor.
      * intros q Hq. contradiction.
      * constructor.
        -- intros q Ha He.
Admitted. (* TODO *)


Inductive wheap_init {w} : (nat -> bool) -> forall {n}, wheap w n -> Prop :=
  | heap_init_addr f a : wheap_init f (heap_cell a)
  | heap_init_node f {n} (l : wheap w n) c r e :
      addr_zero f c -> addr_zero f e -> wheap_init f l -> wheap_init f r -> 
      wheap_init f (heap_node l c r e).

Lemma mk_wheap_wf :
  forall w n (a : addr (wheap_size w n)), wheap_wf (mk_wheap a).
Proof.
  intros w n. induction n as [| n IH].
  - intros. constructor.
Abort. (* TODO *)

Fixpoint read_carve { w n } : wheap w n -> addr n -> bccom :=
  match n with
  | 0 => fun _ _ => bcskip
  | S n' =>
      fun h a =>
      let c := wheap_ctrl h in
      let cl := addr_hd c in
      let cr := addr_hd (addr_tl c) in
      let a0 := addr_hd a in
      let a' := addr_tl a in
      ctrl0 a0 (bcx cl); bccnot a0 cr;
      bccont cl (read_carve (wheap_left h) a');
      bccont cr (read_carve (wheap_right h) a')
  end.

Lemma read_carve_used :
  forall w n (h : wheap w n) (a : addr n),
  Equal (used_wires (read_carve h a))
        (union (wheap_ctrl_wires h) (addr_wires a)).
Proof.
  intros w n.
  induction h as [a' | n l IHl c r IHr]; simpl; intros a i;
  try rewrite IHl; try rewrite IHr; autorewrite with simpl_wires; tauto.
Qed.

Lemma read_carve_wf :
  forall w n (h : wheap w n) (a : addr n),
  wheap_wf h -> all_different (wheap_wires h) (addr_wires a) ->
  well_formed (read_carve h a).
Proof.
  intros w n. induction n as [| n IH]; auto using well_formed.
  intros h a Hw Hd. simpl in *. constructor.
  - constructor.
    + constructor.
      * apply ctrl0_wf; try constructor.
        simpl. autorewrite with simpl_wires. intros Hc.
        eapply Hd with (q := addr_hd a); autorewrite with simpl_wires; auto.
      * apply cnot_wf. intros Hc.
        eapply Hd with (q := addr_hd a); autorewrite with simpl_wires; auto.
    + constructor; try apply IH.
Admitted. (* TODO *)

Lemma read_carve_changed :
  forall w n (h : wheap w n) (a : addr n),
  wheap_wf h ->
  Equal (changed_wires (read_carve h a)) (wheap_ctrl_wires h).
Proof.
  intros w n. induction n as [| n IH]; auto using skip_changed.
  intros h a H. simpl.
Admitted. (* TODO *)

Inductive is_carved {w} (f : nat -> bool) :
  forall {n}, wheap w n -> Bvector n -> Prop :=
  | is_carved_addr (a : addr w) : is_carved f (heap_cell a) []
  | is_carved_node {n} (l : wheap w n) c r e b v :
  f (addr_hd c) <> b -> f (addr_tl c) = b ->
  is_carved f l v -> is_carved f r v ->
  is_carved f (heap_node l c r e) (b :: v).

Lemma bcexec_read_carve :
  forall w n (h : wheap w n) (a : addr n) f,
  is_carved (bcexec (read_carve h a) f) h (bits_at_addr f a).
Proof.
Admitted. (* TODO *)

Fixpoint read_share { w n } : wheap w n -> addr w -> bccom :=
  match n with
  | 0 => fun h out => share (wheap_addr h) out
  | S n' =>
      fun h out =>
      let c := wheap_ctrl h in
      let e := wheap_extra h in
      seq_inv (bccont (addr_hd c) (read_share (wheap_left h) e);
               bccont (addr_hd (addr_tl c)) (read_share (wheap_right h) e))
              (share e out)
  end.

Lemma read_share_used :
  forall w n (h : wheap w n) out,
  Equal (used_wires (read_share h out))
        (union (wheap_wires h) (addr_wires out)).
Proof.
  intros w n h.
  induction h as [a | n l IHl c r IHr e]; simpl; auto using share_used.
  intros out q. repeat rewrite inv_used. rewrite share_used. rewrite IHl, IHr.
  autorewrite with simpl_wires. tauto.
Qed.

Lemma read_share_wf :
  forall w n (h : wheap w n) out,
  wheap_wf h ->
  all_different (wheap_wires h) (addr_wires out) ->
  well_formed (read_share h out).
Proof.
  intros w n h out Hw. generalize dependent out.
  induction Hw as [a | n l c r e Hl IHl Hr IHr Hd]; simpl; auto using share_wf.
  intros out Ho. apply seq_inv_wf.
  - constructor; constructor.
    + rewrite read_share_used. autorewrite with simpl_wires.
      inversion_clear Hd. intros [Hc | Hc].
      * inversion_clear H0. eapply H1; try apply Hc.
        autorewrite with simpl_wires. auto.
      * inversion_clear H. inversion_clear H2. inversion_clear H3.
        eapply H2; try apply Hc. autorewrite with simpl_wires. auto.
    + apply IHl. inversion_clear Hd. inversion_clear H0.
      inversion_clear H2. inversion_clear H3. assumption.
    + rewrite read_share_used. autorewrite with simpl_wires.
      intros [Hc | Hc].
      * inversion_clear Hd. inversion_clear H. inversion_clear H2.
        eapply H; try apply Hc.
        autorewrite with simpl_wires. auto.
      * inversion_clear Hd. inversion_clear H. inversion_clear H2.
        inversion_clear H3. eapply H2; try apply Hc.
        autorewrite with simpl_wires. auto.
    + apply IHr. inversion_clear Hd. inversion_clear H. inversion_clear H1.
      inversion_clear H3. assumption.
  - apply share_wf.
    rewrite union_sym in Ho. rewrite <- union_Subset in Ho. assumption.
Qed.

Lemma read_share_changed :
  forall w n (h : wheap w n) out,
  wheap_wf h ->
  Equal (changed_wires (read_share h out)) (addr_wires out).
Proof.
Admitted. (* TODO *)

Lemma bcexec_read_share :
  forall w n (h : wheap w n) out v f,
  wheap_wf h ->
  is_carved f h v ->
  bits_at_addr (bcexec (read_share h out) f) out =
  bits_at_addr f (cell_in_wheap h v).
Proof.
Admitted.

Definition read { n } (h : heap n) (a : addr n) (out : addr n) : bccom :=
  seq_inv (read_carve h a) (read_share h out).

Lemma read_wf :
  forall n (h : heap n) a out,
  wheap_wf h ->
  all_different_multi (wheap_wires h :: addr_wires a :: addr_wires out :: []) ->
  well_formed (read h a out).
Proof.
Admitted.

Print Assumptions read_wf.

Lemma read_changed :
  forall n (h : heap n) a out,
  wheap_wf h ->
  all_different_multi (wheap_wires h :: addr_wires a :: addr_wires out :: []) ->
  Equal (changed_wires (read h a out)) (addr_wires out).
Proof.
  intros n h a out Hw Hd. unfold read. 
  inversion_clear Hd. inversion_clear H0. inversion_clear H2.
  rewrite seq_inv_changed.
  - apply read_share_changed. assumption.
  - apply read_carve_wf; assumption.
  - apply read_share_wf; assumption.
  - rewrite read_carve_used, read_share_changed; try assumption.
    autorewrite with simpl_wires. split.
    + rewrite ctrl_wires_Subset. assumption.
    + inversion_clear H. inversion_clear H4. assumption.
Qed.

Print Assumptions read_changed.

Lemma bcexec_read :
  forall n (h : heap n) a out f,
  wheap_wf h ->
  all_different_multi (wheap_wires h :: addr_wires a :: addr_wires out :: []) ->
  bits_at_addr (bcexec (read h a out) f) out =
  bits_at_addr f (cell_in_wheap h (bits_at_addr f a)).
Proof.
  intros n h a out f Hw Hd. unfold read. rewrite seq_inv_bits.
  - simpl. erewrite bcexec_read_share; auto using bcexec_read_carve.
    apply bcexec_bits_unchanged. rewrite read_carve_changed; try assumption.
    rewrite cell_in_cell_wires.
    specialize (wheap_wire_groups_different n n h Hw) as Hg.
    inversion_clear Hg. inversion_clear H0. assumption.
  - apply read_carve_wf; try assumption.
    inversion_clear Hd. inversion_clear H0. assumption.
  - rewrite read_carve_used, all_different_union, ctrl_wires_Subset.
    inversion_clear Hd. inversion_clear H. inversion_clear H0.
    inversion_clear H2. inversion_clear H3. auto.
Qed.

Print Assumptions bcexec_read.
