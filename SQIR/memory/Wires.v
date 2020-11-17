Require Import Basics List Setoid Equivalence Morphisms.
Import ListNotations.


Definition wires := nat -> Prop.

Definition In q (ws : wires) : Prop := ws q.

Definition empty : wires := fun _ => False.

Lemma empty_spec :
  forall q, In q empty <-> False.
Proof. 
  unfold empty, In. reflexivity.
Qed.

Definition add q ws : wires := fun i => i = q \/ In i ws.

Lemma add_spec :
  forall ws q i, In i (add q ws) <-> i = q \/ In i ws.
Proof.
  unfold add, In. reflexivity.
Qed.

Hint Rewrite empty_spec add_spec : simpl_wires.

Definition singleton q : wires := add q empty.

Lemma singleton_spec :
  forall q i, In i (singleton q) <-> i = q.
Proof.
  unfold singleton. intros. autorewrite with simpl_wires. tauto.
Qed.

Definition Equal ws ws' : Prop := forall q, In q ws <-> In q ws'.

Lemma add_same :
  forall ws q, Equal (add q (add q ws)) (add q ws).
Proof.
  intros ws q i. autorewrite with simpl_wires. tauto.
Qed.

Lemma add_skip :
  forall ws q q', Equal (add q (add q' (add q ws))) (add q (add q' ws)).
Proof.
  intros ws q q' i. autorewrite with simpl_wires. tauto.
Qed.

Lemma add_add :
  forall ws q q', Equal (add q (add q' ws)) (add q' (add q ws)).
Proof.
  intros ws q q' i. autorewrite with simpl_wires. tauto.
Qed.

Lemma Equal_refl :
  forall ws, Equal ws ws.
Proof.
  intros ws q. reflexivity.
Qed.

Lemma Equal_sym :
  forall ws ws', Equal ws ws' -> Equal ws' ws.
Proof.
  unfold Equal. intros ws ws' H w. rewrite H. reflexivity.
Qed.

Lemma Equal_trans :
  forall ws ws' ws'',
  Equal ws ws' -> Equal ws' ws'' -> Equal ws ws''.
Proof.
  unfold Equal. intros ws ws' ws'' H H' w. rewrite H, H'. reflexivity.
Qed.

Instance Equal_Equivalence : Equivalence Equal.
Proof.
  split; eauto using Equal_refl, Equal_sym, Equal_trans.
Qed.

Instance In_Equal_Proper q :
  Proper (Equal ==> iff) (In q).
Proof.
  intros ws ws' H. auto.
Qed.

Instance add_Proper q :
  Proper (Equal ==> Equal) (add q).
Proof.
  intros ws ws' H i. unfold Equal in H.
  split; intros []; subst; autorewrite with simpl_wires; auto;
  right; apply H; assumption.
Qed.

Definition Subset (ws ws' : wires) :=
  forall q, In q ws -> In q ws'.

Lemma empty_Subset :
  forall (ws : wires), Subset empty ws.
Proof.
  intros. unfold Subset. contradiction.
Qed.

Lemma add_Subset :
  forall ws q, Subset ws (add q ws).
Proof.
  intros ws q i H. autorewrite with simpl_wires. tauto.
Qed.

Lemma Subset_refl :
  forall ws, Subset ws ws.
Proof.
  unfold Subset. auto.
Qed.

Instance Subset_Reflective : Reflexive Subset := Subset_refl.

Instance Subset_Subset_Proper :
  Proper (Subset ==> Equal ==> flip impl) Subset.
Proof.
  intros ws ws' H ws1 ws2 H2 Hs q Hi. apply H2. apply Hs. apply H. assumption.
Qed.

Instance Subset_Equal_Proper :
  Proper (Equal ==> Equal ==> flip impl) Subset.
Proof.
  intros ws ws' H ws1 ws2 H2 Hs q Hi. apply H2. apply Hs. apply H. assumption.
Qed.

Lemma Subset_trans :
  forall ws ws' ws'',
  Subset ws ws' -> Subset ws' ws'' -> Subset ws ws''.
Proof.
  unfold Subset. auto.
Qed.

Instance In_Subset_Proper q :
  Proper (Subset ==> impl) (In q).
Proof.
  intros ws ws' H Hi. auto. 
Qed.

Lemma Equal_Subset :
  forall ws ws',
  Equal ws ws' <-> Subset ws ws' /\ Subset ws' ws.
Proof.
  split.
  - intros H. split; intros w; apply H.
  - intros [] q. split; auto.
Qed.

Definition union (ws ws' : wires) : wires :=
  fun q => In q ws \/ In q ws'.

Lemma union_spec :
  forall ws ws' q, In q (union ws ws') <-> In q ws \/ In q ws'.
Proof.
  unfold union, In. reflexivity.
Qed.

Hint Rewrite singleton_spec union_spec add_same add_skip : simpl_wires.

Lemma union_sym :
  forall ws ws',
  Equal (union ws ws') (union ws' ws).
Proof.
  intros ws ws' q. autorewrite with simpl_wires. tauto.
Qed.

Lemma union_empty :
  forall ws, Equal (union empty ws) ws.
Proof.
  intros ws q. autorewrite with simpl_wires. tauto.
Qed.

Lemma union_self :
  forall ws, Equal (union ws ws) ws.
Proof.
  intros ws q. autorewrite with simpl_wires. tauto.
Qed.

Lemma union_assoc :
  forall ws ws' ws'',
  Equal (union (union ws ws') ws'') (union ws (union ws' ws'')).
Proof.
  intros ws ws' ws'' q. autorewrite with simpl_wires. tauto.
Qed.

Lemma union_Subset :
  forall ws ws', Subset ws (union ws ws').
Proof.
  intros ws ws' q. autorewrite with simpl_wires. auto.
Qed.

Lemma union_add :
  forall q ws ws', Equal (union (add q ws) ws') (add q (union ws ws')).
Proof.
  intros q ws ws' i. autorewrite with simpl_wires. tauto.
Qed.

Lemma union_add_2 :
  forall ws ws' q, Equal (union ws (add q ws')) (add q (union ws ws')).
Proof.
  intros ws ws' q i. autorewrite with simpl_wires. tauto.
Qed.

Lemma union_singleton :
  forall q ws,
  Equal (union (singleton q) ws) (add q ws).
Proof.
  intros q ws i. autorewrite with simpl_wires. reflexivity.
Qed.

Lemma union_singleton_2 :
  forall q ws,
  Equal (union ws (singleton q)) (add q ws).
Proof.
  intros q ws i. autorewrite with simpl_wires. tauto.
Qed.

Instance union_Proper :
  Proper (Equal ==> Equal ==> Equal) union.
Proof.
  intros ws ws' H is is' He q.
  split; intros Hu; autorewrite with simpl_wires in *.
  - rewrite <- H, <- He. apply Hu.
  - rewrite H, He. assumption.
Qed.

Instance union_Subset_Proper :
  Proper (Subset ==> Subset ==> Subset) union.
Proof.
  intros ws ws' H ws1 ws2 Hs q Hi. autorewrite with simpl_wires in *.
  rewrite <- H, <- Hs. assumption.
Qed.

Definition all_different (ws ws' : wires) : Prop :=
  forall q, In q ws -> In q ws' -> False.

Lemma all_different_sym :
  forall ws ws', all_different ws ws' -> all_different ws' ws.
Proof.
  intros ws ws' H q. eauto.
Qed.

Instance all_different_Symmetric : Symmetric all_different := all_different_sym.

Instance all_different_Proper :
  Proper (Subset ==> Subset ==> flip impl) all_different.
Proof.
  intros ws ws' H ws1 ws2 H2 Hd q Hi H1. eauto.
Qed.

Instance all_different_Equal_Proper :
  Proper (Equal ==> Equal ==> flip impl) all_different.
Proof.
  intros ws ws' H ws1 ws2 H2 Hd q Hi H1. eapply Hd.
  - apply H, Hi.
  - apply H2, H1.
Qed.

Instance all_different_iff_Proper :
  Proper (Equal ==> Equal ==> iff) all_different.
Proof.
  intros ws ws' H ws1 ws2 H2. split; rewrite H, H2; auto.
Qed.

Lemma all_different_singleton :
  forall ws q, all_different (singleton q) ws <-> ~ In q ws.
Proof.
  intros ws q. split.
  - intros H Hc. eapply H; try apply Hc.
    autorewrite with simpl_wires. reflexivity.
  - intros H i Hq Hw. autorewrite with simpl_wires in Hq. subst. congruence.
Qed.

Lemma all_different_singleton_2 :
  forall ws q, all_different ws (singleton q) <-> ~ In q ws.
Proof.
  intros ws q. split; intros H.
  - apply all_different_singleton, all_different_sym. assumption.
  - apply all_different_sym, all_different_singleton. assumption.
Qed.

Lemma all_different_union :
  forall ws ws' ws'',
  all_different (union ws ws') ws'' <->
  all_different ws ws'' /\ all_different ws' ws''.
Proof.
  intros ws ws' ws''. split.
  - intros H. split.
    + intros q Hw H'. eapply H; try apply H'.
      autorewrite with simpl_wires. auto.
    + intros q Hw H'. eapply H; try apply H'.
      autorewrite with simpl_wires. auto.
  - intros [H H'] q Hu Hq. autorewrite with simpl_wires in Hu.
    destruct Hu as [Hu | Hu]; eauto.
Qed.

Lemma all_different_union_2 :
  forall ws ws' ws'',
  all_different ws (union ws' ws'') <->
  all_different ws ws' /\ all_different ws ws''.
Proof.
  intros ws ws' ws''. split; intros H.
  - apply all_different_sym, all_different_union in H.
    split; apply all_different_sym; apply H.
  - apply all_different_sym, all_different_union.
    split; apply all_different_sym; apply H.
Qed.

Lemma all_different_add :
  forall ws ws' q,
  all_different (add q ws) ws' <-> ~ In q ws' /\ all_different ws ws'.
Proof.
  intros ws ws' q.
  rewrite <- union_singleton, all_different_union, all_different_singleton. 
  reflexivity.
Qed.

Lemma all_different_add_2 :
  forall ws ws' q,
  all_different ws (add q ws') <-> ~ In q ws /\ all_different ws ws'.
Proof.
  intros ws ws' q.
  rewrite <- union_singleton_2, all_different_union_2,
      all_different_singleton_2.
  tauto.
Qed.

Hint Rewrite union_empty union_self
  union_add union_add_2 union_singleton union_singleton_2
  all_different_singleton all_different_singleton_2
  all_different_union all_different_union_2
  all_different_add all_different_add_2 :
  simpl_wires.
Hint Rewrite <- union_assoc : simpl_wires.

Inductive all_different_multi : list wires -> Prop :=
  | all_different_multi_nil : all_different_multi []
  | all_different_multi_cons ws l :
      all_different_multi l -> Forall (all_different ws) l ->
      all_different_multi (ws :: l).

