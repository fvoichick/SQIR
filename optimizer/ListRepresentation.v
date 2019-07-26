Require Import Setoid.
(* Require Import Equivalences. *)
Require Import UnitarySem.
Require Import Tactics.
Require Import Coq.Reals.ROrderedType.
Require Import Phase.
Require Export List.

Local Open Scope ucom_scope.


(* This file contains utilities for manipulating (unitary) SQIRE programs 
   to make implementing transformations easier. The primary contribution is 
   a 'list of gates' representation.

   TODO: We've been thinking for a while about adding a DAG representation of 
   circuits. This would be useful for implementing optimizations because the
   dependence between gates would be obvious (and existing optimizers like Qiskit
   and the Nam et al. optimizer use a DAG representation). However, we have put
   this off for several reasons:
      - Reasoning about the semantics of graphs will be complicated by the need
        to topologically sort the graph to find the order of instructions.
      - A Coq-based representation of graphs (as sets of nodes and edges) will
        probably not be nice to export to OCaml.
   If we decide to return to this in the future, we should look to existing
   verified compilers (e.g. CompCert) to see how they use graphs.
*)


(***************************)
(**       Gate set        **)
(***************************)
(* In this file, we'll be using a slightly different "fixed" set of unitaries.
   Instead of an arbitrary rotation R_ parameterized by a real, we will use a
   k * PI / 4 rotation for natural number k. We will also exclude Z, which 
   corresponds to PI4 k with k = 4.
 *)

Inductive fUnitary : nat -> Set := 
  | fU_H           : fUnitary 1 
  | fU_X           : fUnitary 1
  | fU_PI4 (k : Z) : fUnitary 1
  | fU_CNOT        : fUnitary 2.

Definition fUnitary_to_Unitary  {n} (u : fUnitary n) : Unitary n :=
  match u with
  | fU_H     => U_H
  | fU_X     => U_X
(*  | fU_PI4 k => if (beq_nat k 4) then U_Z else U_R (INR k * PI / 4)%R *)
  | fU_PI4 k =>  U_R (IZR k * PI / 4)%R (* simpler version *)
  | fU_CNOT  => U_CNOT
  end.

Definition Unitary_to_fUnitary  {n} (u : Unitary n) : option (fUnitary n) :=
  match u with
  | U_H    => Some fU_H
  | U_X    => Some fU_X
  | U_Y    => None
  | U_Z    => Some (fU_PI4 4)
  | U_R θ  => if Reqb θ (0 * PI / 4) then Some (fU_PI4 0) else
             if Reqb θ (1 * PI / 4) then Some (fU_PI4 1) else
             if Reqb θ (2 * PI / 4) then Some (fU_PI4 2) else
             if Reqb θ (3 * PI / 4) then Some (fU_PI4 3) else
             if Reqb θ (4 * PI / 4) then Some (fU_PI4 4) else (* can leave out *)
             if Reqb θ (5 * PI / 4) then Some (fU_PI4 5) else
             if Reqb θ (6 * PI / 4) then Some (fU_PI4 6) else
             if Reqb θ (7 * PI / 4) then Some (fU_PI4 7) else
               None
  | U_CNOT => Some fU_CNOT
  end.

(* Rotation shorthands (not used in this file) *)
Definition fU_T : fUnitary 1 := fU_PI4 1.
Definition fU_P : fUnitary 1 := fU_PI4 2.
Definition fU_Z : fUnitary 1 := fU_PI4 4.
Definition fU_PDAG : fUnitary 1 := fU_PI4 6.
Definition fU_TDAG : fUnitary 1 := fU_PI4 7.

(* Only true if we special case on Z:
Lemma unitary_conversion_sound : forall {n} (u : Unitary n) u',
  Unitary_to_fUnitary u = Some u' ->
  fUnitary_to_Unitary u'= u.
Proof.
  intros.
  dependent destruction u; inversion H; simpl; trivial.
  clear H.
  repeat match goal with 
  | [ H : (if ?b then _ else _) = _ |- _] => let E := fresh "E" in destruct b eqn:E
  | [ E : Reqb _ _ = true |- _]           => apply Reqb_eq in E; subst
  | [ H : Some _ = Some _ |- _]           => inversion H; subst
  | [ H : None = Some _ |- _]             => inversion H
  end; simpl; apply f_equal; lra.
Qed.
*)

(* Semantic version: *)
Lemma unitary_conversion_sound' : forall (u : Unitary 1) u' dim n,
  Unitary_to_fUnitary u = Some u' ->
  ueval1 dim n (fUnitary_to_Unitary u') = ueval1 dim n u.
Proof.
  intros.
  dependent destruction u; inversion H; simpl; trivial.
  - unfold ueval1, ueval_unitary1, pad.
    repad.
    rewrite <- phase_pi.
    replace (4 * PI / 4)%R with PI by lra.
    reflexivity.
  - clear H.
    repeat match goal with 
    | [ H : (if ?b then _ else _) = _ |- _] => let E := fresh "E" in destruct b eqn:E
    | [ E : Reqb _ _ = true |- _]           => apply Reqb_eq in E; subst
    | [ H : Some _ = Some _ |- _]           => inversion H; subst
    | [ H : None = Some _ |- _]             => inversion H
    end; simpl; do 2 apply f_equal; lra.
Qed.
  
Definition match_gate {n} (U U' : fUnitary n) : bool :=
  match U, U' with
  | fU_H, fU_H | fU_X, fU_X | fU_CNOT, fU_CNOT => true
  | fU_PI4 k, fU_PI4 k' => Z.eqb k k'
  | _, _ => false
  end.

Lemma match_gate_refl : forall {n} (U U' : fUnitary n), match_gate U U' = true <-> U = U'. 
Proof.
  intros.
  split; intros.
  - dependent destruction U; dependent destruction U';
    inversion H; try reflexivity.
    apply Z.eqb_eq in H1. subst. reflexivity.    
  - subst. dependent destruction U'; trivial. 
    simpl. apply Z.eqb_refl.
Qed.


(**************************)
(** List representation  **)
(**************************)
(* Represent a unitary circuit as a list of gate applications.*)

Inductive gate_app (dim : nat): Set :=
| App1 : fUnitary 1 -> nat -> gate_app dim
| App2 : fUnitary 2 -> nat -> nat -> gate_app dim.

Arguments App1 {dim}.
Arguments App2 {dim}.

(* Some shorthands *)
Definition _H {dim} n : gate_app dim := App1 fU_H n.
Definition _X {dim} n : gate_app dim := App1 fU_X n.
Definition _PI4 {dim} k n : gate_app dim := App1 (fU_PI4 k) n.
Definition _CNOT {dim} m n : gate_app dim := App2 fU_CNOT m n.

(* Shorthands for common rotation gates *)
Definition _I {dim} n : gate_app dim := App1 (fU_PI4 0) n.
Definition _T {dim} n : gate_app dim := App1 (fU_PI4 1) n.
Definition _P {dim} n : gate_app dim := App1 (fU_PI4 2) n.
Definition _Z {dim} n : gate_app dim := App1 (fU_PI4 4) n.
Definition _PDAG {dim} n : gate_app dim := App1 (fU_PI4 6) n.
Definition _TDAG {dim} n : gate_app dim := App1 (fU_PI4 7) n.

Definition gate_list dim := list (gate_app dim).

Fixpoint ucom_to_list {dim} (c: ucom dim) : option (gate_list dim) :=
  match c with
  | c1; c2 => match ucom_to_list c1, ucom_to_list c2 with
             | Some l1, Some l2 => Some (l1 ++ l2)
             | _, _ => None
             end
  | uapp1 u n => match (Unitary_to_fUnitary u) with
                | Some u => Some [App1 u n]
                | _ => None
                end
  | uapp2 u m n => match (Unitary_to_fUnitary u) with
                  | Some u => Some [App2 u m n]
                  | _ => None
                  end
  | uskip => Some []
  end.

Fixpoint list_to_ucom {dim} (l : gate_list dim) : ucom dim :=
  match l with
  | [] => uskip
  | (App1 u n)::t => (uapp1 (fUnitary_to_Unitary u) n) ; (list_to_ucom t)
  | (App2 u m n)::t => (uapp2 (fUnitary_to_Unitary u) m n) ; (list_to_ucom t)
  end.

Lemma list_to_ucom_append : forall {dim} (l1 l2 : gate_list dim),
  list_to_ucom (l1 ++ l2) ≡ list_to_ucom l1 ; list_to_ucom l2.
Proof.
  intros dim l1 l2.
  unfold uc_equiv.
  induction l1; simpl.
  - Msimpl. reflexivity.
  - destruct a; simpl;
    rewrite IHl1; simpl;
    rewrite Mmult_assoc;
    reflexivity.
Qed.

Lemma ucom_list_equiv : forall {dim} (c : ucom dim) l,
  ucom_to_list c = Some l ->
  c ≡ list_to_ucom l.
Proof.
  intros.
  unfold uc_equiv.
  generalize dependent l.
  induction c; intros l H.
  - inversion H; subst. reflexivity.
  - simpl in H. 
    destruct (ucom_to_list c1); destruct (ucom_to_list c2); inversion H; subst. 
    simpl.
    rewrite list_to_ucom_append; simpl.
    rewrite (IHc1 g), (IHc2 g0); reflexivity.
  - simpl in H. 
    remember (Unitary_to_fUnitary u) as eqU.
    destruct eqU.
    inversion H; subst. simpl.
    Msimpl. symmetry.
    apply unitary_conversion_sound'.
    auto.
    discriminate.
  - simpl in H. 
    remember (Unitary_to_fUnitary u) as eqU.
    destruct eqU.
    inversion H; subst. simpl.
    Msimpl. reflexivity.
    discriminate.
Qed.

(* Well-typedness for lists *)
Local Close Scope R_scope.
Inductive uc_well_typed_l {dim} : gate_list dim -> Prop :=
| WT_nil : uc_well_typed_l []
| WT_app1 : forall u n t, n < dim -> uc_well_typed_l t 
            -> uc_well_typed_l ((App1 u n) :: t)
| WT_app2 : forall u m n t, m < dim -> n < dim -> m <> n -> uc_well_typed_l t 
            ->  uc_well_typed_l ((App2 u m n) :: t).

Lemma list_to_ucom_WT : forall {dim} (l : gate_list dim), 
  uc_well_typed_l l <-> uc_well_typed (list_to_ucom l).
Proof.
  intros. 
  split; intros. 
  - induction H.
    + constructor.
    + constructor.
      constructor; assumption.
      apply IHuc_well_typed_l.
    + constructor.
      constructor; assumption.
      apply IHuc_well_typed_l.
  - induction l.
    + constructor.
    + destruct a; dependent destruction f;
      inversion H; subst;
      inversion H2; subst;
      constructor;
      try apply IHl;
      assumption.
Qed.

Lemma uc_well_typed_l_app : forall {dim} (l1 l2 : gate_list dim),
  uc_well_typed_l l1 -> uc_well_typed_l l2 -> uc_well_typed_l (l1 ++ l2).
Proof.
  intros. induction H; simpl; try constructor; assumption.
Qed.

Lemma ucom_to_list_WT : forall {dim} (c : ucom dim) l,
  ucom_to_list c = Some l -> uc_well_typed c -> uc_well_typed_l l.
Proof.
  intros.
  generalize dependent l.
  induction H0; intros.
  - inversion H; subst. constructor.
  - simpl in H.
    destruct (ucom_to_list c1); 
    destruct (ucom_to_list c2);
    inversion H; subst.
    apply uc_well_typed_l_app.
    apply IHuc_well_typed1; reflexivity.
    apply IHuc_well_typed2; reflexivity.
  - simpl in H0. destruct (Unitary_to_fUnitary u); inversion H0; subst. 
    constructor; try constructor; assumption.
  - simpl in H2. destruct (Unitary_to_fUnitary u); inversion H2; subst. 
    constructor; try constructor; assumption.
Qed. 

(** Equivalences that allow us to do rewriting. **)

Definition uc_equiv_l {dim} (l1 l2 : gate_list dim) := 
  (list_to_ucom l1) ≡ (list_to_ucom l2).
Infix "=l=" := uc_equiv_l (at level 70).

Lemma uc_equiv_l_refl : forall {dim} (l1 : gate_list dim), l1 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_sym : forall {dim} (l1 l2 : gate_list dim), l1 =l= l2 -> l2 =l= l1.
Proof. easy. Qed.
 
Lemma uc_equiv_l_trans : forall {dim} (l1 l2 l3 : gate_list dim), 
  l1 =l= l2 -> l2 =l= l3 -> l1 =l= l3.
Proof. intros dim l1 l2 l3 H12 H23. unfold uc_equiv_l in *. rewrite H12. easy. Qed.

Lemma uc_eval_l_cons_app1 : forall {dim} (u : fUnitary 1) (n : nat) (t : gate_list dim),
  uc_eval (list_to_ucom ((App1 u n)::t)) = uc_eval (list_to_ucom t) × ueval1 dim n (fUnitary_to_Unitary u).
Proof. easy. Qed.

Lemma uc_eval_l_cons_app2 : forall {dim} (u : fUnitary 2) (m n : nat) (t : gate_list dim),
  uc_eval (list_to_ucom ((App2 u m n)::t)) = uc_eval (list_to_ucom t) × ueval_cnot dim m n.
Proof. easy. Qed.

Lemma uc_eval_l_app : forall {dim} (l1 l2 : gate_list dim),
  uc_eval (list_to_ucom (l1 ++ l2)) = uc_eval (list_to_ucom l2) × uc_eval (list_to_ucom l1).
Proof.
  intros.
  induction l1.
  - simpl. Msimpl. reflexivity.
  - simpl. 
    destruct a; simpl; rewrite IHl1; rewrite Mmult_assoc; reflexivity.
Qed.

Lemma cons_congruence : forall {dim} (g : gate_app dim)  (l l' : gate_list dim),
  l =l= l' ->
  g :: l =l= g :: l'.
Proof.
  intros dim g l l' Hl.
  unfold uc_equiv_l, uc_equiv.
  destruct g.
  - repeat rewrite uc_eval_l_cons_app1.
    rewrite Hl.
    reflexivity.
  - repeat rewrite uc_eval_l_cons_app2.
    rewrite Hl.
    reflexivity.
Qed.

Lemma app_congruence : forall {dim} (l1 l1' l2 l2' : gate_list dim),
  l1 =l= l1' ->
  l2 =l= l2' ->
  l1 ++ l2 =l= l1' ++ l2'.
Proof.
  intros dim l1 l1' l2 l2' Hl1 Hl2.
  unfold uc_equiv_l, uc_equiv.
  repeat rewrite uc_eval_l_app.
  rewrite Hl1, Hl2.
  reflexivity.
Qed.

Add Parametric Relation (dim : nat) : (gate_list dim) (@uc_equiv_l dim)
  reflexivity proved by uc_equiv_l_refl
  symmetry proved by uc_equiv_l_sym
  transitivity proved by uc_equiv_l_trans
  as uc_equiv_l_rel.

Add Parametric Morphism (dim : nat) : (@cons (gate_app dim))
  with signature eq ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as cons_mor.
Proof. intros y x0 y0 H0. apply cons_congruence; easy. Qed.

Add Parametric Morphism (dim : nat) : (@app (gate_app dim))
  with signature (@uc_equiv_l dim) ==> (@uc_equiv_l dim) ==> (@uc_equiv_l dim) as app_mor.
Proof. intros x y H x0 y0 H0. apply app_congruence; easy. Qed.

(** Useful relationship between equivalence and well-typedness **)

Lemma uc_equiv_l_implies_WT : forall {dim} (l l' : gate_list dim),
  l =l= l' ->
  uc_well_typed_l l ->
  uc_well_typed_l l'.
Proof.
  intros.
  apply list_to_ucom_WT; apply uc_eval_nonzero_iff.
  apply list_to_ucom_WT in H0; apply uc_eval_nonzero_iff in H0.
  rewrite <- H; assumption.
Qed.
  

(** Useful operations on the list representation. **)

(* Get the next single-qubit gate applied to qubit q.
   
   Returns None if there is no next gate on qubit q or the next gate is
   not a single-qubit gate. Otherwise, it returns Some (g, l') where g is 
   the application of the gate and l' is the program with that application
   removed.
*)
Fixpoint next_single_qubit_gate {dim} (l : gate_list dim) (q : nat) 
             : option (fUnitary 1 * gate_list dim) :=
  match l with
  | [] => None
  | (App1 u n) :: t => if n =? q
                     then Some (u, t) 
                     else match (next_single_qubit_gate t q) with
                          | None => None
                          | Some (u', l') => Some (u', (App1 u n) :: l')
                          end
  | (App2 u m n) :: t => if (m =? q) || (n =? q)
                       then None 
                       else match (next_single_qubit_gate t q) with
                            | None => None
                            | Some (u', l') => Some (u', (App2 u m n) :: l')
                            end
  end.

(* Commutativity lemmas for list representation. *)
Lemma U_V_comm_l : forall {dim} (u1 : fUnitary 1) (u2 : fUnitary 1) q1 q2 (l : gate_list dim),
  q1 <> q2 ->
  (App1 u1 q1)::(App1 u2 q2)::l =l= (App1 u2 q2)::(App1 u1 q1)::l.
Proof.
  intros.
  unfold uc_equiv_l.
  simpl list_to_ucom.
  rewrite <- useq_assoc. 
  rewrite (U_V_comm _ _ _ _ H).
  rewrite <- useq_assoc. 
  reflexivity.
Qed.

Lemma U_CNOT_comm_l : forall {dim} (u1 : fUnitary 1) (u2 : fUnitary 2) q1 q2 q3 (l : gate_list dim),
  q1 <> q2 -> q1 <> q3 ->
  (App1 u1 q1)::(App2 u2 q2 q3)::l =l= (App2 u2 q2 q3)::(App1 u1 q1)::l.
Proof.
  intros.
  unfold uc_equiv_l.
  simpl list_to_ucom.
  dependent destruction u2.
  rewrite <- useq_assoc.
  specialize (@U_CNOT_comm dim q1 q2 q3 (fUnitary_to_Unitary u1) H H0) as Hcomm.
  rewrite Hcomm.
  rewrite <- useq_assoc. 
  reflexivity.
Qed.        

Lemma nsqg_preserves_semantics : forall {dim} (l : gate_list dim) q u l',
  next_single_qubit_gate l q = Some (u, l') -> l =l= App1 u q :: l'.
Proof.
  intros.
  generalize dependent l'.
  induction l; try easy.
  intros l' H.
  simpl in H.
  destruct a.
  - bdestruct (n =? q).
    + inversion H; subst. reflexivity.
    + destruct (next_single_qubit_gate l q); try easy; destruct p.
      inversion H; subst.
      rewrite IHl with (l':=g); try reflexivity.
      apply U_V_comm_l; assumption.      
  - bdestruct (n =? q); bdestruct (n0 =? q); simpl in H; try easy.
    destruct (next_single_qubit_gate l q); try easy; destruct p.
    inversion H; subst.
    rewrite IHl with (l':=g); try reflexivity.
    rewrite U_CNOT_comm_l; try lia. 
    reflexivity.  
Qed.

Lemma nsqg_WT : forall {dim} (l : gate_list dim) q u l',
  next_single_qubit_gate l q = Some (u, l') -> uc_well_typed_l l -> uc_well_typed_l l'.
Proof.
  intros dim l q u l' H WT.
  generalize dependent l'.
  induction l; try easy.
  intros l' H.
  simpl in H.
  destruct a; inversion WT; subst.
  - bdestruct (n =? q).
    + inversion H; subst. assumption.
    + destruct (next_single_qubit_gate l q); try easy; destruct p.
      inversion H; subst.
      constructor; try assumption.
      apply IHl; try assumption; reflexivity.   
  - bdestruct (n =? q); bdestruct (n0 =? q); simpl in H; try easy.
    destruct (next_single_qubit_gate l q); try easy; destruct p.
    inversion H; subst.
    constructor; try assumption.
    apply IHl; try assumption; reflexivity. 
Qed.

(* Get the next two-qubit gate applied to qubit q.
   
   Returns None if there is no next gate on qubit q or the next gate is
   not a two-qubit gate. Otherwise, it returns Some (l1, g, l2) where g is 
   the application of the gate, l1 is the portion of the program before g, 
   and l2 is the portion of the program after g.
*)
Fixpoint next_two_qubit_gate {dim} (l : gate_list dim) (q : nat) 
             : option (gate_list dim * nat * nat * gate_list dim) :=
  match l with
  | [] => None
  | (App1 u n) :: t => if n =? q
                     then None
                     else match (next_two_qubit_gate t q) with
                          | None => None
                          | Some (l1, m', n', l2) => Some ((App1 u n) :: l1, m', n', l2)
                          end
  | (App2 u m n) :: t => if (m =? q) || (n =? q)
                       then Some ([], m, n, t) 
                       else match (next_two_qubit_gate t q) with
                            | None => None
                            | Some (l1, m', n', l2) => Some ((App2 u m n) :: l1, m', n', l2)
                            end
  end.

Lemma ntqg_returns_two_qubit_gate : forall {dim} (l : gate_list dim) q l1 m n l2,
  next_two_qubit_gate l q = Some (l1, m, n, l2) -> 
  (q = m \/ q = n).
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a.
  - bdestruct (n0 =? q); try easy.
    destruct (next_two_qubit_gate l q); try easy; destruct p; destruct p; destruct p.
    inversion H; subst.
    apply IHl with (l1:=g0); reflexivity.
  - bdestruct (n0 =? q).
    + simpl in H; inversion H; subst.
      left; reflexivity.
    + bdestruct (n1 =? q); simpl in H.
      * inversion H; subst.
        right; reflexivity.
      * destruct (next_two_qubit_gate l q); try easy; destruct p; destruct p; destruct p.
        inversion H; subst.
        apply IHl with (l1:=g0); reflexivity.
Qed.

Lemma ntqg_preserves_semantics : forall {dim} (l : gate_list dim) q l1 m n l2,
  next_two_qubit_gate l q = Some (l1, m, n, l2) -> l =l= l1 ++ [App2 fU_CNOT m n] ++ l2.
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a.
  - destruct (n0 =? q); try easy.
    destruct (next_two_qubit_gate l q); try easy.
    destruct p; destruct p; destruct p; inversion H; subst.
    rewrite IHl with (l1:=g0); reflexivity.
  - destruct ((n0 =? q) || (n1 =? q)).
    + inversion H; subst. reflexivity.
    + destruct (next_two_qubit_gate l q); try easy.
      destruct p; destruct p; destruct p; inversion H; subst.
      rewrite IHl with (l1:=g0); reflexivity.
Qed.

Lemma ntqg_WT : forall {dim} (l : gate_list dim) q l1 m n l2,
  next_two_qubit_gate l q = Some (l1, m, n, l2) -> 
  uc_well_typed_l l -> uc_well_typed_l l1 /\ uc_well_typed_l l2.
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a; inversion H0; subst.
  - destruct (n0 =? q); try easy.
    destruct (next_two_qubit_gate l q); try easy.
    destruct p; destruct p; destruct p; inversion H; subst.
    specialize (IHl H5 g0) as [Hl1 Hl2]; try reflexivity.
    split; try constructor; assumption.
  - destruct ((n0 =? q) || (n1 =? q)).
    + inversion H; subst. split; try constructor; assumption.
    + destruct (next_two_qubit_gate l q); try easy.
      destruct p; destruct p; destruct p; inversion H; subst.
      specialize (IHl H8 g0) as [Hl1 Hl2]; try reflexivity.
      split; try constructor; assumption.
Qed.

Fixpoint does_not_reference {dim} (l : gate_list dim) (q : nat) :=
  match l with
  | [] => true
  | (App1 u n) :: t => (negb (n =? q)) && (does_not_reference t q)
  | (App2 u m n) :: t => negb ((m =? q) || (n =? q)) && (does_not_reference t q)
  end.

Lemma ntqg_l1_does_not_reference : forall {dim} (l : gate_list dim) q l1 m n l2,
  next_two_qubit_gate l q = Some (l1, m, n, l2) ->
  does_not_reference l1 q = true.
Proof.
  intros.
  generalize dependent l1.
  induction l; try easy.
  intros l1 H.
  simpl in H.
  destruct a.
  - bdestruct (n0 =? q); try easy.
    destruct (next_two_qubit_gate l q); try easy.
    destruct p; destruct p; destruct p; inversion H; subst.
    simpl.
    rewrite IHl with (l1:=g0); try reflexivity.
    apply andb_true_intro.
    split; trivial.
    apply negb_true_iff.
    apply eqb_neq; assumption.
  - bdestruct (n0 =? q); bdestruct (n1 =? q); 
    simpl in H; inversion H; subst; try reflexivity.
    destruct (next_two_qubit_gate l q); try easy.
    destruct p; destruct p; destruct p; inversion H; subst.
    simpl.
    rewrite IHl with (l1:=g0); try reflexivity.
    apply andb_true_intro.
    split; trivial.
    apply negb_true_iff.
    apply orb_false_intro; apply eqb_neq; assumption.
Qed.

Lemma does_not_reference_commutes_app1 : forall {dim} (l : gate_list dim) u q,
  does_not_reference l q = true ->
  [App1 u q] ++ l =l= l ++ [App1 u q]. 
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl in *.
    destruct a. 
    + apply andb_prop in H as [H1 H2].
      rewrite <- IHl; try assumption.
      apply negb_true_iff in H1.
      apply beq_nat_false in H1.
      apply U_V_comm_l; lia.
    + apply andb_prop in H as [H1 H2].
      rewrite <- IHl; try assumption.
      apply negb_true_iff in H1.
      apply orb_false_elim in H1 as [Hn Hn0].
      apply beq_nat_false in Hn.
      apply beq_nat_false in Hn0.
      apply U_CNOT_comm_l; lia. 
Qed.

Lemma does_not_reference_commutes_app2 : forall {dim} (l : gate_list dim) u m n,
  does_not_reference l m = true ->
  does_not_reference l n = true ->
  [App2 u m n] ++ l =l= l ++ [App2 u m n]. 
Proof.
  intros.
  induction l.
  - reflexivity.
  - simpl in *.
    destruct a. 
    + apply andb_prop in H as [H1 H2].
      apply andb_prop in H0 as [H3 H4].
      rewrite <- IHl; try assumption.
      apply negb_true_iff in H1. 
      apply negb_true_iff in H3.
      apply beq_nat_false in H1.
      apply beq_nat_false in H3.
      rewrite U_CNOT_comm_l; try reflexivity; lia.
    + apply andb_prop in H as [H1 H2].
      apply andb_prop in H0 as [H3 H4].
      rewrite <- IHl; try assumption.
      apply negb_true_iff in H1.
      apply negb_true_iff in H3.
      apply orb_false_elim in H1 as [H5 H6].
      apply orb_false_elim in H3 as [H7 H8].
      apply beq_nat_false in H5.
      apply beq_nat_false in H6.
      apply beq_nat_false in H7.
      apply beq_nat_false in H8.
      specialize (@CNOT_CNOT_comm dim m n n0 n1 H5 H7 H6 H8) as Hcomm.
      unfold uc_equiv_l; simpl list_to_ucom. 
      rewrite <- useq_assoc.
      dependent destruction u; dependent destruction f.
      rewrite Hcomm.
      rewrite useq_assoc.
      reflexivity.
Qed.

(* Count the gates in a program. *)
Local Close Scope C_scope.
Fixpoint count_H_gates {dim} (l : gate_list dim) :=
  let fix aux l acc :=
    match l with
    | [] => acc
    | (App1 fU_H _) :: t => aux t (acc + 1)
    | _ :: t => aux t acc
    end in
  aux l 0.

Fixpoint count_X_gates {dim} (l : gate_list dim) :=
  let fix aux l acc :=
    match l with
    | [] => acc
    | (App1 fU_X _) :: t => aux t (acc + 1)
    | _ :: t => aux t acc
    end in
  aux l 0.

Fixpoint count_rotation_gates {dim} (l : gate_list dim) :=
  let fix aux l acc :=
    match l with
    | [] => acc
    | (App1 (fU_PI4 _) _) :: t  => aux t (acc + 1)
    | _ :: t => aux t acc
    end in
  aux l 0.

Fixpoint count_CNOT_gates {dim} (l : gate_list dim) :=
  let fix aux l acc :=
    match l with
    | [] => acc
    | (App2 fU_CNOT _ _) :: t => aux t (acc + 1)
    | _ :: t => aux t acc
    end in
  aux l 0.


(*******************************)
(** Benchmark representation  **)
(*******************************)
(* The benchmarks we will be using include Toffoli gates. Eventually, we will
   want to compile these gates away. But referencing the Toffoli gates directly
   will be useful for some optimizations (such as X propagation) *)

Inductive benchmark_gate_app : Set :=
| bench_H : nat -> benchmark_gate_app
| bench_X : nat -> benchmark_gate_app
| bench_Z : nat -> benchmark_gate_app
| bench_CNOT : nat -> nat -> benchmark_gate_app
| bench_TOFF : nat -> nat -> nat -> benchmark_gate_app.

Definition TOFF {dim} (a b c : nat) : gate_list dim :=
  (_H c) :: (_CNOT b c) :: (_TDAG c) :: (_CNOT a c) :: (_T c) :: (_CNOT b c) :: (_TDAG c) :: (_CNOT a c) :: (_CNOT a b) :: (_TDAG b) :: (_CNOT a b) :: (_T a) :: (_T b) :: (_T c) :: (_H c) :: [].

Fixpoint benchmark_to_list dim (l : list benchmark_gate_app) : gate_list dim :=
  match l with
  | []                      => []
  | (bench_H n) :: t        => (_H n) :: (benchmark_to_list dim t)
  | (bench_X n) :: t        => (_X n) :: (benchmark_to_list dim t)
  | (bench_Z n) :: t        => (_Z n) :: (benchmark_to_list dim t)
  | (bench_CNOT m n) :: t   => (_CNOT m n) :: (benchmark_to_list dim t)
  | (bench_TOFF m n p) :: t => (TOFF m n p) ++ (benchmark_to_list dim t)
  end.
