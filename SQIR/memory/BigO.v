Import Nat.
Require Import Psatz.

(*Local Open Scope R_scope.

Notation "w <= x <= y <= z" := (w <= x <= y /\ y <= z)
  (at level 70, x at next level, y at next level, no associativity) : R_scope.*)

Local Open Scope nat_scope.

Definition Big_Theta g :=
  fun f => exists c1 c2 n0, forall n, n >= n0 ->
  g n <= c1 * f n /\ f n <= c2 * g n.

Definition Big_O g :=
  fun f => exists c n0, forall n, n >= n0 ->
  f n <= c * g n.

Notation "f 'is' S" := (S (f : nat -> nat) : Prop) (at level 70).

Example test_Big_O :
  (fun n => 3 * n ^ 2 - 4 * n + 1) is Big_O (fun n => n ^ 2).
Proof. exists 4, 1. simpl. lia. Qed.

Definition Big_Omega g :=
  fun f => exists c n0, forall n, n >= n0 ->
  g n <= c * f n.

Example test_Big_Omega :
  (fun n => 3 * n ^ 2 - 4 * n + 1) is Big_Omega (fun n => n ^ 2).
Proof. exists 1, 2. simpl. nia. Qed.

Theorem Big_Theta_iff :
  forall f g,
  f is Big_Theta g <-> f is Big_O g /\ f is Big_Omega g.
Proof.
  split.
  - intros [c1 [c2 [n0 H]]]. split.
    + exists c2, n0. intros. apply H. assumption.
    + exists c1, n0. intros. apply H. assumption.
  - intros [[c2 [n2 H2]] [c1 [n1 H1]]].
    exists c1, c2, (n1 + n2). split.
    + apply H1. lia.
    + apply H2. lia.
Qed.

Example test_Big_Theta :
  (fun n => 3 * n ^ 2 - 4 * n + 1) is Big_Theta (fun n => n ^ 2).
Proof.
  apply Big_Theta_iff. split.
  - apply test_Big_O.
  - apply test_Big_Omega.
Qed.

