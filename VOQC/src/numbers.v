Require Import UnitaryOps.
Require Import BooleanCompilation.
Open Scope ucom.

(*********************************)
(** Boolean Circuit Compilation **)
(*********************************)
(* This file defines a 'compile' function that converts an arbitrary
   boolean expression into a reversible circuit that (provably) uncomputes 
   its ancillae. We use eager ancilla cleanup, which requires fewer qubits,
   but more gates, than the lazy approach. Because SQIR does not allow
   initializing / discarding qubits, we precompute the number of ancillae
   needed and include them in the global register.
 
   The boolean expression language and compilation strategy are modelled 
   after the Oracles.v file in (Re)QWIRE, which is based on the ReVerC 
   reversible circuit compiler. 

   We prove that compilation is correct by showing that the output circuit
   has the expected behavior on any basis state. The proof requires some
   new formalisms for describing classical states (see 'f_to_vec'). *)

(** Natural Number Expressions **)
Inductive  nexp :=
| n_val : nat -> nat -> nexp (* value, num_bits*)
| n_plus : nexp -> nexp -> nexp
 (*| n_group : nat -> nexp *). (* Just starting line and length*)

Fixpoint interpret_nexp (n : nexp) (f : nat -> bool): nat :=
  match n with
  | n_val n1 n2 => n1
  | n_plus n1 n2 => (interpret_nexp n1 f) + (interpret_nexp n2 f)
  end. 


Fixpoint size n : nat :=
  match n with
| n_val n1 n2 => n2
| n_plus n1 n2 => max (size n1) (size n2)
  end.

Fixpoint interpret_nexp_at (n : nexp) (f : nat -> bool) (d : nat) : bool := 
  match n with (*d of 0 is last bit, d of 1 is next to least significant *)
  |n_val n1 n2 => if (n1/( 2 ^ d )%nat  mod 2 =? 1) then true else false
  | n_plus n1 n2 => let val := interpret_nexp n f in if (val mod (2 ^ d)%nat =? 1) then true else false
  end. 


                                                                                                
Inductive nexp_well_typed : nat -> nexp -> Prop :=
| WT_n_val : forall n n1 n2, (n2 > 0)%nat -> nexp_well_typed n (n_val n1 n2 )
| WT_n_plus : forall n n1 n2, nexp_well_typed n n1 -> nexp_well_typed n n2 -> nexp_well_typed n (n_plus n1 n2).
(*may want to return to this later *)

Lemma n_well_typed_increase_dim : forall e n n',
    (n <= n')%nat ->
    nexp_well_typed n e ->
    nexp_well_typed n' e.
Proof.
  intros.
  induction H0.
  - try constructor; try lia.
  - try constructor; try lia;
      try apply IHnexp_well_typed1;
      try apply IHnexp_well_typed2;
      assumption.
Qed.
    

Lemma interpret_nexp_f : forall i n f f',
    nexp_well_typed i n ->
    (forall k, (k < i)%nat -> f k = f' k) ->
    interpret_nexp n f = interpret_nexp n f'.
Proof.
  intros.
  induction H; simpl; try reflexivity.
  rewrite IHnexp_well_typed1.
  rewrite IHnexp_well_typed2.
  reflexivity.
  apply H0.
  apply H0.
Qed.
(*
Lemma interpret_bexp_f : forall i b f f',
  bexp_well_typed i b ->
  (forall k, (k < i)%nat -> f k = f' k) ->
  interpret_bexp b f = interpret_bexp b f'.
Proof.
  intros.
  induction H; simpl; try reflexivity.
  - apply H0. assumption.
  - rewrite IHbexp_well_typed1; try assumption.
    rewrite IHbexp_well_typed2; try assumption.
    reflexivity.
  - rewrite IHbexp_well_typed1; try assumption.
    rewrite IHbexp_well_typed2; try assumption.
    reflexivity.
  - rewrite IHbexp_well_typed1; try assumption.
    rewrite IHbexp_well_typed2; try assumption.
    reflexivity.
  - rewrite IHbexp_well_typed; try assumption.
    reflexivity.
Qed.
*)
Lemma interpret_nexp_update : forall n f i j r,
    (i <= j)%nat ->
    nexp_well_typed i n->
    interpret_nexp n f = interpret_nexp n (update f j r).
Proof.
  intros.
  apply interpret_nexp_f with (i:=i); try assumption.
  intros.
  rewrite update_index_neq; try lia.  
  reflexivity.
Qed.



(** Compilation of boolean expressions to oracles **)

(* How many input variables does this expression use? *)

(*Where the last used input of the number is *)
Fixpoint n_max_var (n : nexp) (v : nat) :=
  match n with
  | n_plus n1 n2 => ((n_max_var n1 v) + (n_max_var n2 v) + max (size n1) (size n2))%nat
  | n_val n1 n2 => max v n2
  
  end.

(*This isn't used right now *)
Fixpoint n_no_vars n : nat:=
  match n with
  | n_val n1 n2 => 0
  | n_plus n1 n2 => 0 
  end.

 


Definition n_num_inputs (n : nexp) : nat := n_max_var n 0 .
(*Lemma n_num_inputs_well_typed : forall n,
    nexp_well_typed (n_num_inputs n) n.
Proof.
  induction n.
  - constructor. unfold n_num_inputs; simpl. lia.  
  - constructor.
    + apply n_well_typed_increase_dim with (n:=n_num_inputs n1); try assumption.
      unfold n_num_inputs. simpl. lia.
    + apply n_well_typed_increase_dim with (n:= n_num_inputs n2); try assumption.
      unfold n_num_inputs. simpl. lia.
Qed.
*)


(* How many ancillary qubits are needed to represent this expression? *)




Fixpoint n_num_out n : nat :=
  match n with
  | n_val n1 n2 => 0
  | n_plus n1 n2 => 1 + (max (size n1) (size n2)) 
  end.
Fixpoint n_num_ancillae n : nat :=
  match n with
  | n_plus n1 n2 => size n1 + 7
  | _ => 0
  end.
  
(* Total number of qubits required. *)
Definition n_dim (n : nexp) : nat := (n_num_inputs n) + (n_num_out n) + (n_num_ancillae n).
(* Translate a boolean expression into a reversible circuit. The produced 
   program should only modify the qubit at index i.
   - i is the index of the result
   - j is the index of the next available ancilla. *)





(** FOR NOW, SECOND NUMBER MUST BE LARGER SIZE THAN THE FIRST **)
(*b for begin, l for length: Note, j is to store the cnot, j+1 also used for carry *)
Fixpoint n_compile_plus {dim} (n1_e n2_e n1_l n2_l i j : nat) : base_ucom dim:=
  match n1_l, n2_l with
  | 0, 0 => compile' (b_var j) i (j + 2) (* Only the carry!*)

  | 0, S v => compile' (b_var j) i (j + 2);  (*Very similar to below  but other bit*)
              compile' (b_var n2_e) i (j + 2);
              n_compile_plus n1_e (n2_e - 1) (0) v (i - 1) j 
  (*
  | S v, 0 => compile' (b_xor (b_var j) (b_var i)) i (j + 1);  (*Very similar to below *)
              compile' (b_and (b_var j) (b_var i)) j (j+1);  (*don't need carry or the xor to add*)
              compile' (b_var n1_e) i (j + 1);
              n_compile_plus (n1_e - 1) n2_e v (0) (i - 1) j*)

  | S v1, S v2 => (*Puts carry in j, with j increasing 1 for each carry. So many ancillae bits *)
    compile' (b_xor (b_var n1_e) (b_var n2_e)) (j + 2) (j + 5);  
    compile' (b_and (b_var n1_e) (b_var n2_e)) (j + 3) (j + 5);
    compile' (b_xor (b_var (j + 2)) (b_var (j))) (i) (j + 5);(*sum- old carry is j*)
    compile' (b_and (b_var (j + 2)) (b_var (j))) (j + 4) (j + 5); 
    compile' (b_or (b_var (j + 3)) (b_var (j + 4))) (j + 1) (j + 5); (*carry *)
    compile' (b_and (b_var (j + 2)) (b_var (j))) (j + 4) (j + 5); (*cleanup*)
    compile' (b_xor (b_var n1_e) (b_var n2_e)) (j + 2) (j + 5);(*cleanup*)  
    compile' (b_and (b_var n1_e) (b_var n2_e)) (j + 3) (j + 5);(*cleanup*)
    n_compile_plus (n1_e - 1) (n2_e - 1) v1 v2 (i - 1) (j + 1) ; 
    compile' (b_xor (b_var n1_e) (b_var n2_e)) (j + 2) (j + 5);  (*Recalculate everything (except sum) to remove carry *)
    compile' (b_and (b_var n1_e) (b_var n2_e)) (j + 3) (j + 5);
    compile' (b_and (b_var (j + 2)) (b_var (j))) (j + 4) (j + 5); 
    compile' (b_or (b_var (j + 3)) (b_var (j + 4))) (j + 1) (j + 5);
    compile' (b_and (b_var (j + 2)) (b_var (j))) (j + 4) (j + 5); 
    compile' (b_xor (b_var n1_e) (b_var n2_e)) (j + 2) (j + 5); 
    compile' (b_and (b_var n1_e) (b_var n2_e)) (j + 3) (j + 5)
  | _, _ => SKIP 
end.

(*TODO: Replace nat with a binary one *)
Fixpoint n_compile_val {dim} (n1 n2 offset: nat) : base_ucom dim :=
  (*remove the offset and combine with i and j next time *)
  match n2 with
  |S n => if (n1 mod 2) =? 1 then X (n2 - 1 + offset);
                                  n_compile_val (n1 / 2) n offset
                             else n_compile_val (n1 / 2) n offset
  |0 => SKIP
  end.
Fixpoint n_compile' {dim} (n : nexp) (i j offset: nat) : base_ucom dim :=
  match n with
  | n_val n1 n2 => n_compile_val n1 n2 offset 
                        
  | n_plus n1 n2 => n_compile' n1 i j offset;
                    n_compile' n2 i j (offset + size n1) %nat;
                    n_compile_plus (offset + size n1 - 1) (offset + size n2 + size n1 - 1) (size n1) (size n2) i j
  end. 

  
Definition n_compile n : base_ucom (n_dim n) :=
  n_compile' n (n_max_var n 0) (n_max_var n 0 + 1) 0.
(* Correctness of compile':
   1. The value at index i is xor-ed with the desired boolean expression.
   2. All other values remain unchanged.

   Notes:
   * The well-typedness constraint is used in the b_var case.
   * 'i < j' is used when applying f_to_vec_X, f_to_vec_CNOT, and f_to_vec_TOFF.
   * 'j + (num_ancillae b) < n + 1' and 'forall k ...' are used in the b_and 
     case -- note that this is the only case where the ancilla matter.
*)
Local Opaque CCX.


(*
Lemma n_compile'_correct : forall (n : nexp) (f : nat -> bool) (dim i j d: nat), (* d for digit (even though it's bits *)
    nexp_well_typed i n -> (i < j)%nat -> (d < size n)%nat -> (j + (n_num_ancillae n) < dim + 1)%nat ->
    (forall k, (k > i)%nat -> f k = false) ->  
    (uc_eval (@n_compile' dim n i j 0)) × (f_to_vec dim f) =
    f_to_vec dim (update f (i- d)%nat ((f (i - d)%nat) ⊕ (interpret_nexp_at n f d))).
Proof.
  intros.
  generalize dependent f.
  generalize dependent j.
  generalize dependent i.
  induction n; intros. (* Inductive structure of nexp *)
  - inversion H; subst; clear H.
    unfold n_compile'. unfold n_compile_val.
    (* Induction on d *)
   (* induction d.
    + unfold interpret_nexp_at.
      assert (n/(2 ^ 0) = n)%nat. simpl. apply Nat.div_1_r. rewrite H.
      induction n0. unfold size. simpl in H1. autorewrite with eval_db. try lia. try lia.
      destruct (n mod 2 =? 1).
      2:{induction n. assert ((0 / 2) = 0 )%nat. apply Nat.div_small. lia. rewrite H4. rewrite IHn0. reflexivity. unfold size.  unfold size in H1. rewrite H1. }*)
(*Induction on n0?*)
    induction n. (* induction on value of the number *)
    + unfold interpret_nexp_at. unfold size. simpl in H1.
      rewrite Nat.div_0_l. rewrite Nat.mod_0_l.
      induction n0. (*induction on number of bits used *) 
      * simpl. autorewrite with eval_db; try lia.
      * simpl. simpl in IHn0. simpl in H2.  assert (n0 > 0 -> S n0 > 0)%nat by lia.
        rewrite IHn0. reflexivity.                    
      try lia.
      try lia.
    + destruct (n mod 2 =? 1).
      2:{unfold interpret_nexp_at. unfold interpret_nexp_at in IHn0. simpl in H1. rewrite IHn0. }
Abort.
*)
(** Examples **)
(* Small examples taken from (Re)QWIRE's Arithmetic.v file.
   
   TODO: Port over n-qubit adder examples. (I don't think this will cause
   any problems, but precomputing the number of ancillae might get a bit
   weird.) *)

Infix "⊻" := b_xor (at level 40).
Infix "∧" := b_and (at level 40).
(*Coercion b_var : nat >-> bexp.*)

Local Close Scope R_scope.

(*
Input : var 1 : y
        var 2 : x
        var 3 : cin
Output : cout = cin(x ⊕ y) ⊕ xy
*)
Definition adder_cout_bexp : bexp := (3 ∧ (2 ⊻ 1)) ⊻ (2 ∧ 1).
Eval cbv in (compile adder_cout_bexp).

(*
Input : var 0 : y
        var 1 : x
        var 2 : cin
Output : sum = cin ⊕ (x ⊕ y)
 *)
Definition adder_sum_bexp : bexp := 2 ⊻ (1 ⊻ 0).
Eval cbv in (compile adder_sum_bexp).

(*
Input : var 0 : x
        var 1 : y
Output : xor = x ⊕ y
*)
Definition xor_bexp : bexp := 0 ⊻ 1.
Eval cbv in (compile xor_bexp).

(*
Input : var 0 : x
Output : x' = x
*)
Definition id_bexp : bexp := 0.
Eval cbv in (compile id_bexp).

(*
Input : var 0 : a
        var 1 : b
        var 2 : c
        var 3 : d
Output : ((a ⊻ b) ∧ (c ⊻ d))
 *)
Definition test_bexp : bexp := (0 ⊻ 1) ∧ (2 ⊻ 3).
Eval cbv in (compile test_bexp).

(*Input : var 0 : x
  Output: not = not x *)
Definition not_bexp : bexp := (b_not 0).
Eval cbv in (compile not_bexp).

Definition true_bexp : bexp := (b_f).
Eval cbv in (compile true_bexp).

Definition var_bexp : bexp := (b_var 1).
Eval cbv in (compile var_bexp).

Definition or_bexp : bexp := (b_or 4  (b_or 0 1)).
Eval cbv in (compile or_bexp).

Set Printing Depth 70.
Definition num_nexp : nexp := (n_plus (n_val 3 2) (n_val 3 2)).
Redirect "out2" Eval compute in (n_compile num_nexp).
Eval cbv in (n_compile num_nexp).
