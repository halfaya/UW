(* Benchmark proofs *)

(* Require Import Arith NPeano List. *)
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.

(* Each benchmark consists of a proven original theorem, a proven
   modified version, and an admitted patch theorem. The modified
   theorem is always stronger than the original. The patch
   theorem establishes the original theorem from the modified one,
   so that `patch(modified)` can be used in place of `original`.
   Your job is to prove each patch theorem.

   You should assume that you can't directly apply the original
   theorem, though you can reprove it from scratch if you want.
   This is why we ask you to leave all the old theorems aborted. *)




(* ------------------------ 1 ------------------------ *)

Print le.


(* ORIGINAL *)
Theorem le_trans :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle. 
Abort. (* Don't change to QED *)

(* MODIFIED *)
Theorem le_trans :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - apply H.
  - constructor. apply IHle. 
Qed.

(* PATCH *)
Theorem le_trans_patch :
  (forall (n m p : nat),
     n <= m ->
     m <= p ->
     n <= p) ->
  (forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1).
Proof.
  (* TODO: Establish ORIGINAL from MODIFIED. *)
Admitted. (* Change to QED when done. *)

(* --------------------------------------------------- *)




(* ------------------------ 2 ------------------------ *)

(* ORIGINAL *)
Theorem le_trans_succ :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= S p.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle. 
Abort. (* Don't change to QED *)

(* MODIFIED *)
Theorem le_trans_succ :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.   
  - intuition.
  - constructor. apply IHle.
Qed.

(* PATCH *)
Theorem le_trans_succ_patch :
  (forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p) ->
  (forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= S p).
Proof.
  (* Your patch here. *)
Admitted. (* Change to QED when done. *)

(* --------------------------------------------------- *)




(* ------------------------ 3 ------------------------ *)

(* ORIGINAL *)
Theorem le_trans_lt_le :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < S p.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle.
Abort. (* Don't change to QED *)

(* MODIFIED *)
Theorem le_trans_lt_le :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.   
  - intuition.
  - constructor. apply IHle.
Qed.

(* PATCH *)
Theorem le_trans_lt_le_patch :
  (forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p) ->
  (forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < S p).
Proof.
  (* Your patch here. *)
Admitted. (* Change to QED when done. *)

(* --------------------------------------------------- *)




(* ------------------------ 4 ------------------------ *)

(* ORIGINAL *)
Theorem le_trans_plus_succ :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < p + 1.
Proof.
  intros. induction H0.
  - rewrite plus_comm. intuition.
  - constructor. apply IHle.
Abort. (* Don't change to QED *)

(* MODIFIED *)
Theorem le_trans_plus_succ :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < S p.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle. 
Qed.

(* PATCH *)
Theorem le_trans_plus_succ_patch :
  (forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < S p) ->
  (forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < p + 1).
Proof.
  (* Your patch here. *)
Admitted. (* Change to QED when done. *)

(* --------------------------------------------------- *)




(* ------------------------ 5 ------------------------ *)

Inductive ListSum : list nat -> nat -> Type :=
| ListSumNil :
    ListSum nil 0
| ListSumCons :
    forall (h : nat) (tl : list nat) (n : nat),
       ListSum tl n ->
       ListSum (h :: tl) (h + n).

(* ORIGINAL *)
Theorem list_sum :
  forall (n m : nat) (l1 l2 : list nat),
    ListSum l1 n ->
    ListSum (l1 ++ l2) (n + m) ->
    ListSum (rev (rev l2)) m.
Proof.
  intros. induction H.
  - rewrite rev_involutive. apply H0. 
  - inversion H0. subst.
    rewrite plus_assoc_reverse in H4.
    assert (n0 = n + m). 
    + eapply plus_reg_l; eauto.
    + subst. apply IHListSum in H2. apply H2.
Abort. (* Don't change to QED *)

(* MODIFIED *)
Theorem list_sum :
   forall (n m : nat) (l1 l2 : list nat),
     ListSum l1 n ->
     ListSum (l1 ++ l2) (n + m) ->
     ListSum l2 m.
Proof.
  intros. induction H.
  - apply H0.
  - inversion H0. subst.
    rewrite plus_assoc_reverse in H4.
    assert (n0 = n + m).
    + eapply plus_reg_l; eauto.
    + subst. apply IHListSum in H2. apply H2.
Qed.

(* PATCH *)
Theorem list_sum_patch :
  (forall (n m : nat) (l1 l2 : list nat),
     ListSum l1 n ->
     ListSum (l1 ++ l2) (n + m) ->
     ListSum l2 m) ->
  (forall (n m : nat) (l1 l2 : list nat),
    ListSum l1 n ->
    ListSum (l1 ++ l2) (n + m) ->
    ListSum (rev (rev l2)) m).
Proof.
  (* Your patch here. *)
Admitted. (* Change to QED when done. *)

(* --------------------------------------------------- *)




(* ------------------------ 6 ------------------------ *)

(* ORIGINAL *)
Theorem list_append_length :
  forall l1 l2 : list nat,
    length (rev (l1 ++ l2)) = (length (rev l1)) + (length (rev l2)).
Proof.
  intros l1 l2.
  induction l1 as [| n l1' IHl1'].
  - simpl. reflexivity.
  - repeat rewrite -> rev_length in *. simpl.
    rewrite -> IHl1'. reflexivity.
Abort. (* Don't change to QED *)

(* MODIFIED *)
Theorem list_append_length :
  forall l1 l2 : list nat,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

(* PATCH *)
Theorem list_append_length_patch :
  (forall l1 l2 : list nat,
      length (l1 ++ l2) = (length l1) + (length l2)) ->
  (forall l1 l2 : list nat,
      length (l1 ++ l2) = (length (rev l1)) + (length (rev l2))).
Proof.
  (* Your patch here. *)
Admitted. (* Change to QED when done. *)

(* --------------------------------------------------- *)




(* ------------------------ 7 ------------------------ *)

(* ORIGINAL *)
Lemma andb_true :
  forall b1 b2,
    andb b1 b2 = true -> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. intros H. destruct b1; destruct b2.
  - left. reflexivity.
  - left. reflexivity.
  - right. reflexivity.
  - discriminate.
Abort.

(* MODIFIED *)
Lemma andb_true :
  forall b1 b2,
    andb b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. intros H. destruct b1; destruct b2; split; try reflexivity; discriminate.
Qed.

(* PATCH *)
Theorem andb_true_patch :
  (forall b1 b2,
      andb b1 b2 = true -> b1 = true /\ b2 = true) ->
  (forall b1 b2,
      andb b1 b2 = true -> b1 = true \/ b2 = true).
Proof.
  (* Your patch goes here *)
Admitted. (* Change to QED when done. *)

(* --------------------------------------------------- *)




(* ------------------------ 8 ------------------------ *)

(* ORIGINAL *)
Theorem in_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (rev (map f l)).
Proof.
  intros A B f l x. rewrite <- in_rev.
  induction l as [|x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Abort. (* Don't change to QED *)

(* MODIFIED *)
Theorem in_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl. intros [].
  - simpl. intros [H' | H'].
    + rewrite H'. left. reflexivity.
    + right. apply IHl'. apply H'.
Qed.

(* PATCH *)
Theorem in_map_patch :
  (forall (A B : Type) (f : A -> B) (l : list A) (x : A),
      In x l ->
      In (f x) (map f l)) ->
  (forall (A B : Type) (f : A -> B) (l : list A) (x : A),
      In x l ->
      In (f x) (rev (map f l))).
Proof.
  (* Your patch here. *)
Admitted. (* Change to QED when done. *)

(* --------------------------------------------------- *)

