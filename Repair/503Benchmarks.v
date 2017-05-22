(* Benchmark proofs *)

Require Import Arith NPeano List.

(* For each benchmark, there is an old, a new,
   and a patch from new to old.
   Your job is to find the patch.

   You should also assume that you can't
   directly apply the old theorem, though
   you can reprove the old theorem from
   scratch if you want. This is why we ask
   you to leave all of the old theorems as admitted. *)

(* --- 1 --- *)

Theorem leTransOld:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle. 
Admitted. (* Don't change to QED *)

Theorem leTransNew:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - apply H.
  - constructor. apply IHle. 
Qed.

Theorem leTransOldViaNew :
  (forall (n m p : nat),
     n <= m ->
     m <= p ->
     n <= p) ->
  (forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 1).
Proof.
  (* Your patch here. *)
Admitted. (* Change to QED when done. *)

(* --- 2 --- *)

Theorem leTransSOld:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= S p.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle. 
Admitted. (* Don't change to QED *)

Print leTransSOld.

Theorem leTransSNew:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.   
  - intuition.
  - constructor. apply IHle.
Qed.

Theorem leTransSOldViaNew:
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

(* --- 3 --- *)

Theorem leTransLtLeOld:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < S p.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle.
Admitted. (* Don't change to QED *)

Theorem leTransLtLeNew:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.   
  - intuition.
  - constructor. apply IHle.
Qed.

Theorem leTransLtLeOldViaNew:
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

(* --- 4 --- *)

Theorem leTransSPlusOld:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < p + 1.
Proof.
  intros. induction H0.
  - rewrite plus_comm. intuition.
  - constructor. apply IHle.
Admitted. (* Don't change to QED *)

Theorem leTransSPlusNew:
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n < S p.
Proof.
  intros. induction H0.
  - intuition.
  - constructor. apply IHle. 
Qed.

Theorem leTransSPlusOldViaNew:
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

(* --- 5 --- *)

Inductive ListSum : list nat -> nat -> Type :=
| ListSumNil :
    ListSum nil 0
| ListSumCons :
    forall (h : nat) (tl : list nat) (n : nat),
       ListSum tl n ->
       ListSum (h :: tl) (h + n).

Theorem listSumOld:
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
Admitted. (* Don't change to QED *)

Theorem listSumNew:
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
    
Theorem listSumOldViaNew:
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

(* --- 6 --- *)

Theorem listAppLengthOld :
  forall l1 l2 : list nat,
    length (rev (l1 ++ l2)) = (length (rev l1)) + (length (rev l2)).
Proof.
  intros l1 l2.
  induction l1 as [| n l1' IHl1'].
  - simpl. reflexivity.
  - repeat rewrite -> rev_length in *. simpl. 
    rewrite -> IHl1'. reflexivity.
Admitted. (* Don't change to QED *)

Theorem listAppLengthNew :
  forall l1 l2 : list nat,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2. induction l1 as [| n l1' IHl1'].
  - reflexivity.
  - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem listAppLengthOldViaNew :
  (forall l1 l2 : list nat,
      length (l1 ++ l2) = (length l1) + (length l2)) ->
  (forall l1 l2 : list nat,
      length (rev (l1 ++ l2)) = (length (rev l1)) + (length (rev l2))).
Proof.
  (* Your patch here. *)
Admitted. (* Change to QED when done. *)

(* --- 7 --- *)

Lemma andbOld :
  forall b1 b2,
    andb b1 b2 = true -> b1 = true \/ b2 = true.
Proof.
  intros b1 b2. intros H. destruct b1; destruct b2.
  - left. reflexivity.
  - left. reflexivity.
  - right. reflexivity.
  - discriminate.
Admitted.

Lemma andbNew :
  forall b1 b2,
    andb b1 b2 = true -> b1 = true /\ b2 = true.
Proof.
  intros b1 b2. intros H. destruct b1; destruct b2; split; try reflexivity; discriminate.
Qed.

Theorem andbOldViaNew :
  (forall b1 b2,
      andb b1 b2 = true -> b1 = true /\ b2 = true) ->
  (forall b1 b2,
      andb b1 b2 = true -> b1 = true \/ b2 = true).
Proof.
  (* Your patch goes here *)
Admitted. (* Change to QED when done. *)

(* --- 8 --- *)

Theorem inMapOld :
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
Admitted. (* Don't change to QED *)

Theorem inMapNew :
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

Theorem inMapOldViaNew :
  (forall (A B : Type) (f : A -> B) (l : list A) (x : A),
      In x l ->
      In (f x) (map f l)) ->
  (forall (A B : Type) (f : A -> B) (l : list A) (x : A),
      In x l ->
      In (f x) (rev (map f l))).
Proof.
  (* Your patch here. *)
Admitted. (* Change to QED when done. *)
