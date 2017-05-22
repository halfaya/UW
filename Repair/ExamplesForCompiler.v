(* Here are some examples for the compiler to think about
   how I would translate different kinds of proofs to find patches.

   These are supposed to be simple/minimal examples that show different cases,
   so proofs are deliberately simple.

   These will probably eventually be benchmarks, though to start off,
   it would be good to have more examples of the easiest case (four).
   I don't think the ease of four is because of the simplicity of le.
   It's easy because the patch we are looking for shows up explicitly, rather than implicitly
   [requiring us to understand more about the type theory]. *)

Require Import Arith NPeano.

(* One: Sum / coproduct
 
   Here we have two simple proofs of a different conclusion from the same hypothesis
   using different constructors of sum.

   The third proof is from one conclusion to the other conclusion, but is not possible
   to infer from the first two proofs unless you know about elimination/destruct (sum_rect/match). 
   So this makes it extra interesting. *)

Theorem SumOne :
  forall T1 T2,
    T1 ->
    sum T1 T2.
Proof.
  intros. left. apply X.
Qed.

Definition sumOneTerm (T1 T2 : Type) (X : T1) := 
  inl T2 X.

Theorem sumTwo : 
  forall T1 T2,
    T1 ->
    sum T2 T1.
Proof.
  intros. right. apply X.
Qed.

Definition sumTwoTerm (T1 T2 : Type) (X : T1) :=
  inr T2 X.

Theorem sumOneToSumTwo :
  forall T1 T2,
    sum T1 T2 ->
    sum T2 T1.
Proof.
  intros. elim X.
  - intros. right. apply a.
  - intros. left. apply b.
Qed.

Definition sumOneToSumTwoTerm (T1 T2 : Type) (X : sum T1 T2) :=
  sum_rect 
    (fun _ : sum T1 T2 => 
      sum T2 T1) 
    (fun a : T1 => inr T2 a)
    (fun b : T2 => inl T1 b) 
     X.

Theorem sumOneToSumTwoMatch :
  forall T1 T2,
    sum T1 T2 ->
    sum T2 T1.
Proof.
  intros. destruct X. 
  - right. apply t.
  - left. apply t.
Qed.

Definition sumOneToSumTwoMatchTerm (T1 T2 : Type) (X : T1 + T2) :=
match X with
| inl t => inr t
| inr t => inl t
end.

(* Two: Product 

   Product is the dual of sum (coproduct), so they model two different kinds of inductive types
   that have different properties. In sum you can always refactor an arrow out, but not an arrow in;
   in product you can always refactor an arrow in, but not an arrow out.
 
   Here we have two simple proofs using different projections from product. 
   These show the basic structure of product.

   The third proof is from one conclusion to the other conclusion, but is not possible
   to infer from the first two proofs unless you know about both substitution (eq_ind_r)
   and the constructors of le (in particular le_n). So this makes it interesting 
   if we end up implicitly expanding any inductive types that show up in our proofs. *)

Theorem productOne :
  forall (n : nat),
    (prod (n = 1) (n <= 1)) ->
    n = 1.
Proof.
  intros. elim H. intros. apply a.
Qed.

Print prod_ind.

Definition productOneTerm (n : nat) (H : (n = 1) * (n <= 1)) :=
  @prod_ind 
    (n = 1) 
    (n <= 1) 
    (fun _ : (n = 1) * (n <= 1) => 
       n = 1)
    (fun (a : n = 1) (_ : n <= 1) => 
       a) 
     H.

Theorem productTwo :
  forall (n : nat),
    (prod (n = 1) (n <= 1)) ->
    n <= 1.
Proof.
  intros. elim H. intros. apply b.
Qed.

Definition productTwoTerm (n : nat) (H : (n = 1) * (n <= 1)) :=
  @prod_ind 
    (n = 1) 
    (n <= 1) 
    (fun _ : (n = 1) * (n <= 1) => 
       n <= 1)
    (fun (_ : n = 1) (b : n <= 1) => 
       b) 
     H.

Theorem productThree :
  forall (n : nat),
    n = 1 ->
    n <= 1.
Proof.
  intros. subst. apply le_n.
Qed.

Definition productThreeTerm (n : nat) (H : n = 1) :=
  @eq_ind_r 
    nat 
    1 
   (fun n0 : nat => 
      n0 <= 1) 
   (le_n 1) 
    n 
    H.

(* Three: Induction on nat

   This is the same proof inducting first over m, then over n, then over n but without
   introducing m until later.

   This one is not useful for patching, but it is useful for seeing how inducting over
   different hypotheses impacts the term we generate. So eventually,
   we can imagine combining this with something like four, and still being able to find
   the patch we need. *)

Theorem natIndOne :
  forall (n m : nat),
    n <= m + n.
  Proof.
    intros. induction m.
    - apply le_n.
    - apply le_S. apply IHm.
Qed.

Definition natIndOneTerm (n m : nat) :=
  nat_ind 
    (fun m0 : nat => n <= m0 + n) 
    (le_n (0 + n))
    (fun (m0 : nat) (IHm : n <= m0 + n) =>
       le_S n
       (plus m0 n) 
     IHm) 
     m.

Theorem natIndTwo :
  forall (n m : nat),
    n <= m + n.
  Proof.
    intros. induction n.
    - apply le_O_n.
    - rewrite <- plus_n_Sm. apply le_n_S. apply IHn. 
Qed.

Definition natIndTwoTerm (n m : nat) :=
  nat_ind 
    (fun n0 : nat => n0 <= m + n0) 
    (le_0_n (m + 0))
    (fun (n0 : nat) (IHn : n0 <= m + n0) =>
       eq_ind 
         (S (m + n0)) 
         (fun n1 : nat => S n0 <= n1) 
         (le_n_S n0 (m + n0) IHn)
         (m + S n0) 
         (plus_n_Sm m n0)) 
     n.

Theorem natIndThree:
  forall (n m : nat),
    n <= m + n.
Proof.
  intros n. induction n.
  - intros. apply le_O_n.
  - intros. rewrite <- plus_n_Sm. apply le_n_S. apply IHn. 
Qed.

Definition natIndThreeTerm (n : nat) :=
  nat_ind 
    (fun n0 : nat => forall m : nat, n0 <= m + n0)
    (fun m : nat => le_0_n (m + 0))
    (fun (n0 : nat) (IHn : forall m : nat, n0 <= m + n0) (m : nat) =>
       eq_ind 
        (S (m + n0)) 
        (fun n1 : nat => S n0 <= n1)
        (le_n_S n0 (m + n0) (IHn m)) 
        (m + S n0) 
        (plus_n_Sm m n0)) 
     n.

(* Four: Induction on less-than 
   This has a functor we should be able to "see." That functor is the proof
   of leIndThree. *)

Theorem leIndOne :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p.
Proof.
  intros. induction H0.
  - apply H.
  - apply le_S. apply IHle. 
Qed.

Check le_ind.

Print le.

Definition leIndOneTerm (n m p : nat) (H : n <= m) (H0 : m <= p) :=
  le_ind 
    m 
   (fun p0 : nat => n <= p0) 
    H
   (fun (m0 : nat) (_ : m <= m0) (IHle : n <= m0) => le_S n m0 IHle) 
    p 
    H0.

Theorem leIndTwo :
  forall (n m p : nat),
    n <= m ->
    m <= p ->
    n <= p + 17.
Proof.
  intros. induction H0.
  - apply le_plus_trans. apply H.
  - apply le_S. apply IHle. 
Qed.

Definition leIndTwoTerm (n m p : nat) (H : n <= m) (H0 : m <= p) :=
  le_ind 
    m 
   (fun p0 : nat => n <= p0 + 17) 
   (le_plus_trans n m 17 H)
   (fun (m0 : nat) (_ : m <= m0) (IHle : n <= m0 + 17) => le_S n (plus m0 17) IHle) 
    p 
    H0.

Theorem leIndThree :
  forall (n p : nat),
    n <= p ->
    n <= p + 17.
Proof.
  intros. apply le_plus_trans. apply H.
Qed.

Definition leIndThreeTerm (n p : nat) (H : n <= p) := 
  le_plus_trans n p 17 H.

(* Five: Co and contravariance

   When we switch (n = 0 -> False) into the hypothesis, it becomes contravariant.

   There's currently no patch for this one, this is here to feed to the compiler
   and see what happens.

   Another interesting thing about this set of proofs is that we can do the covariant direction
   either by substitution or by induction on le. Looking at the difference in terms here 
   is interesting. *)

Theorem co:
  forall (n : nat),
    (n > 0) ->
    (n = 0 -> False).
Proof.
  intros. subst. inversion H. 
Qed.

Definition coTerm (n : nat) (H : n > 0) (H0 : n = 0) :=
  eq_ind_r 
    (fun n0 : nat => n0 > 0 -> False)
    (fun H1 : 0 > 0 =>
    (fun H2 : 0 = 0 -> False => H2 eq_refl)
     match H1 in (_ <= n0) return (n0 = 0 -> False) with
     | le_n =>
         fun H2 : 1 = 0 =>
         (fun H3 : 1 = 0 =>
          (fun H4 : False => (fun H5 : False => False_ind False H5) H4)
            (eq_ind 1
               (fun e : nat => match e with
                               | 0 => False
                               | S _ => True
                               end) I 0 H3)) H2
     | le_S m H2 =>
         fun H3 : S m = 0 =>
         (fun H4 : S m = 0 =>
          (fun H5 : False =>
           (fun H6 : False => False_ind (1 <= m -> False) H6) H5)
            (eq_ind (S m)
               (fun e : nat => match e with
                               | 0 => False
                               | S _ => True
                               end) I 0 H4)) H3 H2
     end) H0 H.

Theorem coInd :
  forall (n : nat),
    (n > 0) ->
    (n = 0 -> False).
Proof.
  intros. induction H; inversion H0.
Qed.

Definition coIndTerm (n : nat) (H : n > 0) (H0 : n = 0) :=
le_ind 1 (fun n0 : nat => n0 = 0 -> False)
  (fun H1 : 1 = 0 =>
   (fun H2 : 0 = 0 -> False => H2 eq_refl)
     match H1 in (_ = y) return (y = 0 -> False) with
     | eq_refl =>
         fun H2 : 1 = 0 =>
         (fun H3 : 1 = 0 =>
          (fun H4 : False => (fun H5 : False => False_ind False H5) H4)
            (eq_ind 1
               (fun e : nat => match e with
                               | 0 => False
                               | S _ => True
                               end) I 0 H3)) H2
     end)
  (fun (m : nat) (_ : 1 <= m) (_ : m = 0 -> False) (H2 : S m = 0) =>
   (fun H3 : 0 = 0 -> False => H3 eq_refl)
     match H2 in (_ = y) return (y = 0 -> False) with
     | eq_refl =>
         fun H3 : S m = 0 =>
         (fun H4 : S m = 0 =>
          (fun H5 : False => (fun H6 : False => False_ind False H6) H5)
            (eq_ind (S m)
               (fun e : nat => match e with
                               | 0 => False
                               | S _ => True
                               end) I 0 H4)) H3
     end) n H H0.

Theorem contra:
  forall (n : nat),
    (n = 0 -> False) ->
    (n > 0).
Proof.
  intros. induction n.
  - apply False_ind. apply H. reflexivity. 
  - apply lt_O_Sn. 
Qed.

Definition contraTerm (n : nat) (H : n = 0 -> False) :=
  nat_ind 
    (fun n0 : nat => (n0 = 0 -> False) -> n0 > 0)
    (fun H0 : 0 = 0 -> False => False_ind (0 > 0) (H0 eq_refl))
    (fun (n0 : nat) (_ : (n0 = 0 -> False) -> n0 > 0) (_ : S n0 = 0 -> False) =>
       lt_0_Sn n0) 
  n H.

(* Example six should use a tree of some kind.
   I'm not sure what to prove here that would reveal interesting strcture.
   Below is a simple natTree to use for the eventual example six. *)

Inductive natTree : Type :=
| Leaf : natTree
| Node : natTree -> nat -> natTree -> natTree.

(* Example seven should deal with an undecidable domain. *)

(* Example eight should use an AST, maybe the STLC. *)

(* Example nine should maybe switch the order of arguments *)
