(* The le type is parameterized over n,
   so (le n) is really the type of all m : nat that
   are greater than or equal to n. *)

Require Import NPeano Arith.

Print le.

(* Inductive le (n : nat) : nat -> Prop :=
    le_n :
      n <= n 
  | le_S :
      forall m : nat,
        n <= m ->
        n <= S m *)

(* The induction principle Coq generations 
   takes this into account. Note that n
   shows up as a parameter before P, and that
   P : nat -> Prop. *)

Check le_ind.

(* forall (n : nat) (P : nat -> Prop),
     P n ->              (* le_n *)
    (forall m : nat,     (* le_S *)
       n <= m ->
       P m ->
       P (S m)) ->
     forall n0 : nat,    (* Conclusion *)
       n <= n0 ->
       P n0 *)

(* Now let's define le_2, which is like le
   but without a parameter. *)

Inductive le_2 : nat -> nat -> Prop :=
  le_n_2 :
    forall (n : nat),
      le_2 n n
| le_S_2 :
    forall (n m : nat),
      le_2 n m ->
      le_2 n (S m).

(* Now Coq generates le_2_ind. Note that the
   initial n parameter is gone before P,
   and now P : nat -> nat -> Prop. *)

Check le_2_ind.

(* forall (P : nat -> nat -> Prop),
     (forall n : nat,      (* le_n_2 *)
        P n n) ->
     (forall n m : nat,    (* le_S_2 *)
        le_2 n m ->
        P n m ->
        P n (S m)) ->
     forall n n0 : nat,    (* Conclusion *)
       le_2 n n0 ->
       P n n0 *)

(* Aux lemmas I need for le_2 so I don't pollute 
   my final proof at all, so it's easy to see the
   correspondence. You can ignore these. *)

Lemma le_le_2:
  forall (n m : nat),
    n <= m ->
    le_2 n m.
Proof.
  intros. induction H; constructor. apply IHle.
Qed. 

Lemma le_2_plus_l:
  forall (n m : nat),
    le_2 n (n + m).
Proof.
  intros. apply le_le_2. apply le_plus_l.
Qed.

(* Proofs with le_ind and le_ind_2 *)

Theorem le_plus_trans_via_le_ind :
  forall (n m p : nat),
    n <= m ->
    n <= m + p.
Proof.
  intros. induction H.
  - apply le_plus_l.
  - apply (le_S n (m + p) IHle).
Qed.

(* Note now that the n shows up as a parameter,
   and our P : nat -> Prop .*)

Print le_plus_trans_via_le_ind.

(* fun (n m p : nat) (H : n <= m) =>
     le_ind n (fun m0 : nat => n <= m0 + p)
       (le_plus_l n p)          (* le_n *)
       (fun                     (* le_S *)
         (m0 : nat)
         (_ : n <= m0)
         (IHle : n <= m0 + p) =>
           le_S n (m0 + p) IHle)
*)

Theorem le_plus_trans_via_le_2_ind :
  forall (n m p : nat),
    le_2 n m ->
    le_2 n (m + p).
Proof.
  intros. induction H.
  - apply le_2_plus_l.
  - apply (le_S_2 n (m + p) IHle_2).
Qed.

(* In this case, n is no longer a parameter,
   our P : nat -> nat -> Prop, and to account
   for this the proofs of the cases each take an
   extra (n0 : nat), which is basically factored
   out in the original proof. *)

Print le_plus_trans_via_le_2_ind.

(* fun (n m p : nat) (H : le_2 n m) =>
     le_2_ind (fun n0 m0 : nat => le_2 n0 (m0 + p))
       (fun n0 : nat =>             (* le_n_2 *)
          le_2_plus_l n0 p)
       (fun                         (* le_S_2 *)
         (n0 m0 : nat)
         (_ : le_2 n0 m0)
         (IHle_2 : le_2 n0 (m0 + p)) =>
           le_S_2 n0 (m0 + p) IHle_2) n m H *)