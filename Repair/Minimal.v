Require Import Arith NPeano.
Require Import List.


Definition newMinimal (n m n0 : nat) (H : eq m n) :=
  Coq.Init.Logic.eq_ind_r
    (fun (m : nat) => (le n (Coq.Init.Nat.max n0 m)))
    (Coq.Arith.PeanoNat.Nat.le_max_r n0 n)
    H.

Definition oldMinimal (n m n0 : nat) (H : eq m n) :=
  Coq.Init.Logic.eq_ind_r
    (fun (m : nat) => (le n (Coq.Init.Nat.add (Coq.Init.Nat.max n0 m) (S O))))
    (le_plus_trans  n (Coq.Init.Nat.max n0 n)  (S O)  (Coq.Arith.PeanoNat.Nat.le_max_r n0 n))
     H.

Print eq_ind_r.
Check Coq.Arith.PeanoNat.Nat.le_max_r.
Check newMinimal.
Check oldMinimal.

Definition expected (n m n0 : nat) (H : n <= Init.Nat.max n0 m) :=
   le_plus_trans n (Init.Nat.max n0 m) (S O) H.

Print le_plus_trans.

Definition patchF (n m : nat) (H : n < S n + m): n < n + S m :=
 eq_ind_r 
   (fun (n0 : nat) => n < n0) 
   (eq_ind 
      (S n + m) 
      (fun (n0 : nat) => n < n0)
      H 
      (S (n + m)) 
      (Coq.Arith.PeanoNat.Nat.add_succ_l n m)) 
   (Coq.Arith.PeanoNat.Nat.add_succ_r n m).

Definition subPatchF (n m : nat) (H : n < S n + m): n < S (n + m) :=
eq_ind 
  (S n + m) 
  (fun (n0 : nat) => n < n0)
  H 
  (S (n + m)) 
  (Coq.Arith.PeanoNat.Nat.add_succ_l n m).

Definition patchFWithSub (n m : nat) (H : n < S (n + m)): n < n + S m :=
  eq_ind_r 
   (fun (n0 : nat) => n < n0) 
   H
   (Coq.Arith.PeanoNat.Nat.add_succ_r n m).

Definition patchForward2 (n m : nat) (H : n < S n + m) : n < n + S m := 
eq_ind_r (fun n0 : nat => n < n0)
  (eq_ind (S n + m) (fun n0 : nat => n < n0) H (S (n + m))
     (PeanoNat.Nat.add_succ_l n m)) (PeanoNat.Nat.add_succ_r n m).

Definition patchForward3 (n m : nat) (H : n < S n + m) : n < n + S m := 
eq_ind_r (fun n0 : nat => n < n0)
  (eq_ind_r (fun n0 : nat => n < n0) H 
     (PeanoNat.Nat.add_succ_l n m)) (PeanoNat.Nat.add_succ_r n m).

Definition patchForward4 (n m : nat) (H : n < S n + m) : n < n + S m := 
eq_ind_r (fun n0 : nat => n < n0)
  H (PeanoNat.Nat.add_succ_r n m).

(*
eq_ind
     : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y

eq_ind_r
     : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, y = x -> P y
 *)

Print or_introl.

(**********)


Inductive Max : list nat -> nat -> Type :=
  | MaxNil:
      Max nil 0
  | MaxCons:
      forall l n m,
        Max l n ->
        Max (m :: l) (max n m).

Theorem InMaxLeOld:
  forall (n : nat) (m : nat) (l : list nat),
    In n l ->
    Max l m ->
    (n <= m + 1).
Proof.
  intros. induction H0.
  - inversion H.
  - induction H.
    + subst. apply le_plus_trans. apply NPeano.Nat.le_max_r.
    + apply IHMax in H. rewrite H.
      apply plus_le_compat_r.
      apply NPeano.Nat.le_max_l.
Qed.

Theorem InMaxLeNew:
  forall (n : nat) (m : nat) (l : list nat),
    In n l ->
    Max l m ->
    (n <= m).
Proof.
  intros. induction H0.
  - inversion H.
  - induction H.
    + subst. apply NPeano.Nat.le_max_r.
    + apply IHMax in H. rewrite H. apply NPeano.Nat.le_max_l.
Qed.

Definition changeTMinimalOld (a n m : nat) (l0 : list nat) (H : a = n) (H0 : Max (a :: l0) m ) :=
  eq_ind_r
    (fun a0 : nat => Max (a0 :: l0) m -> n <= m + 1)
    (fun (H7 : Max (n :: l0) m) =>
       InMaxLeOld n m (n :: l0) (or_introl eq_refl) H7)
    H
    H0.

Definition T (a n m : nat) (l0 : list nat) (H : a = n) (H0 : Max (a :: l0) m) (F : (Max (n :: l0) m) -> (n <= m + 1)) :=
  F
  (eq_rec_r
    (fun a0 : nat => Max (a0 :: l0) m)
    H0
    (eq_sym H)).

Definition T_inv (a n m : nat) (l0 : list nat) (H : a = n) (H0 : n <= m + 1) (F : (n <= m + 1) -> (Max (n :: l0) m)) :=
  eq_rec_r
   (fun a0 : nat => Max (a0 :: l0) m)
   (F H0)
   H.

Check T_inv.