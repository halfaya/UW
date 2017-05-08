(* Default to 0 to make things easy, and use inductive def *)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Omega.
(*
Require Import Coq.Arith.Plus.
Require Import Coq.Numbers.Natural.Peano.NPeano.
 *)

Require Import Coq.Arith.PeanoNat.

Inductive Max : list nat -> nat -> Type :=
| MaxNil: 
    Max nil 0
| MaxCons: 
    forall l n m,
      Max l n ->
      Max (m :: l) (max n m).

(*
Inductive In : nat -> list nat -> Type :=
| Here:
    forall l n,
      In n (n :: l)
| There:
    forall l n m,
      In n l -> In n (m :: l).
*)

Theorem T1:
    forall (n : nat) (m : nat) (l : list nat),
        In n l ->
        Max l m -> 
        n <= m + 1.
Proof.
    intros. induction H0.
        - inversion H.
        - induction H.
            + subst. intuition.
            + apply IHMax in H. rewrite H. intuition.
Qed.

Theorem T2:
    forall (f : nat) (m : nat) (l : list nat),
        hd_error l = value f ->
        Max l m ->
 f <= m + 1.
Proof.
    intros f m.
    induction l; simpl; intros.
        - discriminate.
        - inversion H. subst. eapply T1; eauto.
          simpl. left. reflexivity.
Qed.

Print T1.
Check Max_ind.
Check nat_ind.
Check nat_rec.

Definition t1 : forall (n m : nat) (l : list nat), In n l -> Max l m -> n <= m + 17 := fun (n m : nat) (l : list nat) (H : In n l) (H0 : Max l m) =>
Max_ind
  (fun (l0 : list nat) (m0 : nat) (_ : Max l0 m0) => In n l0 -> n <= m0 + 17)
  (fun H1 : In n nil =>
   (fun H2 : n <= 0 + 17 => H2) match H1 return (n <= 0 + 17) with
                                end)
  (fun (l0 : list nat) (n0 m0 : nat) (_ : Max l0 n0)
     (IHMax : In n l0 -> n <= n0 + 17) (H2 : In n (m0 :: l0)) =>
   or_ind
     (fun H3 : m0 = n =>
      eq_ind_r (fun m1 : nat => n <= max n0 m1 + 17)
        (le_plus_trans n (max n0 n) 17 (PeanoNat.Nat.le_max_r n0 n)) H3)
     (fun H3 : In n l0 =>
      (fun H4 : n <= n0 + 17 =>
       (fun H5 : n0 + 17 <= max n0 m0 + 17 =>
        (fun lemma : n <= n0 + 17 =>
         Morphisms.trans_co_eq_inv_impl_morphism
           RelationClasses.PreOrder_Transitive n (n0 + 17) lemma
           (max n0 m0 + 17) (max n0 m0 + 17)
           (Morphisms.eq_proper_proxy (max n0 m0 + 17))) H4 H5)
         (plus_le_compat_r n0 (max n0 m0) 17 (PeanoNat.Nat.le_max_l n0 m0)))
        (IHMax H3)) H2) l m H0 H.

Definition t1' : forall (n m : nat) (l : list nat), In n l -> Max l m -> n <= m := fun (n m : nat) (l : list nat) (H : In n l) (H0 : Max l m) =>
Max_ind
  (fun (l0 : list nat) (m0 : nat) (_ : Max l0 m0) => In n l0 -> n <= m0)
  (fun H1 : In n nil =>
   (fun H2 : n <= 0 => H2) match H1 return (n <= 0) with
                           end)
  (fun (l0 : list nat) (n0 m0 : nat) (_ : Max l0 n0)
     (IHMax : In n l0 -> n <= n0) (H2 : In n (m0 :: l0)) =>
   or_ind
     (fun H3 : m0 = n =>
      eq_ind_r (fun m1 : nat => n <= max n0 m1) (PeanoNat.Nat.le_max_r n0 n) H3)
     (fun H3 : In n l0 =>
      (fun H4 : n <= n0 =>
       (fun H5 : n0 <= max n0 m0 =>
        (fun lemma : n <= n0 =>
         Morphisms.trans_co_eq_inv_impl_morphism
           RelationClasses.PreOrder_Transitive n n0 lemma (max n0 m0)
           (max n0 m0) (Morphisms.eq_proper_proxy (max n0 m0))) H4 H5)
         (PeanoNat.Nat.le_max_l n0 m0)) (IHMax H3)) H2) l m H0 H.
 
Definition t2 : forall (n m : nat) (l : list nat), hd_error l = value n -> Max l m -> n <= m + 17 := fun (n m : nat) (l : list nat) =>
list_ind
  (fun l0 : list nat => hd_error l0 = value n -> Max l0 m -> n <= m + 17)
  (fun (H : error = value n) (_ : Max nil m) =>
   (fun H1 : False => (fun H2 : False => False_ind (n <= m + 17) H2) H1)
     (eq_ind error
        (fun e : option nat =>
         match e with
         | Some _ => False
         | None => True
         end) I (value n) H))
  (fun (a : nat) (l0 : list nat)
     (_ : hd_error l0 = value n -> Max l0 m -> n <= m + 17)
     (H : value a = value n) (H0 : Max (a :: l0) m) =>
   (fun H1 : value n = value n -> n <= m + 17 => H1 eq_refl)
     match H in (_ = y) return (y = value n -> n <= m + 17) with
     | eq_refl =>
         fun H1 : value a = value n =>
         (fun H2 : value a = value n =>
          (fun H3 : a = n =>
           (fun H4 : a = n =>
            eq_ind_r
              (fun a0 : nat =>
               value a0 = value n -> Max (a0 :: l0) m -> n <= m + 17)
              (fun (_ : value n = value n) (H6 : Max (n :: l0) m) =>
               t1 n m (n :: l0) (or_introl eq_refl) H6) H4 H H0) H3)
            (f_equal
               (fun e : option nat =>
                match e with
                | Some n0 => n0
                | None => a
                end) H2)) H1
     end) l.
 
Definition t2' : forall (n m : nat) (l : list nat),
       hd_error l = value n -> Max l m -> n <= m + 17 := fun (n m : nat) (l : list nat) =>
list_ind
  (fun l0 : list nat => hd_error l0 = value n -> Max l0 m -> n <= m + 17)
  (fun (H : error = value n) (_ : Max nil m) =>
   (fun H1 : False => (fun H2 : False => False_ind (n <= m + 17) H2) H1)
     (eq_ind error
        (fun e : option nat =>
         match e with
         | Some _ => False
         | None => True
         end) I (value n) H))
  (fun (a : nat) (l0 : list nat)
     (_ : hd_error l0 = value n -> Max l0 m -> n <= m + 17)
     (H : value a = value n) (H0 : Max (a :: l0) m) =>
   (fun H1 : value n = value n -> n <= m + 17 => H1 eq_refl)
     match H in (_ = y) return (y = value n -> n <= m + 17) with
     | eq_refl =>
         fun H1 : value a = value n =>
         (fun H2 : value a = value n =>
          (fun H3 : a = n =>
           (fun H4 : a = n =>
            eq_ind_r
              (fun a0 : nat =>
               value a0 = value n -> Max (a0 :: l0) m -> n <= m + 17)
              (fun (_ : value n = value n) (H6 : Max (n :: l0) m) =>
               le_plus_trans n m 17
                 (t1' n m (n :: l0) (or_introl eq_refl) H6)) H4 H H0) H3)
            (f_equal
               (fun e : option nat =>
                match e with
                | Some n0 => n0
                | None => a
                end) H2)) H1
     end) l.
