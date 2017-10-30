Inductive bin : Type :=
  | B0  : bin
  | B2  : bin -> bin
  | B21 : bin -> bin.

Fixpoint incr (n : bin) : bin :=
  match n with
  | B0     => B21 B0
  | B2 n'  => B21 n'
  | B21 n' => B2 (incr n')
  end.

Fixpoint bin_to_nat_b (n : bin) : nat :=
  match n with
  | B0     => O
  | B2 n'  => (bin_to_nat_b n') + (bin_to_nat_b n')
  | B21 n' => S ((bin_to_nat_b n') + (bin_to_nat_b n'))
  end.

Fixpoint bin_to_nat' (n : bin) : nat :=
  match n with
  | B0     => O
  | B2 n'  => (bin_to_nat' n') + (bin_to_nat' n')
  | B21 n' => S ((bin_to_nat' n') + (bin_to_nat' n'))
  end.

Definition patch (P : nat -> Prop) (n0 : bin) (H : P (bin_to_nat_b n0)) :
                  P (bin_to_nat' n0) :=
  eq_ind
    (bin_to_nat_b n0)
    P
    H
    (bin_to_nat' n0)
    eq_refl.

Definition t (b : bin) : bin_to_nat_b b = bin_to_nat' b := eq_refl.

Theorem t' (b : bin) : bin_to_nat_b b = bin_to_nat' b.
Proof.
  reflexivity.
Qed.

Fixpoint bin_to_nat_a (b: bin) : nat :=
  match b with
  | B0 => O
  | B2 b' => 2 * (bin_to_nat_a b')
  | B21 b' => 1 + 2 * (bin_to_nat_a b')
  end.
  
(*
Don't typecheck.

Definition t' (b : bin) : bin_to_nat_a b = bin_to_nat b + 0 :=
  plus_n_O (bin_to_nat b).


Definition patch_a (P : nat -> Prop) (n0 : bin) (H : P (bin_to_nat_a n0)) :
                  P (bin_to_nat_b n0 + 0) :=
  eq_ind
    (bin_to_nat_a n0)
    P
    H
    (bin_to_nat_b n0 + 0)
    (plus_n_O (bin_to_nat_b n0)).
*)

Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n => S (S (double n))
  end.

Fixpoint bin_to_nat_c (b: bin) : nat :=
  match b with
  | B0 => O
  | B2 b' => double (bin_to_nat_c b')
  | B21 b' => S (double (bin_to_nat_c b'))
  end.

Fixpoint bin_to_nat_d (b: bin) : nat :=
  match b with
  | B0 => O
  | B2 b' => 2 * (bin_to_nat_a b')
  | B21 b' => 2 * (bin_to_nat_a b') + 1
  end.

Fixpoint bin_to_nat_e (b: bin) : nat :=
  match b with
  | B0 => O
  | B2 b' => (bin_to_nat_a b') * 2
  | B21 b' => 1 + (bin_to_nat_a b') * 2
  end.

(* Theorems *)

Lemma S_S_plus : forall a b : nat,
  S a + S b = S (S (a + b)).
Proof.
  intros a b.
  induction a.
  reflexivity.
  simpl. rewrite <- IHa. reflexivity. Qed.

(* This proof fails.
   The problem is that we have to do induction on
   both instances of a at once, whereas we want
   to induct on the first and hold the second fixed.
Lemma S_S_same : forall a : nat,
  S a + S a = S (S (a + a)).
Proof.
  intros a.
  induction a.
  reflexivity.
  simpl. rewrite <- IHa. reflexivity. Qed.
 *)

Definition S_S_plus_same : forall a : nat, S a + S a = S (S (a + a)) :=
  fun a => S_S_plus a a.

Lemma S_double : forall a : nat,
  double (S a) = S (S (double a)).
Proof.
  intros a.
  induction a.
  reflexivity.
  simpl. rewrite <- IHa. reflexivity.
Qed.

(* The above proof however is superfluous, as the
   lemma is true definitionally. *)
Lemma S_double' : forall a : nat,
    double (S a) = S (S (double a)).
Proof. reflexivity. Qed.

Theorem bin_to_nat_b_pres_incr : forall b : bin,
    bin_to_nat_b (incr b) = S (bin_to_nat_b b).
Proof.
  intros b.
  induction b as [|b'|b'].
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> IHb'.
    assert (H : forall a b : nat, S a + S b = S (S (a + b))).
    + intros a b. apply S_S_plus.
    + rewrite -> H.
      reflexivity.
Qed.

Theorem bin_to_nat_c_pres_incr : forall b : bin,
    bin_to_nat_c (incr b) = S (bin_to_nat_c b).
Proof.
  intros b.
  induction b as [|b'|b'].
  - reflexivity.
  - reflexivity.
  - simpl.
    rewrite -> IHb'.
    assert (H : forall a : nat, double (S a) = S (S (double a))).
    + intros a. apply S_double.
    + rewrite -> H.
      reflexivity.
Qed.

(* The extra lemma is superfluous because it holds
   definitionally. Here is the better proof. *)
Theorem bin_to_nat_c_pres_incr' : forall b : bin,
    bin_to_nat_c (incr b) = S (bin_to_nat_c b).
Proof.
  intros b.
  induction b as [|b'|b'].
  - reflexivity.
  - reflexivity.
  - simpl. rewrite -> IHb'. reflexivity.
Qed.

(* Term for bin_to_nat_b_pres_incr *)
Definition bin_to_nat_b_pres_incr_term : forall b : bin, bin_to_nat_b (incr b) = S (bin_to_nat_b b) :=
fun b : bin =>
bin_ind (fun b0 : bin => bin_to_nat_b (incr b0) = S (bin_to_nat_b b0)) eq_refl
  (fun (b' : bin) (_ : bin_to_nat_b (incr b') = S (bin_to_nat_b b')) =>
   eq_refl)
  (fun (b' : bin) (IHb' : bin_to_nat_b (incr b') = S (bin_to_nat_b b')) =>
   eq_ind_r (fun n : nat => n + n = S (S (bin_to_nat_b b' + bin_to_nat_b b')))
     (let H :=
        (fun a b0 : nat => S_S_plus a b0)
        :
        forall a b0 : nat, S a + S b0 = S (S (a + b0)) in
      eq_ind_r (fun n : nat => n = S (S (bin_to_nat_b b' + bin_to_nat_b b')))
               eq_refl (H (bin_to_nat_b b') (bin_to_nat_b b'))) IHb') b.


(* Term for bin_to_nat_c_pres_incr *)
Definition bin_to_nat_c_pres_incr_term : forall b : bin, bin_to_nat_c (incr b) = S (bin_to_nat_c b) := 
fun b : bin =>
bin_ind (fun b0 : bin => bin_to_nat_c (incr b0) = S (bin_to_nat_c b0))
  eq_refl
  (fun (b' : bin) (_ : bin_to_nat_c (incr b') = S (bin_to_nat_c b')) =>
   eq_refl)
  (fun (b' : bin) (IHb' : bin_to_nat_c (incr b') = S (bin_to_nat_c b')) =>
   eq_ind_r (fun n : nat => double n = S (S (double (bin_to_nat_c b'))))
     (let H :=
        (fun a : nat => S_double a)
        :
        forall a : nat, double (S a) = S (S (double a)) in
      eq_ind_r (fun n : nat => n = S (S (double (bin_to_nat_c b')))) eq_refl
               (H (bin_to_nat_c b'))) IHb') b.

(* The term for the better proof bin_to_nat_c_pres_incr' no longer
   has a clear correspondence to that for bin_to_nat_b_pres_incr.

   Strangely the term generated by Coq from the lemma fails to typecheck.
   Some sort of Coq bug?  I haven't investigated.

Definition bin_to_nat_c_pres_incr'_term : forall b : bin, bin_to_nat_c (incr b) = S (bin_to_nat_c b) := 
fun b : bin =>
bin_ind (fun b0 : bin => bin_to_nat_c (incr b0) = S (bin_to_nat_c b0)) eq_refl
  (fun (b' : bin) (_ : bin_to_nat_c (incr b') = S (bin_to_nat_c b')) =>
   eq_refl)
  (fun (b' : bin) (IHb' : bin_to_nat_c (incr b') = S (bin_to_nat_c b')) =>
   eq_ind_r (fun n : nat => double n = S (S (double (bin_to_nat_c b'))))
     eq_refl IHb') b.
*)

(*
The two theorems bin_to_nat_b_pres_incr_term and
bin_to_nat_c_pres_incr_term are more or less isomorphic modulo the lemmas,
so concentrate on the difference between the lemmas.

S_S_plus is more general than S_double but it is used in the above theorems only with a=b;
that special case (S_S_plus_same) is isomorphic to S_double.
*)

(* Term for S_S_plus *)
Definition S_S_plus_term : forall a b : nat, S a + S b = S (S (a + b)) := 
fun a b : nat =>
nat_ind (fun a0 : nat => S a0 + S b = S (S (a0 + b))) eq_refl
  (fun (a0 : nat) (IHa : S a0 + S b = S (S (a0 + b))) =>
   eq_ind (S a0 + S b) (fun n : nat => S (S (a0 + S b)) = S n) eq_refl
          (S (S (a0 + b))) IHa) a.

(* Direct term for S_S_plus_same.
   Didn't work with tactics, but hand-derivable by
   specializing the term for S_S_plus'.
   Question:  Is there some way to derive this proof via tactics? *)
Definition S_S_plus_same_term : forall a : nat, S a + S a = S (S (a + a)) := 
fun a : nat =>
nat_ind (fun a0 : nat => S a0 + S a = S (S (a0 + a))) eq_refl
  (fun (a0 : nat) (IHa : S a0 + S a = S (S (a0 + a))) =>
   eq_ind (S a0 + S a) (fun n : nat => S (S (a0 + S a)) = S n) eq_refl
          (S (S (a0 + a))) IHa) a.

(*
Term for S_double.
The isomorphism with S_S_plus_same_term is clear
which implies a + a = double a
but it appears a mapping between a + a and double a
cannot be derived from this information.
 *)
Definition S_double_term : forall a : nat, double (S a) = S (S (double a)) := 
fun a : nat =>
nat_ind (fun a0 : nat => double (S a0) = S (S (double a0))) eq_refl
  (fun (a0 : nat) (IHa : double (S a0) = S (S (double a0))) =>
   eq_ind (double (S a0)) (fun n : nat => S (S n) = S (S n)) eq_refl
          (S (S (double a0))) IHa) a.

(*
Term for S_double'.
The isomorphism with S_S_plus_same_term is now impossible to see.
*)
Definition S_double'_term : forall a : nat, double (S a) = S (S (double a)) :=
  fun a : nat => eq_refl.

Set Nonrecursive Elimination Schemes.

Record int : Type :=
  mkint { intval: nat; intrange: 0 <= intval < 10 }.

Definition int_ind_term : forall P : int -> Prop,
       (forall (intval : nat) (intrange : 0 <= intval < 10),
        P {| intval := intval; intrange := intrange |}) -> 
       forall i : int, P i := 
  fun P : int -> Prop => int_rect P.

Definition int_rect_term : forall P : int -> Type,
       (forall (intval : nat) (intrange : 0 <= intval < 10),
        P {| intval := intval; intrange := intrange |}) -> 
       forall i : int, P i := 
fun (P : int -> Type)
  (f : forall (intval : nat) (intrange : 0 <= intval < 10),
       P {| intval := intval; intrange := intrange |}) 
  (i : int) =>
match i as i0 return (P i0) with
| {| intval := x; intrange := x0 |} => f x x0
end.

Definition int' : Type :=
  exists intval, 0 <= intval < 10.

(*
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> exists y, P y
 *)

Definition ex_ind_term : forall (A : Type) (P : A -> Prop) (P0 : Prop),
       (forall x : A, P x -> P0) -> (exists y, P y) -> P0 := 
fun (A : Type) (P : A -> Prop) (P0 : Prop) (f : forall x : A, P x -> P0)
  (e : exists y, P y) => match e with
                         | ex_intro _ x x0 => f x x0
                         end.

Inductive ex' (A : Type) (P : A -> Prop) : Prop :=
    ex'_intro : forall x : A, P x -> ex' A P.

Definition ex'_ind_term : forall (A : Type) (P : A -> Prop) (P0 : Prop),
       (forall x : A, P x -> P0) -> ex' A P -> P0 := 
fun (A : Type) (P : A -> Prop) (P0 : Prop) (f : forall x : A, P x -> P0)
  (e : ex' A P) => match e with
                   | ex'_intro _ _ x x0 => f x x0
                   end.

(*
Inductive eq (A : Type) (x : A) : A -> Prop
  :=  eq_refl : x = x

eq_ind = 
fun (A : Type) (x : A) (P : A -> Prop) => eq_rect x P
     : forall (A : Type) (x : A) (P : A -> Prop),
       P x -> forall y : A, x = y -> P y

eq_rect = 
fun (A : Type) (x : A) (P : A -> Type) (f : P x) (y : A) (e : x = y) =>
match e in (_ = y0) return (P y0) with
| eq_refl => f
end
     : forall (A : Type) (x : A) (P : A -> Type),
       P x -> forall y : A, x = y -> P y
*)

Inductive eq1 (A:Type) (x:A) : A -> Prop :=
  eq1_refl : eq1 A x x.

Definition eq1_rect' : forall (A : Type) (x : A) (P : A -> Type),
       P x -> forall y : A, eq1 A x y -> P y := 
fun (A : Type) (x : A) (P : A -> Type) (f : P x) (y : A) (e : eq1 A x y) =>
match e in (eq1 _ _ y0) return (P y0) with
| eq1_refl _ _ => f
end.

Inductive eq2 (A : Type) : A -> A -> Prop :=
  eq2_refl (x : A) : eq2 A x x.

(*
Fails.

Definition eq2_rect : forall (A : Type) (P : A -> A -> Type),
       (forall x : A, P x x) -> forall y y0 : A, eq2 A y y0 -> P y y0 := 
fun (A : Type) (P : A -> A -> Type) (f : forall x : A, P x x) 
  (y y0 : A) (e : eq2 A y y0) =>
match e in (eq2 _ y1 y2) return (P y1 y2) with
| eq2_refl _ x => f x
end.
*)
    
(*
eq'_ind = 
fun (A : Type) (P : A -> A -> Prop) (f : forall x : A, P x x) 
  (y y0 : A) (e : eq' A y y0) =>
match e in (eq' _ y1 y2) return (P y1 y2) with
| eq'_refl _ x => f x
end
     : forall (A : Type) (P : A -> A -> Prop),
       (forall x : A, P x x) -> forall y y0 : A, eq' A y y0 -> P y y0
*)
