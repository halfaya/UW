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

Print bin_to_nat_c_pres_incr'.

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

(*
Note that the two theorems are more or less isomoorphic modulo the lemmas, so concentrate on the difference between the lemmas.

S_S_plus is more general than S_double but it is used in the above theorems only with a=b; that special case (S_S_plus_same) is isomorphic to S_double.
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

(* Term for S_double *)
Definition S_double_term : forall a : nat, double (S a) = S (S (double a)) := 
fun a : nat =>
nat_ind (fun a0 : nat => double (S a0) = S (S (double a0))) eq_refl
  (fun (a0 : nat) (IHa : double (S a0) = S (S (double a0))) =>
   eq_ind (double (S a0)) (fun n : nat => S (S n) = S (S n)) eq_refl
          (S (S (double a0))) IHa) a.

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
Term for S_double'.
Note that this isomorphism with S_S_plus_same_term is now impossible to see.
*)
Definition S_double'_term : forall a : nat, double (S a) = S (S (double a)) :=
  fun a : nat => eq_refl.
