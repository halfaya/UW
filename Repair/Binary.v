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
