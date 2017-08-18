(*
Translation of <= transitivity example from Agda to Gallina.
*)

(*
Coq version of <=, from the standard library:

Inductive le (n : nat) : nat -> Prop :=
  | le_n : n <= n
  | le_S : forall m : nat, n <= m -> n <= S m


"n <= m" := le n m   : nat_scope

The definition in Agda (of the Coq version) is the follows:

data _≤_ (n : ℕ) : ℕ → Set where
  ln :                   n ≤ n
  ls : {m : ℕ} → n ≤ m → n ≤ suc m
*)

(* Agda's default definition of <= from its library.
   Note that it also provides an alternative definition
   that is the same as Coq's.

data _≤a_ : ℕ → ℕ → Set where
  lz : {n : ℕ}            → zero  ≤a n
  ls : {m n : ℕ} → m ≤a n → suc m ≤a suc n
 *)

Reserved Notation "x <=a y" (at level 70, no associativity).

Inductive lea : nat -> nat -> Prop :=
  | lea_z : forall n : nat, 0 <=a n
  | lea_S : forall m n : nat, m <=a n -> S m <=a S m
where "n <=a m" := (lea n m) : nat_scope.                                  

(* Map from <= to <=a

≤asuc : {m n : ℕ} → m ≤a n → m ≤a suc n
≤asuc lz     = lz
≤asuc (ls x) = ls (≤asuc x)

≤→≤a : {m n : ℕ} → m ≤ n → m ≤a n
≤→≤a {zero}  _      = lz
≤→≤a {suc m} ln     = ls (≤→≤a {m} ln)
≤→≤a {suc m} (ls x) = ≤asuc (≤→≤a {suc m} x)
 *)

(* This kind of pattern matching doesn't seem to work for Gallina
Fixpoint leaS (m n : nat) (p : m <=a n) {struct p}: m <=a S n :=
  match p with
  | lea_z n     => lea_z (S n)
  | lea_S m n x => lea_S m (S n) (leaS m n x)
  end.

Fixpoint leToLea (m n : nat, p : m <= n) : m <=a n :=
  match m with
  | 0   => leaz
  | S m => match p with
          | le_n => lea_S (leToLea m n le_n)
          | le_S => (* to be done *)
          end.
  end.             
 *)

(* Following this, define the reverse map <=a to <=.
   Then prove transitivity for the Coq <= (should already be in the standard library).
   Then prove transitivity for the Agda <= by converting the two hypotheses to the coq version,
   running Coq <= transitivity, and converting the result back to the Agda version.
*)
