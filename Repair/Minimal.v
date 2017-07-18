Require Import Arith NPeano.

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
Print newMinimal.
Check oldMinimal.

Definition expected (n m n0 : nat) (H : n <= Init.Nat.max n0 m) :=
   le_plus_trans n (Init.Nat.max n0 m) (S O) H.

Print le_plus_trans