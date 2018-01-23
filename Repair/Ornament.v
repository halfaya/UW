Definition extend (n : nat) (A : Set) : Set :=
  match n with
  | O   => unit
  | S _ => A
  end.

Inductive one : Type := star : one.

Definition extendT (n : nat) (A : Type) : Type :=
  match n with
  | O   => one
  | S _ => A
  end.

Definition patch1 (n : nat) (A : Set) : extend n A -> list A :=
  match n with
  | O   => fun (_ : unit) => nil
  | S_  => fun (a : A)    => cons a nil
  end.

Definition patchT1 (n : nat) (A : Type) : extendT n A -> list A :=
  match n with
  | O   => fun (_ : one) => nil
  | S_  => fun (a : A)   => cons a nil
  end.
