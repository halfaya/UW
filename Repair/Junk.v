Require Import Coq.Lists.List.
Require Import Coq.Program.Basics.

Print  eq_rect_r.

Definition x_eq_rect : forall (A : Type) (x : A) (P : A -> Type),
       P x -> forall y : A, x = y -> P y := 
fun (A : Type) (x : A) (P : A -> Type) (f : P x) (y : A) (e : x = y) =>
match e in (_ = y0) return (P y0) with
| eq_refl => f
end.

Definition x_eq_rect_r: forall (A : Type) (x : A) (P : A -> Type),
       P x -> forall y : A, y = x -> P y := 
fun (A : Type) (x : A) (P : A -> Type) (H : P x) (y : A) (H0 : y = x) =>
x_eq_rect A x (fun y0 : A => P y0) H y (eq_sym H0).

(*
Definition y_eq_rect_r: forall (A : Type) (x : A) (P : A -> Type),
       P x -> forall y : A, y = x -> P y := 
fun (A : Type) (x : A) (P : A -> Type) (f : P x) (y : A) (e : y = x) =>
match e in (y0 = _) return (P y0) with
| eq_refl => f
end.
*)

Print eq_sym.

Definition alices : (fun x => _) 0 = 0 := eq_refl.

Print alices.

(* Definition bobs : _ 0 = 0 := eq_refl. *)

(* Definition alices2 : forall (x y z : nat), In x ((y :: nil) ++ (z :: x :: nil)) := fun x y z => in_eq x nil.

Print alices2. *)

Print eq_refl.

Theorem ea : forall (A B C : Type) (f : A -> B) (g : B -> C), compose g f = compose g  (fun x => f x).
Proof. intros. reflexivity. Qed.

Print ea.

Definition eta_equality : forall (A B : Type) (f : A -> B), f = f :=
                              eq_refl.