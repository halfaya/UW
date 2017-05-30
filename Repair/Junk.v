Require Import Coq.Lists.List.

Definition alices : (fun x => _) 0 = 0 := eq_refl.

Print alices.

(* Definition bobs : _ 0 = 0 := eq_refl. *)

Definition alices2 : forall (x y z : nat), In x ((y :: nil) ++ (z :: x :: nil)) := fun x y z => in_eq x nil.

Print alices2.
