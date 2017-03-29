Inductive pbool : Prop := ptrue | pfalse.
(* Attempting to define this yields the error message *)
(* "Elimination of an inductive object of sort Prop is not allowed on a predicate in sort Set *)
(* because proofs can be eliminated only to build proofs." *)
(* Apparently something inherent to Coq is that you can't eliminate Props to make everything except for Props. Why? *)

Definition pbool_to_bool (p:pbool) : bool := match p with ptrue => true | pfalse => false end.

(* Here are some more examples of this: *)

(* This doesn't work: *)
Goal (1 <= 1) -> nat.
intro.
destruct H.

(* This works: *)
Goal (1 <= 1) -> forall (x : nat), x = x.
intro.
destruct H.

(* You can only do this in Prop, not in Set, because you would get universe inconsistency *)
Check (forall P : Prop, P /\ not P -> False) : Prop.
Definition X : Prop := (forall P : Prop, P /\ not P -> False).
