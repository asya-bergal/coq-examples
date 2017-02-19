Require Import Coq.QArith.QArith_base.

CoInductive rat_stream : Type :=
  | Cons : Q -> rat_stream -> rat_stream.

Definition hd (s : rat_stream) : Q :=
  match s with
  | Cons hd _ => hd
  end.

Definition tl (s : rat_stream) : rat_stream :=
  match s with
  | Cons _ tl => tl
  end.

Definition frob (s : rat_stream) : rat_stream :=
  match s with
    | Cons h t => Cons h t
  end.

Theorem frob_eq : forall (s : rat_stream), s = frob s.
  destruct s; reflexivity.
Qed.

Notation " 4 " := (4#1) : Q_scope.
Notation " 3 " := (3#1) : Q_scope.

CoFixpoint fourths (q : Q) : rat_stream := Cons (q / 4) (fourths (q / 4 )).

CoInductive sum : rat_stream -> Q -> Prop :=
  | Sum : forall h t q, sum t q -> sum (Cons h t) (q + h).

(* Lemma sum_cons : forall (h n: Q) (t : rat_stream), sum (Cons h t) (n + h) -> sum t n. *)
(*   Proof. *)
(*     intros. *)
(*     rewrite (frob_eq (Cons h t)) in H. *)
(*     simpl in H. *)
(*     cofix. *)

Lemma mult_sum : forall (q s n: Q), sum (fourths q) s -> sum (fourths (q * n)) (s * n).
  Proof.
    cofix.
    intros.
    destruct (fourths (q * n)).

    rewrite (frob_eq (fourths (q * n))).
    simpl.
    

(*     sum (fourths (q * n / 4)) ((s * n) - (q * n / 4)) *)

Theorem fourths_sum : forall a, sum (fourths a) (a / 3 ).
  cofix.
  intros.
  rewrite (frob_eq (fourths a)).
  simpl.
  (* assume these all make up 1/3 of the area a/4 *)
  (* 1/3 a = 1/3 (a / 4) + 1/3 (3a / 4) *)
  (* then the head has to make up 1/3 of the area (3a / 4) *)
  (* 1/3 (3a / 4) = a / 4, yay *)

  (* the first section  *)


  cofix.
  intros.
  destruct (fourths a).
  


  rewrite (frob_eq (fourths a)).
  simpl.


  (* inversion fourths_sum. *)


  (* sum (Cons (1 # 4) (fourths ((1 # 4) / 4))) (1 # 3) *)

  (* rewrite (frob_eq sum) *)
  (* assumption. *)
  (* Qed. *)
