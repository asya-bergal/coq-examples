Require Import NAxioms NProperties OrdersFacts.
Require Import Coq.Arith.Mult.
Require Import ZArith.

Fixpoint sum_up_to (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => n + sum_up_to n'
  end.

Lemma sum_up_to_succ (n : nat) : sum_up_to (S n) = (S n) + sum_up_to n.
  simpl.
  reflexivity.
Qed.

(* We use multiplication instead of the standard division definition *)
(* because it's easier to reason about multiplication. *)
Theorem sum_nats : forall n, sum_up_to n * 2 = (S n) * n.
Proof.
  induction n.
  (* Base case *)
  - simpl.
    reflexivity.
  (* Inductive case *)
  - Show.
    rewrite sum_up_to_succ.
    rewrite PeanoNat.Nat.mul_add_distr_r.
    rewrite IHn.
    rewrite <- PeanoNat.Nat.mul_add_distr_l.
    intuition.
Qed.
