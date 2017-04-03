Require Import ZArith.
Require Import Coq.Logic.Decidable.

Definition divides a b := exists k, b = k * a.
Definition prime p := 2 <= p /\ forall k, divides k p -> (k = 1 \/ k = p).

Lemma divides_comm : forall a b, divides a b <-> exists k, b = a * k.
  intros; cbv [divides]; firstorder; exists x; rewrite Nat.mul_comm; assumption.
Qed.

Definition divides' a b := Nat.modulo b a = 0.

Lemma divides_eq : forall a b, b <> 0 -> divides' b a <-> divides b a.
  cbv [divides']; intros; split; rewrite divides_comm; apply Nat.mod_divides; assumption.
Qed.

Infix "==n" := eq_nat_dec (no associativity, at level 50).

Theorem divides_dec : forall n m : nat, {divides n m} + {~divides n m}.
  destruct n.
  { destruct m; cbv [divides].
    { left; exists 0; omega. }
    { right; intro H; destruct H; omega. }
  }
  { intro; destruct (m mod (S n) ==n 0).
    { left; apply divides_eq; auto. }
    { right; rewrite <- divides_eq; auto. }
  }
Qed.

Fixpoint prime_decider' (n m : nat) : bool :=
  match m with
    | 0 => true
    | S m => prime_decider' n m &&
            if divides_dec (S m) n then
              if (S m ==n 1) then true else
                if (S m ==n n) then true else false
            else true
  end.

Definition prime_decider (n : nat) : bool := if (le_dec 2 n) then prime_decider' n n else false.

Ltac simpl_prime_decider :=
  match goal with
  | [ H : prime_decider' _ _ = _ |- _ ] =>
    unfold prime_decider' in H; fold prime_decider' in H;
    rewrite Bool.andb_true_iff in H; firstorder
  | [ |- prime_decider' _ _ = _ ] =>
    unfold prime_decider'; fold prime_decider';
    rewrite Bool.andb_true_iff; firstorder
  end.

Lemma prime_decider_eq_prime' : forall (n m : nat), 2 <= n -> (prime_decider' n m = true) <-> (forall k : nat, k <= m -> divides k n -> k = 1 \/ k = n).
  induction m; firstorder.
  { destruct (le_lt_eq_dec k 0); [assumption | omega | subst; omega]. }
  { destruct (le_lt_eq_dec k (S m)).
    { assumption. }
    { apply H3.
      { simpl_prime_decider. }
      { apply (lt_n_Sm_le k m l). }
      { cbv [divides]; exists x; assumption. }
    }
    { simpl_prime_decider; rewrite e in H2; destruct (divides_dec (S m) n).
      { destruct (S m ==n 1).
        { firstorder. }
        { destruct (S m ==n n); firstorder; discriminate. }
      }
      { destruct n0; cbv [divides]; exists x; assumption. }
    }
  }
  { simpl_prime_decider; destruct (divides_dec (S m) n).
    { destruct (S m ==n 1).
      { trivial. }
      { destruct (S m ==n n).
        { trivial. }
        { specialize (H0 (S m) (le_n (S m))); firstorder; trivial. }
      }
    }
    { trivial. }
  }
Qed.

Lemma le_sufficient : forall (n : nat), 2 <= n -> (forall k : nat, k <= n -> divides k n -> k = 1 \/ k = n) <-> prime n.
  intros; cbv [prime]; split.
  { intros; split.
    { assumption. }
    { intro; destruct (le_gt_dec k n).
      { specialize (H0 k l); assumption. }
      { intros; rewrite <- divides_eq in H1.
        { cbv [divides'] in H1; pose proof (Nat.mod_small n k); omega. }
        { intro; subst; omega. }
      }
    }
  }
  { firstorder. }
Qed.

Lemma prime_decider_eq_prime : forall n, (prime_decider n = true) <-> prime n.
  intros; cbv [prime_decider]; destruct (le_dec 2 n).
  { pose proof (prime_decider_eq_prime' n n l); rewrite H; apply le_sufficient; assumption. }
  { firstorder; discriminate. }
Qed.

Theorem prime_dec : forall n : nat, {prime n} + {~ prime n}.
  intros; destruct (Bool.bool_dec (prime_decider n) true) as [dec | dec];
            rewrite prime_decider_eq_prime in dec; firstorder.
Qed.

Fixpoint mult_primes_up_to' (n prod : nat) :=
  match n with
  | 0 => prod
  | S n => if prime_dec n then mult_primes_up_to' n prod * (S n) else mult_primes_up_to' n prod
  end.

Definition mult_primes_up_to (n : nat) := mult_primes_up_to' n 1.

(* Theorem find_prime_factor (n : nat) : nat. *)
(*   destruct (prime_dec n). *)
(*   exact n. *)
(*   cbv [prime] in n0. *)
(*   := *)
(*   if (prime_dec n) then n else  *)


Lemma not_prime_impl_prime_factor : forall (n : nat), 2 <= n -> ~ prime n -> exists x, divides x n /\ prime x.
Admitted.

Lemma checking_primes_sufficient : forall (n : nat), 2 <= n -> (forall k : nat, prime k -> divides k n -> k = 1 \/ k = n) <-> prime n.
  intros; split.
  { intros; split.
    { assumption. }
    { cut (forall k : nat, divides k n -> ~ ~(k = 1 \/ k = n)).
      { intros; specialize (H1 k H2); apply not_not.
        { apply dec_or; apply dec_eq_nat; assumption. }
        { assumption. }
      }
      { cut (~ exists k, divides k n /\ ~(k = 1 \/ k = n)).
        { firstorder. }
        { intro.
          destruct H1.
          destruct (prime_dec x).
          specialize (H0 x); firstorder.
          pose proof (not_prime_impl_prime_factor x).
          destruct (le_gt_dec 2 x).
          pose proof (H2 l n0).
          destruct H3.
          specialize (H0 x0).
          destruct H3.
          specialize (H0 H4 H3).

          firstorder.
          firstorder.

          specialize (H0 x).
          firstorder.

      intros.
      firstorder.
        intro; destruct H1.
      firstorder.
      destruct (divides_dec x n).
      pose proof (H1 d).
      admit.


Lemma mult_primes_up_to_plus_one_prime : forall n, prime (mult_primes_up_to n).

Theorem primes_infinite : forall n, exists p, p > n /\ prime p.
Proof.
Admitted.