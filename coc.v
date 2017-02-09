(* Formalization of the Calculus of Constructions inside of Coq *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Arith.

Infix "==n" := eq_nat_dec (no associativity, at level 50).

(* Simple finite map of nat to nat for reasoning amount alpha renaming of variables. *)
Definition natmap: Type := list (nat * nat).

Print option.

Fixpoint find (k: nat) (m: natmap) :=
match m with
| nil => None
| kv :: m' => if fst kv ==n k 
                then Some (snd kv)
                else find k m'
end.

(* Notation "x |-> y" := (pair x y) (at level 60, no associativity). *)
(* Notation "[ ]" := nil. *)
(* Notation "[ p , .. , r ]" := (cons p .. (cons r nil) .. ). *)

(* minimally use dependent types, because this is coq *)
Inductive term : Type :=
| cType : term
| cProp : term
| cVar (_:nat) : term
| cApp (_:term) (_:term) : term
| cFun (_:term) (_:term) (_:term) : term
| cForall (_:term) (_:term) (_:term) : term.

(* Definition hasType := prod term term. *)

Inductive hasType :=
  | HasType (t1 t2 : term).

Delimit Scope coc_scope with coc.

Notation "A : B" := (HasType A B) (at level 50) : coc_scope.

(* Substitute term N for the variable parametrixed by n in term B. Assume everything is properly alpha renamed in this function. *)
(* B(x := N) *)
Fixpoint substitute (B : term) (n : nat) (N : term) : term :=
  match B with
  | cVar n' => if (n' ==n n) then N else B
  | cApp func arg => cApp (substitute func n N) (substitute arg n N)
  | cFun x A t => cFun x (substitute A n N) (substitute t n N)
  | cForall x A t => cForall x (substitute A n N) (substitute t n N)
  | _ => B
  end.

Fixpoint beta_reduce (t : term) : term :=
  match t with
  | cApp (cFun (cVar n) A t) N => substitute t n N
  | cFun x A B => cFun x (beta_reduce A) (beta_reduce B)
  | cForall x A B => cForall x (beta_reduce A) (beta_reduce B)
  | _ => t
  end.

Fixpoint alpha_normalize' (t : term) (n : nat) (m : natmap) : term * nat * natmap :=
  match t with
  | cVar n' => match (find n' m) with
              | Some v => (cVar v, n, m)
              | None => (cVar n, S n, (n', n) :: m)
              end
  | cApp func arg => let '(func', n', m') := alpha_normalize' func n m in
                    let '(arg', n'', m'') := (alpha_normalize' arg n' m') in
                    (cApp func' arg', n'', m'')
  | cFun x A B => let '(x', n', m') := alpha_normalize' x n m in
                 let '(A', n'', m'') := alpha_normalize' A n' m' in
                 let '(B', n''', m''') := alpha_normalize' B n'' m'' in
                 (cFun x' A' B', n''', m''')
  | cForall x A B => let '(x', n', m') := alpha_normalize' x n m in
                    let '(A', n'', m'') := alpha_normalize' A n' m' in
                    let '(B', n''', m''') := alpha_normalize' B n'' m'' in
                    (cForall x' A' B', n''', m''')
  | _ => (t, n, m)
  end.

(* Alpha normalize takes in the first fresh index it should start renaming variables to *)
Definition alpha_normalize (t : term) (n : nat) : term := fst (fst (alpha_normalize' t n [])).

Fixpoint fresh_var (t : term) : nat :=
  match t with
    | cVar n => S n
    | cApp func arg => max (fresh_var func) (fresh_var arg)
    | cFun x A B => max (max (fresh_var x) (fresh_var A)) (fresh_var B)
    | cForall x A B => max (max (fresh_var x) (fresh_var A)) (fresh_var B)
    | _ => 0
  end.

Definition beta_eq (t1 t2 : term) : Prop :=
  let n := max (fresh_var t1) (fresh_var t2) in
  alpha_normalize (beta_reduce t1) n = alpha_normalize (beta_reduce t2) n.

Infix "=b" := beta_eq (no associativity, at level 50) : coc_scope.

Reserved Notation "A |- B" (at level 95).
  (* TODO: Guarantee that x is fresh in A in 2, in 4 variables of N should be disjoint with variables of B, freshness constraints all over the damn place*)
Inductive judgement : list hasType -> hasType -> Prop :=
| introduction : forall (gamma : list hasType),
    (gamma |- cProp : cType)%coc
| extra_p : forall (gamma : list hasType) (A x: term),
    (gamma |- A : cProp ->
    x : A :: gamma |- x : A)%coc
| extra_t : forall (gamma : list hasType) (A x: term),
    (gamma |- A : cType ->
    x : A :: gamma |- x : A)%coc
| lambda_fun_p : forall (gamma : list hasType) (A B t K: term) (n : nat),
    (cVar n : A :: gamma |- t : B ->
    cVar n : A :: gamma |- B : cProp ->
    gamma |- cFun (cVar n) A t : cForall (cVar n) A B)%coc
| lambda_fun_t : forall (gamma : list hasType) (A B t K: term) (n : nat),
    (cVar n : A :: gamma |- t : B ->
    cVar n : A :: gamma |- B : cType ->
    gamma |- cFun (cVar n) A t : cForall (cVar n) A B)%coc
| lambda_forall_pp : forall (gamma : list hasType) (A B t K: term) (n : nat),
    (cVar n : A :: gamma |- t : B ->
    cVar n : A :: gamma |- B : cProp ->
    gamma |- cForall (cVar n) A B : cProp)%coc
| lambda_forall_pt : forall (gamma : list hasType) (A B t K: term) (n : nat),
    (cVar n : A :: gamma |- t : B ->
    cVar n : A :: gamma |- B : cProp ->
    gamma |- cForall (cVar n) A B : cType)%coc
| lambda_forall_tp : forall (gamma : list hasType) (A B t K: term) (n : nat),
    (cVar n : A :: gamma |- t : B ->
    cVar n : A :: gamma |- B : cType ->
    gamma |- cForall (cVar n) A B : cProp)%coc
| lambda_forall_tt : forall (gamma : list hasType) (A B t K: term) (n : nat),
    (cVar n : A :: gamma |- t : B ->
    cVar n : A :: gamma |- B : cType ->
    gamma |- cForall (cVar n) A B : cType)%coc
| eval : forall (gamma : list hasType) (M N A B MN: term) (n : nat),
    (gamma |- M : cForall (cVar n) A B ->
    gamma |- N : A ->
    gamma |- MN : substitute B n N)%coc
| equiv_p : forall (gamma : list hasType) (M A B: term),
    (gamma |- M : A ->
    A =b B ->
    [] |- B : cProp ->
    gamma |- M : B)%coc
| equiv_t : forall (gamma : list hasType) (M A B: term),
    (gamma |- M : A ->
    A =b B ->
    [] |- B : cType ->
    gamma |- M : B)%coc
where "A |- B" := (judgement A B) : coc_scope.

(* Notation "A |- B" := (judgement A B) (at level 95) : coc_scope. *)

