(* Formalization of the Calculus of Constructions inside of Coq *)
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Arith.

Infix "==n" := eq_nat_dec (no associativity, at level 50).

(* False is forall T, T. (produces thing of type T for any T), exfalso implemented this way *)
(* coq examples: dependent types lists vs list parametrized by length, writing append function, head vs head with proof *)

(* Definition head_with_proof T (l : list T) (H : l <> []) : T. *)
(*   destruct l as [_ | hd tl]. *)
(*   destruct (H eq_refl). *)
(*   exact t. *)
(* Defined. *)

Inductive var : nat -> Set :=
| Var : forall n, var n.

Inductive termType : Type :=
| ctype
| cprop
| cvar (_ : nat)
| capp
| cfun
| cforall.

(* maximally use dependent types, because this is coq and why the fuck not *)
Inductive term : termType -> Type :=
| cType : term ctype
| cProp : term cprop
| cVar {n} (_ :var n) : term (cvar n)
| cApp {c} (_:term cfun) (_:term c) : term capp
| cFun {c1 c2 n} (_:term (cvar n)) (_:term c1) (_:term c2) : term cfun
| cForall {c1 c2 n} (_:term (cvar n)) (_:term c1) (_:term c2) : term cforall.

Context (hasType : forall {t T : termType}, term t -> term T -> Prop).

Delimit Scope coc_scope with coc.

Notation "A : B" := (hasType _ _ A B) (at level 50) : coc_scope.

Context (judgement : list Prop -> list Prop -> Prop).
Notation "A |- B" := (judgement A B) (at level 95) : coc_scope.

(* B(x := N) *)
Fixpoint substitute {tB tN} (B : term tB) {n} (x : term (cvar n)) (N : term tN):
  term match B with
       | @cVar n' _ => if n' ==n n then tN else tB
       | _ => tB
       end.
  destruct B; try constructor.
  destruct (n0 ==n n).
  exact N.
  exact (cVar v).
  refine (cApp _ _).
  assert (
      match B1 with
      | cType => cfun
      | cProp => cfun
      | @cVar n' _ => if n' ==n n then tN else cfun
      | cApp _ _ => cfun
      | cFun _ _ _ => cfun
      | cForall _ _ _ => cfun
      end = cfun).
  destruct B1.

  refine (substitute cfun tN B1 n x N).

  exact (cApp (substitute c1 tN B1 n x N) (substitute c2 tN B2 n x N)).
  (* TODO: ask peter about this *)
  exact (cFun B1 (substitute c1 tN B2 n x N) (substitute c2 tN B3 n x N)).
  exact (cForall B1 (substitute c1 tN B2 n x N) (substitute c2 tN B3 n x N)).

  match B as t' in (term t) return (term match t' with
                                         | @cVar n' _ => if n' ==n n then tN else t
                                         | _ => t
                                         end) with
  | cType => cType
  | cProp => cProp
  | @cVar n' v => let s := n' ==n n in if s as s0 return (term (if s0 then tN else cvar n')) then N else cVar v
  | cApp B1 B2 => cApp (substitute B1 x N) (substitute B2 x N)
  | cFun B1 B2 B3 => cFun B1 (substitute B2 x N) (substitute B3 x N)
  | cForall B1 B2 B3 => cForall B1 (substitute B2 x N) (substitute B3 x N)
  end.

(* Fixpoint beta_reduce {T} (t: term T) : *)
(*   term match t with *)
(*        | cApp func args =>  *)
(*          match func with *)
(*          |  *)
(*          | _ => T *)

(*        | _ => T *)
(*        end. *)
  


  (* application lambda thing of type A *)

  (* TODO: Guarantee that x is fresh in A in 2, in 4 variables of N should be disjoint with variables of B, freshness constraints all over the damn place*)
Axiom (introduction : forall (gamma : list Prop) (P : term cprop) (T : term ctype), 
          (gamma |- [P : T])%coc).

Axiom (weakening_type : forall (gamma : list Prop) {tA} (A : term tA) (K : term ctype) {n} (x : term (cvar n)),
          (x : A :: gamma |- [x : A])%coc).

Axiom (weakening_prop : forall (gamma : list Prop) {t} (A : term t) (K : term cprop) {n} (x : term (cvar n)),
          (x : A :: gamma |- [x : A])%coc).

(* TODO : t is an arbitrary term, loloops *)
Axiom (lambda_type : forall (gamma : list Prop) {tA tB} (A : term tA) (B : term tB) {n1 n2} (x : term (cvar n1)) (t : term (cvar n2)) (K : term ctype),
          n1 <> n2 ->
          (x : A :: gamma |- [t : B ; B : K])%coc ->
          (gamma |- [cFun x A t : cForall x A B ; cForall x A B : K])%coc).

Axiom (lambda_prop : forall (gamma : list Prop) {tA tB} (A : term tA) (B : term tB) {n1 n2} (x : term (cvar n1)) (t : term (cvar n2)) (K : term cprop),
          n1 <> n2 ->
          (x : A :: gamma |- [t : B ; B : K])%coc ->
          (gamma |- [cFun x A t : cForall x A B ; cForall x A B : K])%coc).

Axiom (eval : forall (gamma : list Prop) {tM tN tA tB} (M : term tM) (N : term tN) (A : term tA) (B : term tB) {n} (x : term (cvar n)) (MN : term match B with
       | cType => tB
       | cProp => tB
       | @cVar n' _ => if n' ==n n then tN else tB
       | cApp _ _ => tB
       | cFun _ _ _ => tB
       | cForall _ _ _ => tB
       end),
          (gamma |- [M : cForall x A B])%coc ->
          (gamma |- [N : A])%coc ->
          (gamma |- [MN : substitute B x N])%coc).
