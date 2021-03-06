(* Formalization of the Calculus of Constructions inside of Coq *)
Require Import Coq.Lists.List.
Require Import Coq.Lists.ListSet.
Import ListNotations.
Require Import Arith.

Infix "==n" := eq_nat_dec (no associativity, at level 50).

Section Natmap.
  (* Simple finite map of nat to nat for reasoning amount alpha renaming of variables. *)
  Definition natmap: Type := list (nat * nat).

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
End Natmap.

Section CoC.
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

  Scheme Equality for hasType.

  (* Compute { fun cProp ': cProp, cProp }. *)
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

  Fixpoint fresh (n : nat) (t : term) :=
    match t with
      | cVar n' => if (n ==n n') then True else False
      | cApp func arg => fresh n func /\ fresh n arg
      | cFun x A B => fresh n x /\ fresh n A /\ fresh n B
      | cForall x A B => fresh n x /\ fresh n A /\ fresh n B
      | _ => True
    end.

  Definition beta_eq (t1 t2 : term) : Prop :=
    let n := max (fresh_var t1) (fresh_var t2) in
    alpha_normalize (beta_reduce t1) n = alpha_normalize (beta_reduce t2) n.

  Definition hasTypeInSet (h : hasType) (gamma : set hasType) : Prop :=
    set_In h gamma.
  
  Definition hasTypeAddSet (h : hasType) (gamma : set hasType) : set hasType :=
    set_add hasType_eq_dec h gamma.

  Infix "=b" := beta_eq (no associativity, at level 50).
  Notation "A ': B" := (HasType A B) (at level 60).
  Notation "{ 'fun' x ': A , t }" := (cFun x A t) (at level 50, x at level 44).
  Notation "{ 'forall' x ': A , t }" := (cForall x A t) (at level 50, x at level 44).
  Reserved Notation "A '|- B" (at level 95).

  Infix "'in" := hasTypeInSet (at level 66).
  Infix "'::" := hasTypeAddSet (right associativity, at level 65).
  Notation "[ x '; y '; .. '; z ]" := (hasTypeAddSet x (hasTypeAddSet y .. (hasTypeAddSet z nil) ..)).

  (* Solution 1 *)
  (* TODO: x is fresh in A and in gamma and in K in rule 2 *)
  (* TODO: You can't apply rule 3 if x appears elsewhere in the context gamma *)

  (* Solution 2 *)
  (* No free variables in the types of things in your context gamma (no dependencies in gamma) *)

  Inductive judgement : set hasType -> hasType -> Prop :=
  | introduction : forall (gamma : set hasType),
      gamma '|- cProp ': cType
  | weakening : forall (gamma : set hasType) (h : hasType),
      h 'in gamma ->
      gamma '|- h
  | extra_p : forall (gamma : set hasType) (A x: term),
      gamma '|- A ': cProp ->
      x ': A ':: gamma '|- x ': A
  | extra_t : forall (gamma : set hasType) (A x: term),
      gamma '|- A ': cType ->
      x ': A ':: gamma '|- x ': A
  | lambda_fun_p : forall (gamma : set hasType) (A B t: term) (n : nat),
      cVar n ': A ':: gamma '|- t ': B ->
      cVar n ': A ':: gamma '|- B ': cProp ->
      gamma '|- { fun (cVar n) ': A , t } ': { forall (cVar n) ': A , B }
  | lambda_fun_t : forall (gamma : set hasType) (A B t: term) (n : nat),
      cVar n ': A ':: gamma '|- t ': B ->
      cVar n ': A ':: gamma '|- B ': cType ->
      gamma '|- { fun (cVar n) ': A , t } ': { forall (cVar n) ': A , B }
  | lambda_forall_pp : forall (gamma : set hasType) (A B: term) (n : nat),
      cVar n ': A ':: gamma '|- B ': cProp ->
      gamma '|- { forall (cVar n) ': A , B } ': cProp
  | lambda_forall_pt : forall (gamma : set hasType) (A B: term) (n : nat),
      cVar n ': A ':: gamma '|- B ': cProp ->
      gamma '|- { forall (cVar n) ': A , B } ': cType
  | lambda_forall_tp : forall (gamma : set hasType) (A B: term) (n : nat),
      cVar n ': A ':: gamma '|- B ': cType ->
      gamma '|- { forall (cVar n) ': A , B } ': cProp
  | lambda_forall_tt : forall (gamma : set hasType) (A B: term) (n : nat),
      cVar n ': A ':: gamma '|- B ': cType ->
      gamma '|- { forall (cVar n) ': A , B } ': cType
  | eval : forall (gamma : set hasType) (M N A B MN: term) (n : nat),
      gamma '|- M ': { forall (cVar n) ': A , B } ->
      gamma '|- N ': A ->
      gamma '|- MN ': substitute B n N
  | equiv_p : forall (gamma : set hasType) (M A B: term),
      gamma '|- M ': A ->
      A =b B ->
      [] '|- B ': cProp ->
      gamma '|- M ': B
  | equiv_t : forall (gamma : set hasType) (M A B: term),
      gamma '|- M ': A ->
      A =b B ->
      [] '|- B ': cType ->
      gamma '|- M ': B
  where "A '|- B" := (judgement A B).

Notation "A '|- B" := (judgement A B) (at level 95).

Section Examples.
  Theorem well_typed_prop : forall (gamma : list hasType), gamma '|- cProp ': cType.
    constructor.
  Qed.

  Ltac in_set := repeat (apply set_add_intro; try (left ; reflexivity); right).

  Theorem well_typed_id_t : forall (n : nat) (A : term),
      [A ': cType] '|- { fun (cVar n) ': A , (cVar n) } ': { forall (cVar n) ': A , A }.
    intros.
    apply lambda_fun_t.
    {
      apply extra_t; apply weakening; cbv [hasTypeInSet set_In]; intuition.
    }
    {
      apply weakening; cbv [hasTypeInSet hasTypeAddSet]; in_set; cbv [set_In]; intuition.
    }
  Qed.

  Theorem well_typed_snd_tt : forall (n1 : nat) (n2 : nat) (A B: term) (_ : n1 <> n2),
      [A ': cType '; B ': cType] '|- 
                                { fun (cVar n1) ': A , { fun (cVar n2) ': B , (cVar n2) } } ': 
                                { forall (cVar n1) ': A , { forall (cVar n2) ': B , B } }.
    intros.
    apply lambda_fun_t.
    {
      apply lambda_fun_t.
      {
        apply weakening; cbv [hasTypeInSet hasTypeAddSet]; in_set.
      }
      {
        apply weakening; in_set.
      }
    }
    apply lambda_forall_tt; apply weakening; cbv [hasTypeInSet hasTypeAddSet]; in_set.
  Qed.

  Theorem well_typed_fst_tt : forall (n1 : nat) (n2 : nat) (A B: term) (_ : n1 <> n2),
      [A ': cType '; B ': cType] '|- 
                                { fun (cVar n1) ': A , { fun (cVar n2) ': B , (cVar n1) } } ': 
                                { forall (cVar n1) ': A , { forall (cVar n2) ': B , A } }.
    intros.
    apply lambda_fun_t.
    {
      apply lambda_fun_t.
      {
        apply weakening; cbv [hasTypeInSet hasTypeAddSet]; in_set.
      }
      {
        apply weakening; in_set.
      }
    }
    apply lambda_forall_tt; apply weakening; cbv [hasTypeInSet hasTypeAddSet]; in_set.
  Qed.

  (* Proof : Impossible to produce a judgement with a double-bound variable on the right-hand side. *)
End Examples.

End CoC.

