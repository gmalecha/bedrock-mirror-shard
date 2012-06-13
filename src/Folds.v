Require Import List.
Require Import Reflection.

Set Implicit Arguments.
Set Strict Implicit.

Section fold_left2_opt.
  Variable T U V : Type.
  Variable F : T -> V -> U -> option U.

  Fixpoint fold_left_2_opt (ls : list T) (ls' : list V) (acc : U) : option U :=
    match ls, ls' with 
      | nil , nil => Some acc
      | x :: xs , y :: ys => 
        match F x y acc with
          | None => None
          | Some acc => fold_left_2_opt xs ys acc
        end
      | _ , _ => None
    end.
End fold_left2_opt.

Section fold_left3_opt.
  Variable T U V A : Type.
  Variable F : T -> U -> V -> A -> option A.

  Fixpoint fold_left_3_opt (ls : list T) (ls' : list U) (ls'' : list V) 
    (acc : A) : option A :=
    match ls, ls', ls'' with 
      | nil , nil , nil => Some acc
      | x :: xs , y :: ys , z :: zs => 
        match F x y z acc with
          | None => None
          | Some acc => fold_left_3_opt xs ys zs acc
        end
      | _ , _ , _ => None
    end.
End fold_left3_opt.

Section All2.
  Variable X Y : Type.
  Variable F : X -> Y -> bool.

  Fixpoint all2 (xs : list X) (ys : list Y) : bool :=
    match xs , ys with
      | nil , nil => true
      | x :: xs, y :: ys => if F x y then all2 xs ys else false
      | _ , _ => false
    end.
  
  Variable P : X -> Y -> Prop.
  Inductive Forall2 : list X -> list Y -> Prop :=
  | Forall2_nil : Forall2 nil nil
  | Forall2_cons : forall l ls r rs,
    P l r ->
    Forall2 ls rs -> Forall2 (l :: ls) (r :: rs).

  Hypothesis F_P : forall x y, F x y = true -> P x y.
  
  Theorem all2_Forall2 : forall a b,
    all2 a b = true -> Forall2 a b.
  Proof.
    induction a; destruct b; simpl; intros; try congruence; try solve [ econstructor ].
      specialize (@F_P a y). destruct (F a y); eauto; try congruence; econstructor; eauto.
  Qed.

  Hypothesis P_F : forall x y, P x y -> F x y = true.
  
  Theorem Forall2_all2 : forall a b,
    Forall2 a b -> all2 a b = true.
  Proof.
    induction 1; simpl; auto.
    rewrite P_F; auto.
  Qed.
End All2.    

Lemma Forall_app : forall A (P : A -> Prop) ls1 ls2,
  Forall P ls1
  -> Forall P ls2
  -> Forall P (ls1 ++ ls2).
Proof.
  induction 1; simpl; auto.
Qed.

Lemma all2_map_2 : forall T U V (P : T -> U -> bool) (F : V -> _) l1 l2,
  all2 P l1 (map F l2) = all2 (fun x y => P x (F y)) l1 l2.
Proof.
  clear. induction l1; destruct l2; simpl; auto.
  destruct (P a (F v)); auto.
Qed.
Lemma all2_map_1 : forall T U V (P : T -> U -> bool) (F : V -> _) l1 l2,
  all2 P (map F l1) l2 = all2 (fun x y => P (F x) y) l1 l2.
Proof.
  clear. induction l1; destruct l2; simpl; auto.
  destruct (P (F a) u); auto.
Qed.

Lemma all2_impl : forall T U (P P' : T -> U -> bool) l1 l2,
  all2 P' l1 l2 = true ->
  (forall x y, P' x y = true -> P x y = true) ->
  all2 P l1 l2 = true .
Proof.
  clear; induction l1; destruct l2; simpl; intros; auto.
  consider (P' a u); intros. rewrite H0; eauto.
Qed.
