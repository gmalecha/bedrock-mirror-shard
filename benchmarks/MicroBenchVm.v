Require Import Heaps.
Require Import SepExpr.
Require Import EquivDec.
Require Import List.

Set Implicit Arguments.

Module SepExprTests (B : Heap) (ST : SepTheoryX.SepTheoryXType B).
  Module Sep := SepExpr.SepExpr B ST.

  (** Just a test separation logic predicate **)
  Section Tests.
    Variable f : forall a b, nat -> ST.hprop a b nil.
    Variable h : forall a b, nat -> ST.hprop a b nil.
    Variable i : forall a b, nat -> ST.hprop a b nil.
    Variable g : bool -> nat -> nat -> nat.

    Ltac isConst e :=
      match e with
        | true => true
        | false => true
        | O => true
        | S ?e => isConst e
        | _ => false
      end.

    Definition nat_type : type :=
      {| Impl := nat 
       ; Eq := fun x y => match equiv_dec x y with
                            | left pf => Some pf
                            | _ => None 
                          end
       |}.


    Fixpoint all a b (f : nat -> ST.hprop a b nil) (n : nat) : ST.hprop a b nil :=
      match n with
        | 0 => f 0
        | S n => ST.star (f (S n)) (all f n)
      end.

    Fixpoint allb a b (f : nat -> ST.hprop a b nil) (n m : nat) : ST.hprop a b nil :=
      match n with
        | 0 => f m
        | S n => ST.star (f (m - S n)) (allb f n m)
      end.

    Opaque ST.himp ST.star ST.emp ST.inj ST.ex.

    Ltac go := Sep.sep isConst (nat_type :: nil) ltac:(vm_compute).

    Goal let N := 1 in
      forall a b c, @ST.himp a b c 
      (ST.star (allb (@h a b) N N) (allb (@f a b) N N))
      (ST.star (all (@f a b) N) (all (@h a b) N)).
    Proof.
      simpl; intros.
      Time go. reflexivity.
    Time Qed.

    Goal let N := 5 in
      forall a b c, @ST.himp a b c 
      (ST.star (allb (@h a b) N N) (allb (@f a b) N N))
      (ST.star (all (@f a b) N) (all (@h a b) N)).
    Proof.
      simpl; intros.
      Time go. reflexivity.
    Time Qed.

    Goal let N := 10 in
      forall a b c, @ST.himp a b c 
      (ST.star (allb (@h a b) N N) (allb (@f a b) N N))
      (ST.star (all (@f a b) N) (all (@h a b) N)).
    Proof.
      simpl; intros.
      Time go. reflexivity.
    Time Qed.

    Goal let N := 15 in
      forall a b c, @ST.himp a b c 
      (ST.star (allb (@h a b) N N) (allb (@f a b) N N))
      (ST.star (all (@f a b) N) (all (@h a b) N)).
    Proof.
      simpl; intros.
      Time go. reflexivity.
    Time Qed.

    Goal let N := 20 in
      forall a b c, @ST.himp a b c 
      (ST.star (allb (@h a b) N N) (allb (@f a b) N N))
      (ST.star (all (@f a b) N) (all (@h a b) N)).
    Proof.
      simpl; intros.
      Time go. reflexivity.
    Time Qed.

(*
  Goal forall a b c, @ST.himp a b c 
    (ST.star (all (@h a b) N) (allb (@f a b) M M))
    (ST.star (all (@f a b) M) (all (@h a b) N)).
  Proof.
    simpl all. simpl allb. unfold N, M.
    intros.
    Time Sep.sep isConst (nat_type :: nil). reflexivity.
  Time Qed.

  Goal forall a b c, @ST.himp a b c 
    (ST.star (all (@h a b) N) (all (@f a b) M))
    (ST.star (all (@f a b) M) (all (@h a b) N)).
  Proof.
    simpl all. simpl allb. unfold N, M.
    intros.
    Time Sep.sep isConst (nat_type :: nil). reflexivity.
  Time Qed.

  Goal forall a b c, @ST.himp a b c 
    (ST.star (all (@f a b) M) (all (@h a b) N))
    (ST.star (all (@f a b) M) (all (@h a b) N)).
  Proof.
    simpl all. simpl allb. unfold N, M.
    intros.
    Time Sep.sep isConst (nat_type :: nil). reflexivity.
  Time Qed.
*)


(*
    Goal forall a b c, @ST.himp a b c (ST.star (allb (@h a b) 15 15) (allb (@f a b) 15 15)) (ST.star (all (@f a b) 15) (all (@h a b) 15)).
      simpl all. simpl allb.
      intros. Time Sep.sep isConst (nat_type :: nil). reflexivity.
    Qed.

    Goal forall a b c x y, @ST.himp a b c (f _ _ (g y (x + x) 1)) (f _ _ 1).
      intros. Time Sep.sep isConst (nat_type :: nil).
    Abort.

    Goal forall a b c, @ST.himp a b c 
      (ST.star (f _ _ 2) (f _ _ 1))
      (f _ _ 1).
      intros. Time Sep.sep isConst (nat_type :: nil).
    Abort.

    Goal forall a b c, @ST.himp a b c 
      (ST.ex (fun y : nat => ST.ex (fun x : bool => ST.star (f _ _ (g x 1 2)) (f _ _ 1) )))
      (f _ _ 1).
      intros. Time Sep.sep isConst (nat_type :: nil).
    Abort.

    Goal forall a b c, @ST.himp a b c 
      (ST.ex (fun y : nat => f _ _ y))
      (f _ _ 1).
      intros. Time Sep.sep isConst (nat_type :: nil).
    Abort.
*)
  End Tests.

End SepExprTests.