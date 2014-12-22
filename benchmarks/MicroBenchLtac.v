Require Import Heaps.
Require SepExpr Expr.
Require Import Provers.
Require Import EquivDec.
Require Import List.
    Require Import ReifySepExpr.
    Require ExprUnify.
Require SepCancel.

Set Implicit Arguments.

Module SepExprTests (B : Heap) (ST : SepTheoryX.SepTheoryX with Module H := B).
  Module Sep := SepExpr.Make ST.
  Module Reify := ReifySepExpr Sep.
  Module SH := SepHeap.Make Sep.
  Module CANCEL := SepCancel.Make ExprUnify.UNIFIER SH.

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

    Theorem asdf : forall x y : nat, EqNat.beq_nat x y = true -> x = y.
    Admitted.

    Definition nat_type : Expr.type :=
      {| Expr.Impl := nat 
       ; Expr.Eqb  := EqNat.beq_nat
       ; Expr.Eqb_correct := asdf
       |}.

    Fixpoint star_all a b (f : nat -> ST.hprop a b nil) (n : nat) : ST.hprop a b nil :=
      match n with
        | 0 => f 0
        | S n => ST.star (f (S n)) (star_all f n)
      end.

    Variables pc st : Type.

    (** With Ltac **)
    Section theorems.
      Variable cs : PropX.codeSpec pc st.
      Lemma himp_star_comm_p : forall P Q R,
        ST.himp cs (ST.star P Q) R ->
        ST.himp cs (ST.star Q P) R.
      Admitted.
      
      Lemma himp_star_comm_c : forall P Q R,
        ST.himp cs R (ST.star P Q) ->
        ST.himp cs R (ST.star Q P).
      Admitted.

      Lemma himp_star_assoc_p1 : forall P Q R S,
        ST.himp cs (ST.star P (ST.star Q R)) S ->
        ST.himp cs (ST.star (ST.star P Q) R) S.
      Admitted.

      Lemma himp_star_assoc_p2 : forall P Q R S,
        ST.himp cs (ST.star Q (ST.star P R)) S ->
        ST.himp cs (ST.star (ST.star P Q) R) S.
      Admitted.

      Lemma himp_star_assoc_c1 : forall P Q R S,
        ST.himp cs S (ST.star P (ST.star Q R)) ->
        ST.himp cs S (ST.star (ST.star P Q) R).
      Admitted.

      Lemma himp_star_assoc_c2 : forall P Q R S,
        ST.himp cs S (ST.star Q (ST.star P R)) ->
        ST.himp cs S (ST.star (ST.star P Q) R).
      Admitted.

      Lemma himp_star_emp_p : forall P S,
        ST.himp cs P S ->
        ST.himp cs (ST.star (ST.emp _ _) P) S.
      Admitted.
      
      Lemma himp_star_emp_c : forall P S,
        ST.himp cs S P ->
        ST.himp cs S (ST.star (ST.emp _ _) P).
      Admitted.
      
      Lemma himp_star_frame : forall P Q R S,
        ST.himp cs P R ->
        ST.himp cs Q S ->
        ST.himp cs (ST.star P Q) (ST.star R S).
      Admitted.
        
    End theorems.

    Ltac ltac_canceler :=
      let cancel P Q :=
        let rec iter_right Q :=
        match Q with 
          | @ST.emp _ _ _ =>
            apply himp_star_emp_c
          | @ST.star _ _ _ ?L ?R =>
            (apply himp_star_assoc_c1 ; iter_right L) || (apply himp_star_assoc_c1 ; iter_right R)
          | _ => 
            apply himp_star_frame; [ reflexivity | ]
        end
      in
      let rec iter_left P :=
        match P with
          | @ST.emp _ _ _ =>
            apply himp_star_emp_p
          | @ST.star _ _ _ ?L ?R =>
            (apply himp_star_assoc_p1 ; iter_left L) || (apply himp_star_assoc_p2 ; iter_left R)
          | _ => 
            match Q with
              | @ST.star _ _ _ ?A ?B =>
                iter_right A || (apply himp_star_comm_c; iter_right B)
            end
        end
      in
      match P with 
        | @ST.star _ _ _ ?A ?B =>
          iter_left A || (apply himp_star_comm_p; iter_left B)
      end
    in
    repeat match goal with
             | [ |- @ST.himp _ _ _ ?P ?Q ] =>
               reflexivity || cancel P Q
           end.
    


    Goal let N := 1 in
      forall c, @ST.himp pc st c 
      (ST.star (allb (@h pc st) N N) (allb (@f pc st) N N))
      (ST.star (all (@f pc st) N) (all (@h pc st) N)).
    Proof.
      simpl; intros.
      Time ltac_canceler.
    Time Qed.

    Goal let N := 5 in
      forall c, @ST.himp pc st c 
      (ST.star (allb (@h pc st) N N) (allb (@f pc st) N N))
      (ST.star (all (@f pc st) N) (all (@h pc st) N)).
    Proof.
      simpl; intros.
      Time ltac_canceler. 
    Time Qed.

    Goal let N := 10 in
      forall c, @ST.himp pc st c 
      (ST.star (allb (@h pc st) N N) (allb (@f pc st) N N))
      (ST.star (all (@f pc st) N) (all (@h pc st) N)).
    Proof.
      simpl; intros.
      Time ltac_canceler. 
    Time Qed.

    Goal let N := 15 in
      forall c, @ST.himp pc st c 
      (ST.star (allb (@h pc st) N N) (allb (@f pc st) N N))
      (ST.star (all (@f pc st) N) (all (@h pc st) N)).
    Proof.
      simpl; intros.
      Time ltac_canceler. 
    Time Qed.

    Goal let N := 20 in
      forall c, @ST.himp pc st c 
      (ST.star (allb (@h pc st) N N) (allb (@f pc st) N N))
      (ST.star (all (@f pc st) N) (all (@h pc st) N)).
    Proof.
      simpl; intros.
      Time ltac_canceler. 
    Time Qed.

(*


    Goal forall c, @ST.himp pc st c 
      (ST.star (allb (@h pc st) N N) (allb (@f pc st) M M))
      (ST.star (all (@f pc st) M) (all (@h pc st) N)).
      unfold N, M; simpl all; simpl allb; intros.
      Time ltac_canceler.
    Time Qed.
      
    





Time Sep.sep isConst (nat_type :: nil). reflexivity.


    Goal forall a b c x y, @ST.himp a b c (f _ _ (g y (x + x) 1)) (f _ _ 1).
      sep.
    Abort.

    Theorem t1 : forall a b c, @ST.himp a b c (f _ _ 0) (f _ _ 0).
      sep.
    Qed.

    Theorem t2 : forall a b c, 
      @ST.himp a b c (ST.star (star_all_back (@h a b) 15 15) (star_all_back (@f a b) 15 15))
                     (ST.star (star_all (@f a b) 15) (star_all (@h a b) 15)).
      sep.
    Qed.

    Theorem t3 : forall a b c, @ST.himp a b c 
      (ST.star (f _ _ 2) (f _ _ 1))
      (f _ _ 1).
      sep.
    Abort.

    Theorem t4 : forall a b c, @ST.himp a b c 
      (ST.ex (fun y : nat => ST.ex (fun x : bool => ST.star (f _ _ (g x 1 2)) (f _ _ 1) )))
      (f _ _ 1).
      sep.
    Abort.

    Theorem t5 : forall a b c, @ST.himp a b c 
      (ST.ex (fun y : nat => f _ _ y))
      (f _ _ 1).
      sep.
    Abort.

    Theorem t6 : forall a b c, @ST.himp a b c 
      (f _ _ 1)
      (ST.ex (fun y : nat => f _ _ y)).
      sep.
    Qed.

    Theorem t7 : forall a b c, @ST.himp a b c 
      (ST.star (f _ _ (g true 0 1)) (f _ _ (g true 1 2)))
      (ST.ex (fun y : nat => ST.star (f _ _ (g true 0 y)) (ST.ex (fun z : nat => f _ _ (g true 1 z))))).
      sep.
    Qed.

    Theorem t8 : forall a b c, @ST.himp a b c 
      (ST.star (f _ _ (g true 0 1)) (f _ _ (g true 1 2)))
      (ST.ex (fun y : nat => ST.star (f _ _ (g true 1 y)) (ST.ex (fun z : nat => f _ _ (g true 0 z))))).
      sep.
    Qed.


    (** ** Test use of transitivity prover in cancellation *)

    Theorem t9 : forall a b c x y, x = y
      -> @ST.himp a b c  (f _ _ x) (f _ _ y).
      sep.
    Qed.

    Theorem t10 : forall a b c x y, x = y
      -> @ST.himp a b c  (f _ _ y) (f _ _ x).
      sep.
    Qed.

    Theorem t11 : forall a b c x y z, x = y
      -> x = z
      -> @ST.himp a b c  (f _ _ x) (f _ _ y).
      sep.
    Qed.

    Theorem t12 : forall a b c x y u v, x = y
      -> u = v
      -> @ST.himp a b c  (ST.star (f _ _ x) (f _ _ v)) (ST.star (f _ _ y) (f _ _ u)).
      sep.
    Qed.

    Theorem t13 : forall a b c x y z u v, x = y
      -> z = y
      -> u = v
      -> @ST.himp a b c  (ST.star (f _ _ x) (f _ _ v)) (ST.star (f _ _ z) (f _ _ u)).
      sep.
    Qed.
*)

  End Tests.

End SepExprTests.
