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

    Definition N := 20.
    Definition M := 20.

    Variables pc st : Type.

    Definition try_it_out {ts} (pcV stV : Expr.tvar) (preds : CANCEL.SE.predicates ts pcV stV) (l r : Sep.sexpr ts pcV stV) : 
      (SH.SHeap ts pcV stV * SH.SHeap ts pcV stV * ExprUnify.UNIFIER.Subst ts) :=
      let l := SH.hash l in
      let r := SH.hash r in
      @CANCEL.sepCancel ts pcV stV preds (ReflexivityProver.reflexivityProver) 1 tt (snd l) (snd r) (ExprUnify.UNIFIER.Subst_empty _).      


    Theorem apply_it ts pcT stT funcs (preds : CANCEL.SE.predicates ts pcT stT) l r cs : 
      (let '(l',r',_) := @try_it_out ts pcT stT preds l r in
       @ST.himp (Expr.tvarD ts pcT) (Expr.tvarD ts stT) cs 
         (@Sep.sexprD ts pcT stT funcs preds nil nil (SH.sheapD l')) (@Sep.sexprD ts pcT stT funcs preds nil nil (SH.sheapD r'))) ->
      @ST.himp (Expr.tvarD ts pcT) (Expr.tvarD ts stT) cs 
        (@Sep.sexprD ts pcT stT funcs preds nil nil l) (@Sep.sexprD ts pcT stT funcs preds nil nil r).
    Proof.
    Admitted.

    Ltac go :=
      match goal with
        | [ |- ST.himp _ ?L ?R ] =>
          let Ts := constr:(Reflect.Tcons pc (Reflect.Tcons st Reflect.Tnil)) in
          Reify.collectTypes_sexpr ltac:(isConst) L Ts ltac:(fun Ts =>
          Reify.collectTypes_sexpr ltac:(isConst) R Ts ltac:(fun Ts =>
          let types := ReifyExpr.extend_all_types Ts (nat_type :: @nil Expr.type) in
          let uvars := eval simpl in (@nil _ : Expr.env types) in
          let gvars := uvars in
          let vars := eval simpl in (@nil Expr.tvar) in
          (** build the funcs **)
          let funcs := constr:(@nil (Expr.signature types)) in
          let pcT := constr:(Expr.tvType 1) in
          let stT := constr:(Expr.tvType 2) in
          (** build the base sfunctions **)
          let preds := constr:(@nil (Sep.predicate types pcT stT)) in
          Reify.reify_sexpr ltac:(isConst) L types funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds L =>
          Reify.reify_sexpr ltac:(isConst) R types funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds R =>
            simple apply (@apply_it types pcT stT funcs preds L R); compute
          ))))
      end.

    Goal let N := 1 in
      forall c, @ST.himp pc st c 
      (ST.star (allb (@h pc st) N N) (allb (@f pc st) N N))
      (ST.star (all (@f pc st) N) (all (@h pc st) N)).
    Proof.
      simpl; intros.
      Time go. reflexivity.
    Time Qed.

    Goal let N := 5 in
      forall c, @ST.himp pc st c 
      (ST.star (allb (@h pc st) N N) (allb (@f pc st) N N))
      (ST.star (all (@f pc st) N) (all (@h pc st) N)).
    Proof.
      simpl; intros.
      Time go. reflexivity.
    Time Qed.

    Goal let N := 10 in
      forall c, @ST.himp pc st c 
      (ST.star (allb (@h pc st) N N) (allb (@f pc st) N N))
      (ST.star (all (@f pc st) N) (all (@h pc st) N)).
    Proof.
      simpl; intros.
      Time go. reflexivity.
    Time Qed.

    Goal let N := 15 in
      forall c, @ST.himp pc st c 
      (ST.star (allb (@h pc st) N N) (allb (@f pc st) N N))
      (ST.star (all (@f pc st) N) (all (@h pc st) N)).
    Proof.
      simpl; intros.
      Time go. reflexivity.
    Time Qed.

    Goal let N := 20 in
      forall c, @ST.himp pc st c 
      (ST.star (allb (@h pc st) N N) (allb (@f pc st) N N))
      (ST.star (all (@f pc st) N) (all (@h pc st) N)).
    Proof.
      simpl; intros.
      Time go. reflexivity.
    Time Qed.

(*
    Goal forall c, @ST.himp pc st c 
      (ST.star (allb (@h pc st) N N) (allb (@f pc st) M M))
      (ST.star (all (@f pc st) M) (all (@h pc st) N)).
      unfold N, M; simpl all; simpl allb; intros.
      Time go. reflexivity.
      Time Qed.
*)

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
