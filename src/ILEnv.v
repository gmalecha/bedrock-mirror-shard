(** This file contains generic environment information for the Bedrock IL
 **)
Require Import List.
Require Import MirrorShard.Expr.
Require Import MirrorShard.Env.
Require Import MirrorShard.TypedPackage.
Require Import Word.
Require Import Memory IL.
Require Import Arith.


Set Implicit Arguments.
Set Strict Implicit.

(*
Definition test_seq l r : bool :=
  match l as l , r as r with
    | IL.Eq , IL.Eq => true
    | IL.Ne , IL.Ne => true
    | IL.Le , IL.Le => true
    | IL.Lt , IL.Lt => true
    | _ , _ => false
  end.

Theorem test_seq_compare : forall x y, test_seq x y = true -> x = y.
  destruct x; destruct y; simpl; (reflexivity || congruence).
Defined.
*)

Definition reg_seq l r : bool := 
  match l as l , r as r with
    | IL.Sp , IL.Sp => true
    | IL.Rp , IL.Rp => true
    | IL.Rv , IL.Rv => true
    | _ , _ => false
  end.

Theorem reg_seq_compare : forall x y, reg_seq x y = true -> x = y.
  destruct x; destruct y; simpl; (reflexivity || congruence).
Defined.

Definition W_seq (l r : W) : bool := Word.weqb l r.

Theorem W_seq_compare : forall x y, W_seq x y = true -> x = y.
  intros. apply weqb_sound. unfold W_seq in *. apply H.
Defined.

Lemma all_false_compare T : forall x y : T, false = true -> x = y.
  congruence.
Defined.

Definition bedrock_type_W : type := 
  {| Expr.Impl := W 
   ; Expr.Eqb := W_seq
   ; Expr.Eqb_correct := W_seq_compare
  |}.
Definition bedrock_type_setting_X_state : type :=
  {| Expr.Impl := settings * state
   ; Expr.Eqb := fun _ _ => false
   ; Expr.Eqb_correct := @all_false_compare _
   |}.
Definition bedrock_type_state : type :=
  {| Expr.Impl := state
   ; Expr.Eqb := fun _ _ => false
   ; Expr.Eqb_correct := @all_false_compare _
   |}.
(*
Definition bedrock_type_test : type :=
  {| Expr.Impl := IL.test
   ; Expr.Eqb := test_seq
   ; Expr.Eqb_correct := test_seq_compare
  |}.
*)
Definition bedrock_type_reg : type :=
  {| Expr.Impl := IL.reg
   ; Expr.Eqb := reg_seq
   ; Expr.Eqb_correct := reg_seq_compare
  |}.

Definition bedrock_type_nat : type :=
  {| Expr.Impl := nat
   ; Expr.Eqb := beq_nat
   ; Expr.Eqb_correct := beq_nat_true
  |}.

Definition core_bedrock_types : list Expr.type :=
  bedrock_type_W ::
  bedrock_type_setting_X_state :: nil.

Definition core_bedrock_types_r : Repr Expr.type :=
  Eval cbv beta iota zeta delta [ listToRepr core_bedrock_types ]
    in (listToRepr core_bedrock_types Expr.EmptySet_type).

Definition bedrock_types : list Expr.type :=
  bedrock_type_W ::
  bedrock_type_setting_X_state ::
  bedrock_type_state ::
(*  bedrock_type_test :: *)
  bedrock_type_reg ::
  bedrock_type_nat :: nil.

Definition bedrock_types_r : Repr Expr.type :=
  Eval cbv beta iota zeta delta [ listToRepr bedrock_types ]
    in (listToRepr bedrock_types Expr.EmptySet_type).

Definition comparator (t : IL.test) (l r : W) : Prop :=
  match t with
    | IL.Eq => l = r
    | IL.Ne => l = r -> False
    | IL.Lt => wlt l r
    | IL.Le => not (wlt r l)
  end.

Section typed_ext.
  Variable types' : list type.
  (* Local Notation "'types'" := (repr bedrock_types_r types'). *)

  Local Notation "'pcT'" := (tvType 0).
  Local Notation "'tvWord'" := (tvType 0).
  Local Notation "'stT'" := (tvType 1).
  Local Notation "'tvState'" := (tvType 2).
(*Local Notation "'tvTest'" := (tvType 3).*)
  Local Notation "'tvReg'" := (tvType 3).
  Local Notation "'natT'" := (tvType 4).

  Definition word_types_r : Repr Expr.type :=
    Eval cbv beta iota zeta delta [ listToRepr ] 
      in (listToRepr (bedrock_type_W :: nil) Expr.EmptySet_type).
 

  Definition wplus_r : signature (repr word_types_r types').
    refine {| Domain := tvWord :: tvWord :: nil; Range := tvWord |}.
    exact (@wplus 32).
  Defined.

  Definition wminus_r : signature (repr word_types_r types').
    refine {| Domain := tvWord :: tvWord :: nil; Range := tvWord |}.
    exact (@wminus 32).
  Defined.

  Definition wmult_r : signature (repr word_types_r types').
    refine {| Domain := tvWord :: tvWord :: nil; Range := tvWord |}.
    exact (@wmult 32).
  Defined.

  Definition nat_types_r : Repr Expr.type :=
    Eval cbv beta iota zeta delta [ listToRepr ] 
      in (listOptToRepr (None :: None :: None :: None :: Some bedrock_type_nat :: nil) Expr.EmptySet_type).

  Definition O_r : signature (repr nat_types_r types').
    refine {| Domain := nil; Range := natT |}.
    exact 0.
  Defined.

  Definition S_r : signature (repr nat_types_r types').
    refine {| Domain := natT :: nil; Range := natT |}.
    exact S.
  Defined.

(*
  Definition word_test_r : Repr Expr.type :=
    Eval cbv beta iota zeta delta [ listToRepr ] 
      in (listOptToRepr (Some bedrock_type_W :: None :: None :: Some bedrock_type_test :: nil) Expr.EmptySet_type).

  Definition wcomparator_r : signature (repr word_test_r types').
    refine {| Domain := tvTest :: tvWord :: tvWord :: nil ; Range := tvProp |}.
    exact (comparator).
  Defined.
*)

  Definition word_state_r : Repr Expr.type :=
    Eval cbv beta iota zeta delta [ listToRepr ] 
      in (listOptToRepr (Some bedrock_type_W :: None :: Some bedrock_type_state :: Some bedrock_type_reg :: nil) Expr.EmptySet_type).

  Definition Regs_r : signature (repr word_state_r types').
    refine {| Domain := tvState :: tvReg :: nil ; Range := tvWord |}.
    exact (Regs).
  Defined.

  Definition wlt_r : signature (repr word_types_r types').
    refine {| Domain := tvWord :: tvWord :: nil; Range := tvProp |}.
    exact (@wlt 32).
  Defined.

  Definition word_nat_r : Repr Expr.type :=
    Eval cbv beta iota zeta delta [ listToRepr ] 
      in (listOptToRepr (Some bedrock_type_W :: None :: None :: None :: Some bedrock_type_nat :: nil) Expr.EmptySet_type).

  Definition natToW_r : signature (repr word_nat_r types').
    refine {| Domain := natT :: nil; Range := tvWord |}.
    exact natToW.
  Defined.
End typed_ext.

  Definition bedrock_funcs types' : functions (repr bedrock_types_r types') :=
    let types := repr bedrock_types_r types' in
    wplus_r types ::
    wminus_r types ::
    wmult_r types ::
    (* wcomparator_r types :: *)
    Regs_r types ::
    wlt_r types ::
    natToW_r types :: 
    O_r types ::
    S_r types ::
    nil.

  Definition bedrock_funcs_r types' : Repr (signature (repr bedrock_types_r types')) :=
    Eval cbv beta iota zeta delta [ listToRepr bedrock_funcs ]
      in (listToRepr (bedrock_funcs types') (Default_signature _)).

  Definition nat_funcs types' : list (option (signature (repr nat_types_r types'))) :=
    let types := repr nat_types_r types' in
    None ::
    None ::
    None ::
    None ::
    None ::
    None ::
    Some (O_r types) ::
    Some (S_r types) ::
    nil.

  Definition nat_funcs_r types' : Repr (signature (repr nat_types_r types')) :=
    Eval cbv beta iota zeta delta [ listOptToRepr nat_funcs ]
      in (listOptToRepr (nat_funcs types') (Default_signature _)).

Section nat_const.
  Variable ts' : list type.
  Let ts := repr nat_types_r ts'.
  Variable fs' : functions ts.
  Let fs := repr (nat_funcs_r ts') fs'.

  Fixpoint toConst_nat (e : expr) : option nat :=
    match e with
      | Func 6 nil => Some 0
      | Func 7 (e :: nil) =>
        match toConst_nat e with
          | Some n => Some (S n)
          | None => None
        end
      | _ => None
    end.
  
  Theorem toConst_nat_sound : forall e n,
                                toConst_nat e = Some n ->
                                forall us vs,
                                  exprD fs us vs e (tvType 4) = Some n.
  Proof.
    induction e; simpl; intros; try discriminate.
    do 7 (destruct f; try discriminate).
    { destruct l; try congruence. 
      inversion H0; clear H0; subst.
      simpl. reflexivity. }
    { destruct f; try discriminate.
      do 2 (destruct l; try discriminate).
      inversion H; clear H; subst.
      destruct (toConst_nat e); try discriminate.
      specialize (H3 _ eq_refl).
      simpl.
      rewrite H3. auto. }
  Qed.

  Fixpoint toExpr_nat (n : nat) : expr :=
    match n with
      | 0 => Func 6 nil
      | S n => Func 7 (toExpr_nat n :: nil)
    end.

  Theorem toExpr_nat_sound : forall n us vs,
                               exprD fs us vs (toExpr_nat n) (tvType 4) = Some n.
  Proof.
    induction n; simpl; intros; eauto.
    rewrite IHn. reflexivity.
  Qed.

End nat_const.

  
Section func_ext.
  Local Notation "'pcT'" := (tvType 0).
  Local Notation "'tvWord'" := (tvType 0).
  Local Notation "'stT'" := (tvType 1).
  Local Notation "'tvState'" := (tvType 2).
(*Local Notation "'tvTest'" := (tvType 3).*)
  Local Notation "'tvReg'" := (tvType 3).
  Local Notation "'natT'" := (tvType 4).


  Variable types' : list type.
  Definition types := repr bedrock_types_r types'.

  Variable funcs' : functions types.
  Definition funcs := repr (bedrock_funcs_r types') funcs'.
  
  Definition fPlus (l r : expr) : expr :=
    Expr.Func 0 (l :: r :: nil).
  Definition fMinus (l r : expr) : expr :=
    Expr.Func 1 (l :: r :: nil).
  Definition fMult (l r : expr) : expr :=
    Expr.Func 2 (l :: r :: nil).

  Theorem fPlus_correct : forall l r uvars vars, 
    match exprD funcs uvars vars l (tvType 0) , exprD funcs uvars vars r (tvType 0) with
      | Some lv , Some rv =>
        exprD funcs uvars vars (fPlus l r) (tvType 0) = Some (wplus lv rv)
      | _ , _ => True
    end.
  Proof.
    intros; simpl; unfold eq_ind_r; simpl;
      repeat match goal with
               | [ |- match ?X with
                        | Some _ => _
                        | None => _
                      end ] => destruct X
             end; auto.
  Qed.
  Theorem fMinus_correct : forall l r uvars vars, 
    match exprD funcs uvars vars l tvWord , exprD funcs uvars vars r tvWord with
      | Some lv , Some rv =>
        exprD funcs uvars vars (fMinus l r) tvWord = Some (wminus lv rv)
      | _ , _ => True
    end.
  Proof.
    intros; simpl; unfold eq_ind_r; simpl;
      repeat match goal with
               | [ |- match ?X with
                        | Some _ => _
                        | None => _
                      end ] => destruct X
             end; auto.
  Qed.
  Theorem fMult_correct : forall l r uvars vars, 
    match exprD funcs uvars vars l tvWord , exprD funcs uvars vars r tvWord with
      | Some lv , Some rv =>
        exprD funcs uvars vars (fMult l r) tvWord = Some (wmult lv rv)
      | _ , _ => True
    end.
  Proof.
    intros; simpl; unfold eq_ind_r; simpl;
      repeat match goal with
               | [ |- match ?X with
                        | Some _ => _
                        | None => _
                      end ] => destruct X
             end; auto.
  Qed.
End func_ext.


Module BedrockCoreEnv <: CoreEnv.
  Definition core := 
    Eval unfold bedrock_types_r in bedrock_types_r.
  
  Definition pc := tvType 0.
  Definition st := tvType 1.
End BedrockCoreEnv.

(*Require SepIL. *)
