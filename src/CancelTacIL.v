Require Import List Bool.
Require Import ExtLib.Tactics.Consider.
Require MirrorShard.CancelTacBedrock.
Require MirrorShard.ExprUnify.
Require Import MirrorShard.Expr.
Require Import MirrorShard.Provers.
Require Import MirrorShard.SepExprTac.
Require Import ILEnv SepIL TacPackIL.

Set Implicit Arguments.
Set Strict Implicit.

Module CANCEL_TAC := 
  CancelTacBedrock.Make SepIL.ST SepIL.SEP SepIL.SH
                        TacPackIL.SEP_LEMMA
                        SUBST
                        UNIFY
                        UNF.

Module SEP_TAC := MirrorShard.SepExprTac.Make SepIL.ST SepIL.SEP.

Section canceller.
  Variable ts : list Expr.type.
  Let types := Env.repr BedrockCoreEnv.core ts.

  Definition nexistsSubst (not : Prop -> Prop) (types : list type) (funcs : functions types) (sub : SUBST.Subst) :=
    fix existsSubst (meta vars : env types) (from : nat) 
    (vals : list tvar) (ret : env types -> Prop) {struct vals} : Prop :=
    match vals with
      | nil => ret meta
      | t :: ts =>
        match SUBST.Subst_lookup from sub with
          | Some v =>
            match exprD funcs meta vars v t with
              | Some v0 =>
                existsSubst (meta ++ existT (tvarD types) t v0 :: nil) vars
                (S from) ts ret
              | None =>
                exists x : tvarD types t,
                  existsSubst (meta ++ existT (tvarD types) t x :: nil) vars
                  (S from) ts
                  (fun g : env types =>
                    match exprD funcs g vars v t with
                      | Some y => x = y /\ ret g
                      | None => False
                    end)
            end
          | None =>
            exists x : tvarD types t,
              existsSubst (meta ++ existT (tvarD types) t x :: nil) vars
              (S from) ts ret
        end
    end.

  Theorem nexistsSubst_existsSubst : nexistsSubst not = CANCEL_TAC.INS.existsSubst. 
  Proof. reflexivity. Qed.

  Definition nSubst_equations_to (not : Prop -> Prop) (types : list type) (funcs : functions types) (uenv venv : env types)
    (subst : SUBST.Subst) from ls (rr : Prop) :=
    (fix Subst_equations_to (from : nat) (ls : env types) {struct ls} : Prop :=
    match ls with
      | nil => rr
      | l :: ls0 =>
        match SUBST.Subst_lookup from subst with
          | Some e =>
            match ExprTac.nexprD not types funcs uenv venv e (projT1 l) with
              | Some v => projT2 l = v
              | None => False
            end
          | None => True
        end /\ Subst_equations_to (S from) ls0
    end) from ls.
  
  Theorem nSubst_equations_to_Subst_equations_to : forall ts fs u v s r ls from,
    @nSubst_equations_to not ts fs u v s from ls r <-> @SUBST.Subst_equations_to ts fs u v s from ls /\ r.
  Proof. 
    induction ls; simpl.
    { intuition. }
    { intros. rewrite IHls. intuition. }
  Qed.
  
  Definition cancel (himp : hprop -> hprop -> Prop) (emp : hprop) (star : hprop -> hprop -> hprop) 
    (ex : forall T : Type, (T -> hprop) -> hprop) (inj : Prop -> hprop) (not : Prop -> Prop)
    (boundf boundb : nat)
    (ts : list Expr.type)
    (funcs : Expr.functions (Env.repr ILEnv.BedrockCoreEnv.core ts))
    (preds : SEP.predicates (Env.repr ILEnv.BedrockCoreEnv.core ts))
    (algos : TacPackIL.ILAlgoTypes.AllAlgos)
    (uvars : Expr.env (Env.repr ILEnv.BedrockCoreEnv.core ts))
    (lhs rhs : SEP.sexpr)
    (hyps : Expr.exprs) : Prop :=
    let types := Env.repr ILEnv.BedrockCoreEnv.core ts in
    let hints :=
      match TacPackIL.ILAlgoTypes.Hints algos with
        | Some x => x
        | None =>
          {| TacPackIL.UNF.Forward := nil
           ; TacPackIL.UNF.Backward := nil |}
      end in
    let prover :=
      match TacPackIL.ILAlgoTypes.Prover algos with
        | Some x => x
        | None =>
          Provers.trivialProver
      end in
    let tfuncs := typeof_funcs funcs in
    let tpreds := SEP.typeof_preds preds in
    if SEP.WellTyped_sexpr tfuncs tpreds (typeof_env uvars) nil rhs then
      match CANCEL_TAC.canceller tpreds (TacPackIL.UNF.Forward hints) (TacPackIL.UNF.Backward hints) prover boundf boundb (typeof_env uvars) hyps lhs rhs with
        | None => 
          himp (SEP_TAC.nsexprD not emp star ex inj types funcs preds uvars nil lhs)
               (SEP_TAC.nsexprD not emp star ex inj types funcs preds uvars nil rhs)
        | Some {| CANCEL_TAC.AllExt := new_vars
                ; CANCEL_TAC.ExExt := new_uvars
                ; CANCEL_TAC.Lhs := lhs'
                ; CANCEL_TAC.Rhs := rhs'
                ; CANCEL_TAC.Subst := subst |} =>
          forallEach new_vars (fun nvs : env types =>
             let var_env := nvs in
             ExprTac.nAllProvable_impl not _ funcs uvars var_env
               (nexistsSubst not funcs subst uvars var_env (length uvars) new_uvars
                 (fun meta_env0 : env types =>
                    nSubst_equations_to not funcs meta_env0 var_env subst 0 uvars 
                      (ExprTac.nAllProvable_and not _ funcs meta_env0 var_env
                        (himp
                           (SEP_TAC.nsexprD not emp star ex inj types funcs preds meta_env0 var_env
                              (SH.sheapD
                                 {| SH.impures := SH.impures lhs'
                                  ; SH.pures := nil
                                  ; SH.other := SH.other lhs' |}))
                           (SEP_TAC.nsexprD not emp star ex inj types funcs preds meta_env0 var_env
                              (SH.sheapD
                                 {| SH.impures := SH.impures rhs'
                                  ; SH.pures := nil
                                  ; SH.other := SH.other rhs' |})))
                        (SH.pures rhs')))) (SH.pures lhs'))

        end
    else
      himp (SEP_TAC.nsexprD not emp star ex inj types funcs preds uvars nil lhs)
           (SEP_TAC.nsexprD not emp star ex inj types funcs preds uvars nil rhs).

  Theorem ApplyCancelSep_slice (boundf boundb : nat) : forall (ts : list Expr.type)
      (funcs : Expr.functions (Env.repr ILEnv.BedrockCoreEnv.core ts))
      (preds : SEP.predicates (Env.repr ILEnv.BedrockCoreEnv.core ts))
      (algos : TacPackIL.ILAlgoTypes.AllAlgos),
      TacPackIL.ILAlgoTypes.AllAlgos_correct (types := Env.repr ILEnv.BedrockCoreEnv.core ts) funcs preds algos ->
      forall (uvars : Expr.env (Env.repr ILEnv.BedrockCoreEnv.core ts))
        (lhs rhs : SEP.sexpr)
        (hyps : Expr.exprs),
        Expr.AllProvable funcs uvars nil hyps ->
        (cancel himp emp star ex inj not boundf boundb funcs preds algos uvars lhs rhs hyps) ->
        SEP.himp funcs preds uvars nil lhs rhs.
  Proof.
    Opaque Env.repr.
    intros. unfold cancel in *; simpl in *.    
    consider (SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env uvars) nil rhs); intros; eauto.
    consider (CANCEL_TAC.canceller (SEP.typeof_preds preds)
           (UNF.Forward
              match ILAlgoTypes.Hints algos with
              | Some x => x
              | None => {| UNF.Forward := nil; UNF.Backward := nil |}
              end)
           (UNF.Backward
              match ILAlgoTypes.Hints algos with
              | Some x => x
              | None => {| UNF.Forward := nil; UNF.Backward := nil |}
              end)
           match ILAlgoTypes.Prover algos with
           | Some x => x
           | None => trivialProver
           end boundf boundb (typeof_env uvars) hyps lhs rhs); intros.
    { eapply CANCEL_TAC.ApplyCancelSep_with_eq in H1; eauto. 
      { destruct X. destruct (ILAlgoTypes.Hints algos); eauto using UNF.ForwardOk.
        simpl. constructor. }
      { destruct X. destruct (ILAlgoTypes.Hints algos); eauto using UNF.BackwardOk.
        simpl. constructor. }
      { destruct X. destruct (ILAlgoTypes.Prover algos); eauto using trivialProver_correct. }
      { eapply typeof_funcs_WellTyped_funcs. } 
      { rewrite nexistsSubst_existsSubst in *. 
        destruct c. apply forallEach_sem. intros.
        eapply forallEach_sem in H2; eauto.
        rewrite ExprTac.nAllProvable_impl_AllProvable_impl in H2.
        apply AllProvable_impl_sem; intros.
        apply AllProvable_impl_sem in H2; eauto.
        eapply CANCEL_TAC.INS.existsSubst_sem in H2. eapply existsEach_sem in H2. destruct H2; intuition.
        eapply CANCEL_TAC.INS.existsSubst_sem. eapply existsEach_sem. exists x.
        change (fun A : Prop => A -> False) with not in *.
        rewrite nSubst_equations_to_Subst_equations_to in *. intuition.
        rewrite ExprTac.nAllProvable_and_AllProvable_and in H8. intuition. } }
    { apply H2. }
  Qed.

End canceller.
