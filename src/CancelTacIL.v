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
  
  Definition nsubstInEnv (not : Prop -> Prop) (types : list type) (funcs : functions types)
    (meta_base var_env : env types) (sub : SUBST.Subst types) :=
    fix substInEnv (from : nat) (vals : env types) (ret : env types -> Prop)
    {struct vals} : Prop :=
    match vals with
      | nil => ret nil
      | val :: vals0 =>
        match SUBST.Subst_lookup from sub with
          | Some v =>
            match ExprTac.nexprD not _ funcs meta_base var_env v (projT1 val) with
              | Some v' =>
                projT2 val = v' /\
                substInEnv (S from) vals0
                (fun e : env types =>
                  ret (existT (tvarD types) (projT1 val) v' :: e))
              | None => CANCEL_TAC.ExistsSubstNone (projT1 val) v
            end
          | None =>
            substInEnv (S from) vals0 (fun e : env types => ret (val :: e))
        end
    end.

  Theorem nsubstInEnv_substInEnv : nsubstInEnv not = CANCEL_TAC.substInEnv.
  Proof. reflexivity. Qed.

  Definition nexistsSubst (not : Prop -> Prop) := 
    fun (types : list type) (funcs : functions types) (var_env : env types)
      (sub : SUBST.Subst types) (from : nat)
      (vals : list {t : tvar & option (tvarD types t)}) 
      (ret : env types -> Prop) =>
      CANCEL_TAC.existsMaybe vals
      (fun e : env types => nsubstInEnv not funcs e var_env sub from e ret).
  
  Theorem nexistsSubst_existsSubst : nexistsSubst not = CANCEL_TAC.existsSubst.
  Proof. reflexivity. Qed.

  Definition cancel (himp : hprop -> hprop -> Prop) (emp : hprop) (star : hprop -> hprop -> hprop) 
    (ex : forall T : Type, (T -> hprop) -> hprop) (inj : Prop -> hprop) (not : Prop -> Prop)
    (ts : list Expr.type)
    (funcs : Expr.functions (Env.repr ILEnv.BedrockCoreEnv.core ts))
    (preds : SEP.predicates (Env.repr ILEnv.BedrockCoreEnv.core ts))
    (algos : TacPackIL.ILAlgoTypes.AllAlgos (Env.repr ILEnv.BedrockCoreEnv.core ts))
    (uvars : Expr.env (Env.repr ILEnv.BedrockCoreEnv.core ts))
    (lhs rhs : SEP.sexpr (Env.repr ILEnv.BedrockCoreEnv.core ts))
    (hyps : Expr.exprs (Env.repr ILEnv.BedrockCoreEnv.core ts)) : Prop :=
    let types := Env.repr ILEnv.BedrockCoreEnv.core ts in
    let bound := 10 in
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
          Provers.trivialProver (Env.repr ILEnv.BedrockCoreEnv.core ts)
      end in
    let tfuncs := typeof_funcs funcs in
    let tpreds := SEP.typeof_preds preds in
    if SEP.WellTyped_sexpr tfuncs tpreds (typeof_env uvars) nil rhs then
      match CANCEL_TAC.canceller tpreds (TacPackIL.UNF.Forward hints) (TacPackIL.UNF.Backward hints) prover (typeof_env uvars) hyps lhs rhs with
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
               (nexistsSubst not funcs var_env subst 0
                 (map
                   (fun x : sigT (tvarD types) =>
                       existT (fun t : tvar => option (tvarD types t))
                         (projT1 x) (Some (projT2 x))) uvars ++
                    map
                      (fun x : tvar =>
                       existT (fun t : tvar => option (tvarD types t)) x None)
                      new_uvars)
                   (fun meta_env0 : env types =>
                    ExprTac.nAllProvable_and not _ funcs meta_env0 var_env
                      (himp
                         (SEP_TAC.nsexprD not emp star ex inj types funcs preds meta_env0 var_env
                            (SH.sheapD
                               {|
                               SH.impures := SH.impures lhs';
                               SH.pures := nil;
                               SH.other := SH.other lhs' |}))
                         (SEP_TAC.nsexprD not emp star ex inj types funcs preds meta_env0 var_env
                            (SH.sheapD
                               {|
                               SH.impures := SH.impures rhs';
                               SH.pures := nil;
                               SH.other := SH.other rhs' |})))
                      (SH.pures rhs'))) (SH.pures lhs'))

      end
    else
      himp (SEP_TAC.nsexprD not emp star ex inj types funcs preds uvars nil lhs)
           (SEP_TAC.nsexprD not emp star ex inj types funcs preds uvars nil rhs).
      

  Theorem ApplyCancelSep_slice : forall (ts : list Expr.type)
      (funcs : Expr.functions (Env.repr ILEnv.BedrockCoreEnv.core ts))
      (preds : SEP.predicates (Env.repr ILEnv.BedrockCoreEnv.core ts))
      (algos : TacPackIL.ILAlgoTypes.AllAlgos
        (Env.repr ILEnv.BedrockCoreEnv.core ts)),
      TacPackIL.ILAlgoTypes.AllAlgos_correct (types := Env.repr ILEnv.BedrockCoreEnv.core ts) funcs preds algos ->
      forall (uvars : Expr.env (Env.repr ILEnv.BedrockCoreEnv.core ts))
        (lhs rhs : SEP.sexpr (Env.repr ILEnv.BedrockCoreEnv.core ts))
        (hyps : Expr.exprs (Env.repr ILEnv.BedrockCoreEnv.core ts)),
        Expr.AllProvable funcs uvars nil hyps ->
        (cancel himp emp star ex inj not funcs preds algos uvars lhs rhs hyps) ->
(*           
         let '(x, y) :=
           CancelTacIL.CANCEL_LOOP.cancel (SEP.typeof_preds preds)
           prover (TacPackIL.UNF.Forward hints)
           (TacPackIL.UNF.Backward hints) bound hyps
           (Expr.typeof_env uvars) nil lhs rhs in
           if (SEP.WellTyped_sexpr (Expr.typeof_funcs funcs)
             (SEP.typeof_preds preds) (Expr.typeof_env uvars) nil rhs && y)%bool
           then ncancelResultD himp emp star ex inj funcs preds uvars nil x
           else himp (nsexprD emp star ex inj funcs preds uvars nil lhs)
                     (nsexprD emp star ex inj funcs preds uvars nil rhs)) -> *)
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
           | None => trivialProver (Env.repr BedrockCoreEnv.core ts0)
           end (typeof_env uvars) hyps lhs rhs); intros.
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
        eapply CANCEL_TAC.existsSubst_sem in H2. eapply existsEach_sem in H2. destruct H2; intuition.
        eapply CANCEL_TAC.existsSubst_sem. eapply existsEach_sem. exists x. intuition.
        rewrite ExprTac.nAllProvable_and_AllProvable_and in H8. auto. } }
    { apply H2. }
  Qed.

End canceller.
