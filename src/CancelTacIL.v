Require Import List Bool.
Require MirrorShard.CancelTacBedrock.
Require MirrorShard.ExprUnify.
Require Import MirrorShard.Expr.
Require Import MirrorShard.Reflection.
Require Import MirrorShard.Provers.
Require Import ILEnv SepIL TacPackIL.

Set Implicit Arguments.
Set Strict Implicit.

Module CANCEL_TAC := 
  MirrorShard.CancelTacBedrock.Make SepIL.ST SepIL.SEP SepIL.SH
                                    TacPackIL.SEP_LEMMA 
                                    ExprUnify.UNIFIER
                                    UNF.

Section canceller.
  Variable ts : list Expr.type.
  Let types := Env.repr BedrockCoreEnv.core ts.



(*
  Theorem ApplyCancelSep_with_eq1 :
    forall (funcs : functions types) (preds : SEP.predicates types)
      (algos : TacPackIL.ILAlgoTypes.AllAlgos types)
      (algosC : @TacPackIL.ILAlgoTypes.AllAlgos_correct types funcs preds algos)
      (uvars : env types) (lhs rhs : SEP.sexpr types)
      (hyps : exprs types)
      (cr : CANCEL_LOOP.cancelResult types),
      AllProvable funcs uvars nil hyps ->
      (let bound := 10 in
       let hints :=
         match TacPackIL.ILAlgoTypes.Hints algos with
           | None => {| UNF.Forward := nil ; UNF.Backward := nil |}
           | Some x => x
         end
       in
       let prover :=
         match TacPackIL.ILAlgoTypes.Prover algos with
           | None => Provers.trivialProver types
           | Some x => x
         end
       in
       let '(x,y) :=
         CANCEL_LOOP.cancel (SEP.typeof_preds preds) prover (UNF.Forward hints) (UNF.Backward hints)
         bound hyps (typeof_env uvars) nil lhs rhs in
       (x, SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env uvars) nil rhs && y) = (cr, true)) ->
      CANCEL_LOOP.cancelResultD funcs preds uvars nil 0 cr ->
      SEP.himp funcs preds uvars nil lhs rhs.
  Proof.
  Admitted.

  Theorem ApplyCancelSep_with_eq2 :
    forall (funcs : functions types) (preds : SEP.predicates types)
      (algos : TacPackIL.ILAlgoTypes.AllAlgos types)
      (algosC : @TacPackIL.ILAlgoTypes.AllAlgos_correct types funcs preds algos)
      (uvars : env types) (lhs rhs : SEP.sexpr types)
      (hyps : exprs types),
      AllProvable funcs uvars nil hyps ->
      (let bound := 10 in
       let hints :=
         match TacPackIL.ILAlgoTypes.Hints algos with
           | None => {| UNF.Forward := nil ; UNF.Backward := nil |}
           | Some x => x
         end
       in
       let prover :=
         match TacPackIL.ILAlgoTypes.Prover algos with
           | None => Provers.trivialProver types
           | Some x => x
         end
       in
       let '(x,y) :=
         CANCEL_LOOP.cancel (SEP.typeof_preds preds) prover (UNF.Forward hints) (UNF.Backward hints)
         bound hyps (typeof_env uvars) nil lhs rhs in
       if SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env uvars) nil rhs && y then
         CANCEL_LOOP.cancelResultD funcs preds uvars nil 0 x
       else
         SEP.himp funcs preds uvars nil lhs rhs) ->      
      SEP.himp funcs preds uvars nil lhs rhs.
  Proof.
  Admitted.
*)

  Definition nsexprD (emp : hprop) (star : hprop -> hprop -> hprop) (ex : forall T : Type, (T -> hprop) -> hprop) (inj : Prop -> hprop) :=
    fun (types : list Expr.type) (funcs : Expr.functions types)
      (sfuncs : SEP.predicates types) =>
      fix sexprD (meta_env var_env : Expr.env types) (s : SEP.sexpr types)
      {struct s} : hprop :=
      match s with
        | SEP.Emp => emp
        | SEP.Inj p =>
          match Expr.exprD funcs meta_env var_env p Expr.tvProp with
            | Some p0 => inj p0
            | None => inj (SepExpr.BadInj p)
          end
        | SEP.Star l r =>
          star (sexprD meta_env var_env l) (sexprD meta_env var_env r)
        | SEP.Exists t b =>
          ex _
          (fun x : Expr.tvarD types t =>
            sexprD meta_env (@existT _ (Expr.tvarD types) t x :: var_env) b)
        | SEP.Func f b =>
          match nth_error sfuncs f with
            | Some f' =>
              match
                Expr.applyD (Expr.exprD funcs meta_env var_env) 
                (SEP.SDomain f') b hprop (SEP.SDenotation f')
                with
                | Some p => p
                | None => inj (SepExpr.BadPredApply f b var_env)
              end
            | None => inj (SepExpr.BadPred f)
          end
        | SEP.Const p => p
      end.

  Definition cancel (himp : hprop -> hprop -> Prop) (emp : hprop) (star : hprop -> hprop -> hprop) 
    (ex : forall T : Type, (T -> hprop) -> hprop) (inj : Prop -> hprop)
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
          himp (nsexprD emp star ex inj funcs preds uvars nil lhs)
               (nsexprD emp star ex inj funcs preds uvars nil rhs)
        | Some {| CANCEL_TAC.AllExt := new_vars
                ; CANCEL_TAC.ExExt := new_uvars
                ; CANCEL_TAC.Lhs := lhs'
                ; CANCEL_TAC.Rhs := rhs'
                ; CANCEL_TAC.Subst := subst |} =>
          forallEach new_vars (fun nvs : env types =>
             let var_env := nvs in
             AllProvable_impl funcs uvars var_env
               (CANCEL_TAC.existsSubst funcs var_env subst 0
                 (map
                   (fun x : sigT (tvarD types) =>
                       existT (fun t : tvar => option (tvarD types t))
                         (projT1 x) (Some (projT2 x))) uvars ++
                    map
                      (fun x : tvar =>
                       existT (fun t : tvar => option (tvarD types t)) x None)
                      new_uvars)
                   (fun meta_env0 : env types =>
                    AllProvable_and funcs meta_env0 var_env
                      (himp
                         (nsexprD emp star ex inj funcs preds meta_env0 var_env
                            (SH.sheapD
                               {|
                               SH.impures := SH.impures lhs';
                               SH.pures := nil;
                               SH.other := SH.other lhs' |}))
                         (nsexprD emp star ex inj funcs preds meta_env0 var_env
                            (SH.sheapD
                               {|
                               SH.impures := SH.impures rhs';
                               SH.pures := nil;
                               SH.other := SH.other rhs' |})))
                      (SH.pures rhs'))) (SH.pures lhs'))

      end
    else
      himp (nsexprD emp star ex inj funcs preds uvars nil lhs)
           (nsexprD emp star ex inj funcs preds uvars nil rhs).
      

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
        (cancel himp emp star ex inj funcs preds algos uvars lhs rhs hyps) ->
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
      { eapply typeof_funcs_WellTyped_funcs. } }
    { apply H2. }
  Qed.

End canceller.