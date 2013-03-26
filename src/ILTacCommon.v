Require Import List.
Require Import MirrorShard.DepList.
Require Import MirrorShard.Expr MirrorShard.SepExpr MirrorShard.SepCancel.
Require Import MirrorShard.Prover.
Require Import MirrorShard.Tactics MirrorShard.Reflection.
Require Import MirrorShard.ExprUnify.

Require Import PropX.
Require Import TacPackIL ILEnv.
Require Import IL SepIL.
Require Import Word Memory.
Require Import SymILTac CancelTacIL.

Require Import Evm_compute.

Set Implicit Arguments.
Set Strict Implicit.

(*TIME
Add Rec LoadPath "/usr/local/lib/coq/user-contrib/" as Timing.  
Add ML Path "/usr/local/lib/coq/user-contrib/". 
Declare ML Module "Timing_plugin".
*)

(** Blacklist **)
(***************)
Ltac add_bl get l acc :=
  match l with 
    | @nil _ => acc
    | @List.cons _ ?X ?Y =>
      let t := get X in
        match t with
          (** this is a blacklist for the blacklist! *)
          | @nil _ => add_bl get Y acc
          | @cons _ => add_bl get Y acc
          | S => add_bl get Y acc
          | _ => 
            let acc := constr:(Evm_compute.Bcons _ t acc) in
              add_bl get Y acc
        end
  end.


(** isConst **)
(*************)

Ltac isConst_bool e :=
  match e with
    | true => true
    | false => true
    | _ => false
  end.

Ltac isConst e :=
  match e with
    | 0 => true
    | S ?e => isConst e
    | Rp => true
    | Rv => true
    | Sp => true
    | String.EmptyString => true
    | String.String ?e1 ?e2 =>
      match isConst e1 with
        | true => isConst e2
        | _ => false
      end
    | Ascii.Ascii ?a ?b ?c ?d ?e ?f ?g ?h =>
      match isConst_bool a with
        | true =>
          match isConst_bool b with
            | true =>
              match isConst_bool c with
                | true =>
                  match isConst_bool d with
                    | true =>
                      match isConst_bool e with
                        | true =>
                          match isConst_bool f with
                            | true =>
                              match isConst_bool g with
                                | true =>
                                  match isConst_bool h with
                                    | true => true
                                    | _ => false
                                  end
                                | _ => false
                              end
                            | _ => false
                          end
                        | _ => false
                      end
                    | _ => false
                  end
                | _ => false
              end
            | _ => false
          end
        | _ => false
      end
    | _ => false
  end.

(** Should reflect **)
(** TODO: This is probably deprecated **)
Ltac reflectable shouldReflect P :=
  match P with
    | @PropX.interp _ _ _ _ => false
    | @PropX.valid _ _ _ _ _ => false
    | forall x, _ => false
    | context [ PropX.PropX _ _ ] => false
    | context [ PropX.spec _ _ ] => false
    | _ => match type of P with
             | Prop => shouldReflect P
           end
  end.

Ltac shouldReflect P :=
  match P with
    | evalInstrs _ _ _ = _ => false
    | Structured.evalCond _ _ _ _ _ = _ => false
    | @PropX.interp _ _ _ _ => false
    | @PropX.valid _ _ _ _ _ => false
    | @eq ?X _ _ => 
      match X with
        | context [ PropX.PropX ] => false
        | context [ PropX.spec ] => false
      end
    | forall x, _ => false
    | exists x, _ => false
    | _ => true
  end.

(** Reduce Repr **)
Ltac reduce_repr ext sym ls :=
  match sym with
    | tt =>
      eval cbv beta iota zeta delta [ 
        ext
        Env.repr_combine Env.listToRepr Env.listOptToRepr Env.nil_Repr
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
        ILAlgoTypes.PACK.applyTypes
        ILAlgoTypes.PACK.applyFuncs
        ILAlgoTypes.PACK.applyPreds
        List.tl List.hd List.map Env.repr
        ILAlgoTypes.PACK.CE.core
        bedrock_types_r bedrock_funcs_r
        TacPackIL.ILAlgoTypes.Env
        BedrockCoreEnv.core 
      ] in ls
    | tt =>
      eval cbv beta iota zeta delta [ 
        Env.repr_combine Env.listToRepr Env.listOptToRepr Env.nil_Repr
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
        ILAlgoTypes.PACK.applyTypes
        ILAlgoTypes.PACK.applyFuncs
        ILAlgoTypes.PACK.applyPreds
        List.tl List.hd List.map Env.repr
        ILAlgoTypes.PACK.CE.core
        bedrock_types_r bedrock_funcs_r
        TacPackIL.ILAlgoTypes.Env
        BedrockCoreEnv.core 
      ] in ls
    | _ => 
      eval cbv beta iota zeta delta [
        sym ext
        Env.repr_combine Env.listToRepr Env.listOptToRepr Env.nil_Repr
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
        ILAlgoTypes.PACK.applyTypes
        ILAlgoTypes.PACK.applyFuncs
        ILAlgoTypes.PACK.applyPreds
        List.tl List.hd List.map Env.repr
        ILAlgoTypes.PACK.CE.core
        bedrock_types_r bedrock_funcs_r
        TacPackIL.ILAlgoTypes.Env
        BedrockCoreEnv.core 
      ] in ls
    | _ => 
      eval cbv beta iota zeta delta [
        sym
        Env.repr_combine Env.listToRepr Env.listOptToRepr Env.nil_Repr
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
        ILAlgoTypes.PACK.applyTypes
        ILAlgoTypes.PACK.applyFuncs
        ILAlgoTypes.PACK.applyPreds
        List.tl List.hd List.map Env.repr
        ILAlgoTypes.PACK.CE.core
        bedrock_types_r bedrock_funcs_r
        TacPackIL.ILAlgoTypes.Env
        BedrockCoreEnv.core 
      ] in ls
  end.

(** Cancellation **)
(******************)
Section canceller.
  Variable ts : list type.
  Let types := Env.repr BedrockCoreEnv.core ts.

  Require Import MirrorShard.Provers.
  Require Import Bool.

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


(*
  Definition ncancelResultD (himp : hprop -> hprop -> Prop) (emp : hprop) (star : hprop -> hprop -> hprop) (ex : forall T : Type, (T -> hprop) -> hprop) (inj : Prop -> hprop) := 
    fun (ts : list Expr.type) (fs : Expr.functions ts) (ps : SEP.predicates ts) =>
      fix cancelResultD (U G : Expr.env ts) (from : nat)
      (cr : CancelTacIL.CANCEL_LOOP.cancelResult ts) {struct cr} :
      Prop :=
      match cr with
        | CancelTacIL.CANCEL_LOOP.Done l r =>
          Expr.AllProvable_and fs U G
          (himp (nsexprD emp star ex inj fs ps U G (SH.sheapD l))
            (nsexprD emp star ex inj fs ps U G (SH.sheapD
              {|
                SH.impures := SH.impures r;
                SH.pures := nil;
                SH.other := SH.other r |}))) (SH.pures r)
        | CancelTacIL.CANCEL_LOOP.Quant alls pures exs sub r =>
          Expr.forallEach alls
          (fun Aext : Expr.env ts =>
            let G0 := G ++ Aext in
              Expr.AllProvable_impl fs U G0
              (CancelTacIL.CANCEL_LOOP.CANCEL_TAC.existsSubst fs G0 sub from
                (map
                  (fun x : sigT (Expr.tvarD ts) =>
                    @existT _ (fun x => option (Expr.tvarD ts x)) (projT1 x) (Some (projT2 x))) U ++
                  map (B := sigT (fun x => option (Expr.tvarD ts x))) 
                  (fun x : Expr.tvar => existT (fun x => option (Expr.tvarD ts x)) x None) exs)
                (fun U0 : Expr.env ts => cancelResultD U0 G0 r)) pures)
      end.

  Theorem ApplyCancelSep_slice 
    : forall (ts : list Expr.type)
      (funcs : Expr.functions (Env.repr ILEnv.BedrockCoreEnv.core ts))
      (preds : SEP.predicates (Env.repr ILEnv.BedrockCoreEnv.core ts))
      (algos : TacPackIL.ILAlgoTypes.AllAlgos
        (Env.repr ILEnv.BedrockCoreEnv.core ts)),
      TacPackIL.ILAlgoTypes.AllAlgos_correct (types := Env.repr ILEnv.BedrockCoreEnv.core ts) funcs preds algos ->
      forall (uvars : Expr.env (Env.repr ILEnv.BedrockCoreEnv.core ts))
        (lhs rhs : SEP.sexpr (Env.repr ILEnv.BedrockCoreEnv.core ts))
        (hyps : Expr.exprs (Env.repr ILEnv.BedrockCoreEnv.core ts)),
        Expr.AllProvable funcs uvars nil hyps ->
        (let funcs := funcs in
         let preds := preds in
         let uvars := uvars in
         let lhs := lhs in
         let rhs := rhs in
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
         let '(x, y) :=
           CancelTacIL.CANCEL_LOOP.cancel (SEP.typeof_preds preds)
           prover (TacPackIL.UNF.Forward hints)
           (TacPackIL.UNF.Backward hints) bound hyps
           (Expr.typeof_env uvars) nil lhs rhs in
           if (SEP.WellTyped_sexpr (Expr.typeof_funcs funcs)
             (SEP.typeof_preds preds) (Expr.typeof_env uvars) nil rhs && y)%bool
           then ncancelResultD himp emp star ex inj funcs preds uvars nil x
           else himp (nsexprD emp star ex inj funcs preds uvars nil lhs)
                     (nsexprD emp star ex inj funcs preds uvars nil rhs)) ->
        SEP.himp funcs preds uvars nil lhs rhs.
  Proof. Admitted.
*)
(*
  Theorem ApplyCancelSep_with_eq1 :
    forall (funcs : functions types)
      (preds : SEP.predicates types) (prover : ProverT types)
      (algos : TacPackIL.ILAlgoTypes.AllAlgos types)
      (algosC : @TacPackIL.ILAlgoTypes.AllAlgos_correct types funcs preds algos)
      (uvars : env types) (lhs rhs : SEP.sexpr types)
      (hyps : exprs types) (tfuncs : tfunctions)
      (tpreds : SEP.tpredicates) (tuvars : tenv)
      (cr : CANCEL_LOOP.cancelResult types) (prog : bool),
      ProverT_correct prover funcs ->
      typeof_funcs funcs = tfuncs ->
      SEP.typeof_preds preds = tpreds ->
      WellTyped_env tuvars uvars ->
      SEP.WellTyped_sexpr tfuncs tpreds tuvars nil rhs = true ->
      AllProvable funcs uvars nil hyps ->
      (let bound := 10 in
       let hints :=
         match TacPackIL.ILAlgoTypes.Hints algos with
           | None => {| UNF.Forward := nil ; UNF.Backward := nil |}
           | Some x => x
         end
       in
       CANCEL_LOOP.cancel tpreds prover (UNF.Forward hints) (UNF.Backward hints) bound hyps tuvars nil lhs rhs = (cr, prog))
      ->
      (if prog
        then CANCEL_LOOP.cancelResultD funcs preds uvars nil cr
        else SEP.himp funcs preds uvars nil lhs rhs) ->
      SEP.himp funcs preds uvars nil lhs rhs.
  Proof.
    exact CANCEL_LOOP.cancelLoop_with_eq'.
  Qed.
*)
  
(*
  Print CANCEL_LOOP.
  

  Lemma ApplyCancelSep_with_eq : 
    forall (algos_correct : ILAlgoTypes.AllAlgos_correct funcs preds algos),
    forall (meta_env : Expr.env (Env.repr BedrockCoreEnv.core types)) (hyps : Expr.exprs (_)),

    forall (l r : SEP.sexpr types BedrockCoreEnv.pc BedrockCoreEnv.st) res,
    Expr.AllProvable funcs meta_env nil hyps ->
    canceller preds algos (typeof_env meta_env) hyps l r = Some res ->
    forall (WTR : SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env meta_env) nil r = true) cs,
    match res with
      | {| AllExt := new_vars
         ; ExExt  := new_uvars
         ; Lhs    := lhs'
         ; Rhs    := rhs'
         ; Subst  := subst
         |} =>
        Expr.forallEach new_vars (fun nvs : Expr.env types =>
          let var_env := nvs in
          Expr.AllProvable_impl funcs meta_env var_env
          (existsSubst funcs var_env subst 0 
            (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env ++
             map (fun x => existT (fun t => option (tvarD types t)) x None) new_uvars)
            (fun meta_env : Expr.env types =>
                (Expr.AllProvable_and funcs meta_env var_env
                  (himp cs 
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures lhs') nil (SH.other lhs'))))
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures rhs') nil (SH.other rhs')))))
                  (SH.pures rhs')) ))
            (SH.pures lhs'))
    end ->
    himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
            (@SEP.sexprD _ _ _ funcs preds meta_env nil r).
  Proof. intros. eapply ApplyCancelSep_with_eq'; eauto. Qed.
*)

(*
  Lemma ApplyCancelSep : forall (types : list type) (funcs : functions types)
      (preds : SEP.predicates types) (prover : ProverT types)
      (hintsFwd hintsBwd : list (SEP_LEMMA.sepLemma types)) 
      (bound : nat) (uvars : env types) (lhs rhs : SEP.sexpr types)
      (hyps : exprs types) (tfuncs : tfunctions)
      (tpreds : SEP.tpredicates) (tuvars : tenv),
      ProverT_correct prover funcs ->
      typeof_funcs funcs = tfuncs ->
      SEP.typeof_preds preds = tpreds ->
      WellTyped_env tuvars uvars ->
      SEP.WellTyped_sexpr tfuncs tpreds tuvars nil rhs = true ->
      AllProvable funcs uvars nil hyps ->
      UNF.hintSideD funcs preds hintsFwd ->
      UNF.hintSideD funcs preds hintsBwd ->
      let '(cr,prog) := CANCEL_LOOP.cancel tpreds prover hintsFwd hintsBwd bound hyps tuvars nil lhs rhs in
      match prog with
        | true => CANCEL_LOOP.cancelResultD funcs preds uvars nil 0 cr
        | false => SEP.himp funcs preds uvars nil lhs rhs
      end ->
      SEP.himp funcs preds uvars nil lhs rhs.
  Proof. 
    intros. consider (CANCEL_LOOP.cancel tpreds prover hintsFwd hintsBwd bound hyps tuvars nil lhs rhs); intros.
(*    eapply ApplyCancelSep_with_eq in H6; eassumption. *)
  Admitted.
*)

End canceller.

Lemma ignore_regs : forall p specs stn st rs,
  interp specs (![ p ] (stn, st))
  -> interp specs (![ p ] (stn, {| Regs := rs; Mem := Mem st |})).
Proof.
  rewrite sepFormula_eq; auto.
Qed.

Lemma interp_interp_himp : forall cs P Q stn_st,
  interp cs (![ P ] stn_st) ->
  (himp P Q) ->
  interp cs (![ Q ] stn_st).
Proof.
  unfold himp. intros. destruct stn_st.
  rewrite sepFormula_eq in *. unfold sepFormula_def in *. simpl in *.
  eapply Imply_E; eauto. 
Qed.

Theorem change_Imply_himp : forall p q s,
  himp p q
  -> forall specs, interp specs (![p] s ---> ![q] s)%PropX.
Proof.
  rewrite sepFormula_eq.
  unfold himp, sepFormula_def.
  eauto.
Qed.


Ltac change_to_himp := try apply ignore_regs;
  match goal with
    | [ H : interp ?specs (![ _ ] ?X)
      |- interp ?specs (![ _ ] ?X) ] =>
      eapply (@interp_interp_himp _ _ _ _ H)
    | [ |- _ ===> _ ] => unfold Himp
    | _ => apply change_Imply_himp
  end.

Definition smem_read stn := SepIL.smem_read_word stn. 
Definition smem_write stn := SepIL.smem_write_word stn. 

(** Symbolic Execution **)
(************************)
Require Import ReifyIL.
Lemma Some_cong : forall A (x y : A),
  x = y
  -> Some x = Some y.
  congruence.
Qed.

Ltac find_reg st r :=
  match goal with
    | [ H : Regs st r = ?x |- _ ] => constr:((x, Some_cong (eq_sym H)))
    | _ => constr:((Regs st r, @refl_equal (option W) (Some (Regs st r))))
  end.

Ltac open_stateD H0 :=
  cbv beta iota zeta delta 
    [ SymIL.stateD Expr.exprD Expr.applyD
      EquivDec.equiv_dec 
      Expr.Range Expr.Domain Expr.Denotation
      Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
      sumbool_rec sumbool_rect
      Peano_dec.eq_nat_dec nat_rec nat_rect eq_rec_r eq_rec eq_rect eq_sym
      nth_error map value
      f_equal

      Expr.AllProvable Expr.Provable Expr.tvarD comparator
    ] in H0; 
    let a := fresh in 
    let b := fresh in
    let zz := fresh in destruct H0 as [ a [ b zz ] ] ;
    destruct a as [ ? [ ? ? ] ];
    repeat match type of zz with
             | True => clear zz
             | _ /\ _ => let v := fresh in destruct zz as [ v zz ]
           end.

Ltac get_instrs st :=
  let rec find_exact H Hs :=
    match Hs with
      | tt => false
      | (H, _) => true
      | (_, ?Hs) => find_exact H Hs
    end
  in
  let rec get_instrs st ignore :=
    match goal with
      | [ H : Structured.evalCond ?l _ ?r _ st = Some _ |- _ ] =>
        match find_exact H ignore with
          | false =>
            let ignore := constr:((H, ignore)) in
            let v := get_instrs st ignore in
            constr:((((l,r), H), v))
        end
      | [ H : Structured.evalCond ?l _ ?r _ st = None |- _ ] =>
        constr:((((l,r), H), tt))
      | [ H : evalInstrs _ st ?is = Some ?X |- _ ] =>
        let v := get_instrs X tt in
        constr:(((is, H), v))
      | [ H : evalInstrs _ st ?is = None |- _ ] =>
        constr:(((is, H), tt))
      | [ |- _ ] => tt
    end
  in get_instrs st tt.

Ltac clear_instrs ins :=
  match ins with
    | tt => idtac
    | ((_,?H), ?ins) => clear H; clear_instrs ins
  end.

Ltac collectAllTypes_instrs is Ts k :=
  match is with
    | tt => k Ts
    | (((?l,?r), _), ?is) =>
       collectTypes_rvalue ltac:(isConst) l Ts ltac:(fun Ts =>
         collectTypes_rvalue ltac:(isConst) r Ts ltac:(fun Ts =>
          collectAllTypes_instrs is Ts k))
    | ((?i, _), ?is) =>
      collectTypes_instrs ltac:(isConst) i Ts ltac:(fun Ts =>
        collectAllTypes_instrs is Ts k)
  end.

Ltac build_path types instrs st uvars vars funcs k :=
  match instrs with
    | tt => 
      let is := constr:(nil : @SymIL.istream types) in
      let pf := constr:(refl_equal (Some st)) in
      k uvars funcs is (Some st) pf
    | ((?i, ?H), ?is) =>
      match type of H with
        | Structured.evalCond ?l ?t ?r _ ?st = ?st' =>
          reify_rvalue ltac:(isConst) l types funcs uvars vars ltac:(fun uvars funcs l =>
            reify_rvalue ltac:(isConst) r types funcs uvars vars ltac:(fun uvars funcs r =>
              match st' with
                | None => 
                  let i := constr:(inr (@SymIL.SymAssertCond types l t r st') :: (nil : @SymIL.istream types)) in
                  k uvars funcs i (@None state) H
                | Some ?st'' => 
                  build_path types is st uvars vars funcs ltac:(fun uvars funcs is sf pf =>
                    let i := constr:(inr (@SymIL.SymAssertCond types l t r st') :: is) in
                    let pf := constr:(@conj _ _ H pf) in
                    k uvars funcs i sf pf)
              end))
        | evalInstrs _ ?st _ = ?st' =>
          reify_instrs ltac:(isConst) i types funcs uvars vars ltac:(fun uvars funcs sis =>
            match st' with
              | None => 
                let i := constr:(inl (sis, None) :: (nil : @SymIL.istream types)) in
                  k uvars funcs i (@None state) H
              | Some ?st'' =>
                build_path types is st'' uvars vars funcs ltac:(fun uvars funcs is sf pf =>
                  let i := constr:(inl (sis, st') :: is) in
                  let pf := constr:(@conj _ _ H pf) in
                  k uvars funcs i sf pf)
            end)
      end
  end.
