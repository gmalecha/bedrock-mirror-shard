(** This file implements the tactics for symbolic evaluation for the
 ** language defined in IL.v
 **)
Require Import List.
Require Import MirrorShard.Tactics MirrorShard.Reflection.
Require Import MirrorShard.SepExpr SymEval.
Require Import MirrorShard.Expr MirrorShard.ReifyExpr.
Require Import MirrorShard.Prover.
Require Import MirrorShard.Provers.
Require Import MirrorShard.Quantifier.
Require Import MirrorShard.Env MirrorShard.TypedPackage.
Require MirrorShard.Folds.
Require Import IL SepIL SymIL SymILProofs.
Require Import Word Memory.
Require Import PropX.
Require Import TacPackIL.

Require Structured SymEval.
Require Import ILEnv.

Set Implicit Arguments.
Set Strict Implicit.

(** The Symbolic Evaluation Interfaces *)
Module MEVAL := SymIL.MEVAL.

(** The instantiation of the learn hook with the unfolder **)
Section unfolder_learnhook.
  Variable types : list type.
  Variable hints : UNF.hintsPayload (repr bedrock_types_r types).

  Definition unfolder_LearnHook : MEVAL.LearnHook (repr bedrock_types_r types) 
    (SymState (repr bedrock_types_r types)) :=
    fun prover meta_vars vars_vars st facts ext => 
      match SymMem st with
        | Some m =>
          match fst (UNF.forward (UNF.Forward hints) prover 10 facts
            {| UNF.Vars := vars_vars
             ; UNF.UVars := meta_vars
             ; UNF.Heap := m
             |})
            with
            | {| UNF.Vars := vs ; UNF.UVars := us ; UNF.Heap := m |} =>
              (** assert (us = meta_vars) **)
              ({| SymMem := Some m
                ; SymRegs := SymRegs st
                ; SymPures := SymPures st ++ SH.pures m
                |}, qex (skipn (length vars_vars) vs) QBase)
          end
        | None => (st, QBase)
      end.

  Variable funcs : functions (repr bedrock_types_r types).
  Variable preds : SEP.predicates (repr bedrock_types_r types).
  Hypothesis hints_correct : UNF.hintsSoundness funcs preds hints.

  (** TODO : move to SymILProofs **)
  Lemma stateD_WellTyped_sheap : forall uvars vars cs stn_st s SymRegs SymPures,
    stateD funcs preds uvars vars cs stn_st {| SymMem := Some s; SymRegs := SymRegs; SymPures := SymPures |} ->
    SH.WellTyped_sheap (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env uvars) (typeof_env vars) s = true.
  Proof.
    clear. intros. unfold stateD in H.
    destruct stn_st. destruct SymRegs. destruct p. intuition. generalize H. clear; intros.
    rewrite sepFormula_eq in H. unfold sepFormula_def in *. simpl in H.
    rewrite SH.WellTyped_sheap_WellTyped_sexpr.
    eapply interp_WellTyped_sexpr; eauto.
  Qed.

  Lemma interp_existsEach : forall ts cs vs P stn st,
    PropX.interp cs ((UNF.ST_EXT.existsEach vs P) stn st) ->
    exists G : env ts, map (@projT1 _ _) G = vs /\ PropX.interp cs ((P G) stn st). 
  Proof.
    intros. apply STK.interp_ex in H. destruct H. exists x.
    apply STK.interp_star in H. 
    repeat match goal with
             | [ H : exists x, _ |- _ ] => destruct H
             | [ H : _ /\ _ |- _ ] => destruct H
           end.
    apply STK.interp_pure in H0. intuition.
    PropXTac.propxFo. subst. eapply split_emp in H; eauto. unfold smem_eqv in *. subst; auto.
  Qed.

  Theorem unfolderLearnHook_correct 
    : @MEVAL.LearnHook_correct (repr bedrock_types_r types) _ BedrockCoreEnv.pc BedrockCoreEnv.st (@unfolder_LearnHook) 
    (@stateD _ funcs preds) funcs preds.
  Proof.
    Opaque repr UNF.forward.
    unfold unfolder_LearnHook. econstructor. intros. generalize dependent 10. intros.

    destruct ss. simpl in *.
    destruct SymMem; simpl; intros.
    { remember (UNF.forward (UNF.Forward hints) P n pp
      {| UNF.Vars := typeof_env vars
        ; UNF.UVars := typeof_env uvars
        ; UNF.Heap := s |}).
      destruct p. simpl in *.
      destruct u; simpl in *.
      symmetry in Heqp.
      eapply UNF.forwardOk in Heqp; eauto using typeof_env_WellTyped_env, UNF.ForwardOk.
      Focus 2. simpl.
      eapply stateD_WellTyped_sheap. eauto. simpl in *.
      inversion H2; clear H2; subst.

      apply quantD_qex_QEx. simpl.
      unfold stateD in *. destruct stn_st. destruct SymRegs. destruct p. intuition.
      repeat match goal with
               | [ H : match ?X with _ => _ end |- _ ] => 
                 consider X; intros; try contradiction
             end.
      intuition; subst.
      rewrite Heqp in H.
      rewrite sepFormula_eq in H. unfold sepFormula_def in *. simpl in H.
      eapply interp_existsEach in H. destruct H.
      apply existsEach_sem. exists x. destruct H. split.
      unfold typeof_env. simpl in *. rewrite map_length. rewrite <- H.
      apply map_ext. auto.
      rewrite <- app_nil_r with (l := uvars).
      repeat erewrite exprD_weaken by eassumption. intuition.
      rewrite <- app_nil_r with (l := vars ++ x). rewrite <- UNF.HEAP_FACTS.SEP_FACTS.sexprD_weaken.
      apply interp_satisfies. intuition. apply SM.memoryIn_sound.
      apply AllProvable_app' in H4. destruct H4. repeat apply AllProvable_app; eauto using AllProvable_weaken.
      rewrite app_nil_r. eapply sheapD_pures. eapply H6.
      rewrite app_nil_r. eapply sheapD_pures. eapply H6. }
    { inversion H2. subst. simpl. auto. }
  Qed.
  Transparent UNF.forward.
End unfolder_learnhook.

(** Unfortunately, most things can change while evaluating a stream,
 ** so we have to move it outside the sections
 **)
Section stream_correctness.
  Variable types' : list type.
  Notation TYPES := (repr bedrock_types_r types').

  Notation pcT := (tvType 0).
  Notation tvWord := (tvType 0).
  Notation stT := (tvType 1).
  Notation tvState := (tvType 2).
  Notation tvTest := (tvType 3).
  Notation tvReg := (tvType 4).

  Variable funcs' : functions TYPES.
  Notation funcs := (repr (bedrock_funcs_r types') funcs').
  Variable preds : SEP.predicates TYPES.

  Lemma skipn_length : forall T (ls : list T) n,
    length ls = n ->
    skipn n ls = nil.
  Proof.
    clear. intros; subst; induction ls; simpl; auto.
  Qed.

  Lemma skipn_app_first : forall T (ls ls' : list T) n,
    length ls = n ->
    skipn n (ls ++ ls') = ls'.
  Proof.
    clear; intros; subst; induction ls; auto.
  Qed.

  Lemma interp_ex : forall cs T (P : T -> hprop) stn_st,
    interp cs (![ST.ex P] stn_st) ->
    exists v, interp cs (![P v] stn_st).
  Proof.
    clear. intros.
    rewrite sepFormula_eq in *. destruct stn_st. unfold sepFormula_def in *. simpl in *.
    unfold ST.ex in H. apply interp_sound in H. auto.
  Qed.

  Lemma interp_pull_existsEach : forall cs P stn_st uvars vars' vars,
    interp cs (![SEP.sexprD funcs preds uvars vars (SEP.existsEach vars' P)] stn_st) ->
    exists env', map (@projT1 _ _) env' = vars' /\
      interp cs (![SEP.sexprD funcs preds uvars (rev env' ++ vars) P] stn_st).
  Proof.
    clear. 
    induction vars'; simpl; intros.
    exists nil; simpl; eauto.
    
    apply interp_ex in H.
    destruct H. eapply IHvars' in H. destruct H. intuition. exists (existT (tvarD TYPES) a x :: x0).
    simpl in *. rewrite H0. intuition eauto. rewrite app_ass. simpl. auto.
  Qed.
  
  Theorem stateD_proof_no_heap :
    forall (uvars : Expr.env TYPES) (st : state) (sp rv rp : Expr.expr TYPES),
      let vars := nil in
      exprD funcs uvars vars sp tvWord = Some (Regs st Sp) ->
      exprD funcs uvars vars rv tvWord = Some (Regs st Rv) ->
      exprD funcs uvars vars rp tvWord = Some (Regs st Rp) ->
      forall pures : list (Expr.expr TYPES),
        Expr.AllProvable funcs uvars vars pures ->
        forall (cs : codeSpec W (settings * state)) (stn : settings),
          qstateD funcs preds uvars vars cs (stn, st) QBase
          {| SymMem := None
           ; SymRegs := (sp, rp, rv)
           ; SymPures := pures
           |}.
  Proof.
    Opaque repr.
    unfold qstateD. intros. simpl in *.
    repeat match goal with
             | [ H : _ = _ |- _ ] => rewrite H
           end.
    intuition auto. 
  Qed.

  Theorem stateD_proof : (* vars = nil *)
    forall (uvars : Expr.env TYPES) (st : state) (sp rv rp : Expr.expr TYPES),
      let vars := nil in
      exprD funcs uvars vars sp tvWord = Some (Regs st Sp) ->
      exprD funcs uvars vars rv tvWord = Some (Regs st Rv) ->
      exprD funcs uvars vars rp tvWord = Some (Regs st Rp) ->
      forall pures : list (Expr.expr TYPES),
        Expr.AllProvable funcs uvars vars pures ->
        forall (sh : SEP.sexpr TYPES) (hashed : SH.SHeap TYPES) vars',
          SH.hash sh = (vars', hashed) ->
          forall (cs : codeSpec W (settings * state)) (stn : settings),
            interp cs (![SEP.sexprD funcs preds uvars vars sh] (stn, st)) ->
            qstateD funcs preds uvars vars cs (stn, st) (QEx (rev vars') QBase)
              {| SymMem := Some hashed
               ; SymRegs := (sp, rp, rv)
               ; SymPures := pures
               |}.
  Proof.
    unfold qstateD. intros. simpl.
    generalize (SH.hash_denote funcs preds uvars nil sh). rewrite H3. simpl in *.
    intro XX. rewrite XX in H4. 

    apply interp_pull_existsEach in H4. destruct H4. intuition.
    rewrite <- H5. rewrite app_nil_r in *. apply existsEach_sem.
    exists (rev x). split; eauto. unfold typeof_env. rewrite map_rev. auto.

    change (rev x) with (nil ++ rev x).
    rewrite <- app_nil_r with (l := uvars).
    repeat (erewrite exprD_weaken by eassumption). intuition.
    rewrite app_nil_r. intuition eauto. 

    apply AllProvable_app; auto.
    { eapply AllProvable_weaken. eauto. }
    { rewrite sepFormula_eq in H6. unfold sepFormula_def in H6. simpl in H6.
      eapply sheapD_pures. rewrite app_nil_r. eauto. }
  Qed.

End stream_correctness.


(** Tactic Lemmas **)

Section correctness.
  Variable types' : list type.
  Notation TYPES := (repr bedrock_types_r types').

  Notation pcT := BedrockCoreEnv.pc.
  Notation tvWord := (tvType 0).
  Notation stT := BedrockCoreEnv.st.
  Notation tvState := (tvType 2).
  Notation tvTest := (tvType 3).
  Notation tvReg := (tvType 4).

  Variable funcs' : functions TYPES.
  Notation funcs := (repr (bedrock_funcs_r types') funcs').
  Variable preds : SEP.predicates TYPES.

  Variable algos : ILAlgoTypes.AllAlgos TYPES.
  Variable algos_correct : @ILAlgoTypes.AllAlgos_correct TYPES funcs preds algos.

  (** Unfolding may have introduced some new variables, which we quantify existentially. *)
  Fixpoint quantifyNewVars (vs : variables) (en : env TYPES) (k : env TYPES -> Prop) : Prop :=
    match vs with
      | nil => k en
      | v :: vs' => exists x, quantifyNewVars vs' (en ++ existT _ v x :: nil) k
    end.


  Lemma stateD_AllProvable_pures : forall meta_env vars stn_st ss cs,
    stateD funcs preds meta_env vars cs stn_st ss ->
    AllProvable funcs meta_env vars
    match SymMem ss with
      | Some m0 => SH.pures m0 ++ SymPures ss
      | None => SymPures ss
    end.
  Proof.
    Opaque repr.
    clear. unfold stateD. destruct ss; simpl. destruct stn_st. destruct SymRegs. destruct p.
    intuition. destruct SymMem; auto. apply AllProvable_app' in H2; apply AllProvable_app; intuition.
  Qed.

  Definition sym_eval uvars path qs_env ss :=
    let new_pures := 
      match SymMem ss with
        | None => SymPures ss
        | Some m => SH.pures m ++ SymPures ss
      end in
    let prover := match ILAlgoTypes.Prover algos with
                    | None => trivialProver TYPES
                    | Some p => p
                  end in
    let meval := match ILAlgoTypes.MemEval algos with
                   | None => MEVAL.Default.MemEvaluator_default TYPES
                   | Some me => me
                 end in
    let unfolder := match ILAlgoTypes.Hints algos with
                      | None => @MEVAL.LearnHookDefault.LearnHook_default TYPES _
                      | Some h => unfolder_LearnHook h 
                    end in
    let facts := Summarize prover new_pures in
    let uvars := uvars ++ gatherAll qs_env in
    let vars := gatherEx qs_env in
    (** initial unfolding **)
    let (ss,qs) := unfolder prover uvars vars ss facts new_pures in
    @sym_evalStream _ prover meval unfolder facts path (appendQ qs qs_env) (uvars ++ gatherAll qs) (vars ++ gatherEx qs) ss.

  Theorem Apply_sym_eval_with_eq : forall stn meta_env sound_or_safe st path,   
    istreamD funcs meta_env nil path stn st sound_or_safe ->
    forall cs qs ss res,
      qstateD funcs preds meta_env nil cs (stn,st) qs ss ->
      sym_eval (typeof_env meta_env) path qs ss = res ->
      match res with
        | Safe qs' ss' =>
          quantD nil meta_env qs' (fun vars_env meta_env =>
            match sound_or_safe with
              | None => False
              | Some (st') => stateD funcs preds meta_env vars_env cs (stn, st') ss'
              end)
        | SafeUntil qs' ss' is' =>
          quantD nil meta_env qs' (fun vars_env meta_env =>
            exists st' : state,
              stateD funcs preds meta_env vars_env cs (stn, st') ss' /\
              istreamD funcs meta_env vars_env is' stn st' sound_or_safe)
      end.
  Proof.
    intros. unfold sym_eval in *.
    assert (PC : ProverT_correct
              match ILAlgoTypes.Prover algos with
              | Some p => p
              | None => Provers.trivialProver TYPES
              end (repr (bedrock_funcs_r types') funcs)).
    { generalize (ILAlgoTypes.Acorrect_Prover algos_correct).
      destruct (ILAlgoTypes.Prover algos); intros; auto.
      apply Provers.trivialProver_correct. }
    generalize dependent (match ILAlgoTypes.Prover algos with
                            | Some p => p
                            | None => Provers.trivialProver TYPES
                          end).
    assert (MC : SymILProofs.MEVAL.MemEvaluator_correct pcT stT
      match ILAlgoTypes.MemEval algos with
      | Some me => me
      | None => MEVAL.Default.MemEvaluator_default TYPES
      end (repr (bedrock_funcs_r types') funcs) preds tvWord tvWord
      (IL_mem_satisfies (ts:=types')) (IL_ReadWord (ts:=types'))
      (IL_WriteWord (ts:=types')) (IL_ReadByte (ts:=types')) (IL_WriteByte (ts:=types'))).
    { generalize (ILAlgoTypes.Acorrect_MemEval algos_correct).
      destruct (ILAlgoTypes.MemEval algos); auto; intros.
      apply SymIL.MEVAL.Default.MemEvaluator_default_correct. }
    generalize dependent (match ILAlgoTypes.MemEval algos with
                            | Some me => me
                            | None => MEVAL.Default.MemEvaluator_default TYPES
                          end).
    match goal with
      | [ |- context [ ?X ] ] =>
        match X with 
          | match ILAlgoTypes.Hints _ with _ => _ end =>
            assert (LC : SymILProofs.MEVAL.LearnHook_correct (types_ := TYPES) (tvType 0) (tvType 1) X
              (stateD funcs preds) (repr (bedrock_funcs_r types') funcs) preds); [ | generalize dependent X ]
        end
    end.
    { generalize (ILAlgoTypes.Acorrect_Hints algos_correct).     
      destruct (ILAlgoTypes.Hints algos); auto; intros.
      { apply (@unfolderLearnHook_correct types' h funcs preds H1). } 
      { apply SymIL.MEVAL.LearnHookDefault.LearnHook_default_correct. } }
    intros l LC m MC p ? PC.
    match goal with 
      | [ H : context [ l ?A ?B ?C ?D ?E ?F ] |- _ ] =>
        consider (l A B C D E F); intros
    end.
    unfold qstateD in *. destruct res.
    Opaque stateD.
    { destruct (SymILProofs.SymIL_Correct.sym_evalStream_quant_append _ _ _ _ _ _ _ _ _ H2).
      subst. rewrite <- appendQ_assoc. rewrite quantD_app. eapply quantD_impl; eauto; intros. clear H0.
      simpl in *.
      match goal with 
        | [ H : context [ @Summarize _ ?A ?B ] |- _ ] => 
          assert (AP : AllProvable funcs (meta_env ++ b) a B); [ eauto using stateD_AllProvable_pures |
            assert (VF : Valid PC (meta_env ++ b) a (Summarize A B)); 
              [ clear H; eauto using Summarize_correct | generalize dependent (Summarize A B); generalize dependent B ; intros ] ]
      end.
      eapply (@SymILProofs.MEVAL.hook_sound _ _ _ _ _ _ _ _ LC _ PC (meta_env ++ b) a cs (stn,st)) in H5; eauto.
      2: etransitivity; [ | eapply H1 ]. 2: f_equal; eauto. 2: rewrite typeof_env_app; f_equal; auto.
      rewrite quantD_app. eapply quantD_impl; eauto; intros. simpl in *.

      eapply (@SymILProofs.SymIL_Correct.evalStream_correct_Safe TYPES funcs preds _ PC _ MC _ LC sound_or_safe cs
        stn path f s QBase x s0 ((typeof_env meta_env ++ gatherAll qs) ++ gatherAll q) (gatherEx qs ++ gatherEx q) (appendQ q qs)
        H2).
      { repeat (progress simpl || rewrite typeof_env_app || rewrite app_nil_r); f_equal; auto. f_equal; auto. }
      { repeat (progress simpl || rewrite typeof_env_app || rewrite app_nil_r); f_equal; auto. }
      { apply SymILProofs.SymIL_Correct.istreamD_weaken with (B := b ++ b0) (D := a ++ a0) in H.
        rewrite repr_idempotent. rewrite app_ass. apply H. }
      { simpl. intuition. eapply Valid_weaken. eauto. } }
    { destruct (SymILProofs.SymIL_Correct.sym_evalStream_quant_append _ _ _ _ _ _ _ _ _ H2).
      subst. rewrite <- appendQ_assoc. rewrite quantD_app. eapply quantD_impl; eauto; intros. clear H0.
      simpl in *.
      match goal with 
        | [ H : context [ @Summarize _ ?A ?B ] |- _ ] => 
          assert (AP : AllProvable funcs (meta_env ++ b) a B); [ eauto using stateD_AllProvable_pures |
            assert (VF : Valid PC (meta_env ++ b) a (Summarize A B)); 
              [ clear H; eauto using Summarize_correct | generalize dependent (Summarize A B); generalize dependent B ; intros ] ]
      end.
      eapply (@SymILProofs.MEVAL.hook_sound _ _ _ _ _ _ _ _ LC _ PC (meta_env ++ b) a cs (stn,st)) in H5; eauto.
      2: etransitivity; [ | eapply H1 ]. 2: f_equal; eauto. 2: rewrite typeof_env_app; f_equal; auto.
      rewrite quantD_app. eapply quantD_impl; eauto; intros. simpl in *.

      eapply (@SymILProofs.SymIL_Correct.evalStream_correct_SafeUntil TYPES funcs preds _ PC _ MC _ LC sound_or_safe cs
        stn path f s QBase x s0); eauto.  (*((typeof_env meta_env ++ gatherAll qs) ++ gatherAll q) (gatherEx qs ++ gatherEx q) (appendQ q qs)
        H2). *)
      { repeat (progress simpl || rewrite typeof_env_app || rewrite app_nil_r); f_equal; auto. f_equal; auto. }
      { repeat (progress simpl || rewrite typeof_env_app || rewrite app_nil_r); f_equal; auto. }
      { apply SymILProofs.SymIL_Correct.istreamD_weaken with (B := b ++ b0) (D := a ++ a0) in H.
        rewrite repr_idempotent. rewrite app_ass. apply H. }
      { simpl. intuition. eapply Valid_weaken. eauto. } }
  Qed.
End correctness.

Require Import MirrorShard.SepExprTac.
Module SEP_TAC := SepExprTac.Make SepIL.ST SepIL.SEP.

Section abstracted.

  Variable types' : list type.
  Notation TYPES := (repr bedrock_types_r types').

  Notation pcT := BedrockCoreEnv.pc.
  Notation tvWord := (tvType 0).
  Notation stT := BedrockCoreEnv.st.
  Notation tvState := (tvType 2).
  Notation tvTest := (tvType 3).
  Notation tvReg := (tvType 4).

  Variable funcs : functions TYPES.
(*  Notation funcs := (repr (bedrock_funcs_r types') funcs'). *)
  Variable preds : SEP.predicates TYPES.

  Variable algos : ILAlgoTypes.AllAlgos TYPES.

  Variable interp : codeSpec W (IL.settings * IL.state) -> PropX.PropX W (IL.settings * IL.state) -> Prop.
  Variables (emp : hprop) (star : hprop -> hprop -> hprop) (ex : forall T : Type, (T -> hprop) -> hprop) (inj : Prop -> hprop) (not : Prop -> Prop).
  Variable Regs : state -> regs.

  Definition nstateD (uvars vars : env TYPES) cs (stn_st : IL.settings * state) (ss : SymState TYPES) : Prop :=
    let (stn,st) := stn_st in
      match ss with
        | {| SymMem := m ; SymRegs := (sp, rp, rv) ; SymPures := pures |} =>
          match 
            ExprTac.nexprD not _ funcs uvars vars sp tvWord ,
            ExprTac.nexprD not _ funcs uvars vars rp tvWord ,
            ExprTac.nexprD not _ funcs uvars vars rv tvWord
            with
            | Some sp , Some rp , Some rv =>
              Regs st Sp = sp /\ Regs st Rp = rp /\ Regs st Rv = rv
            | _ , _ , _ => False
          end
          /\ match m with 
               | None => True
               | Some m => 
                 interp cs (SepIL.SepFormula.sepFormula (SEP_TAC.nsexprD not emp star ex inj _ funcs preds uvars vars (SH.sheapD m)) stn_st)%PropX
             end
          /\ ExprTac.nAllProvable_and not _ funcs uvars vars True (match m with 
                                                                     | None => pures
                                                                     | Some m => pures ++ SH.pures m
                                                                   end)
      end.

  Definition qstateD (uvars vars : env TYPES) cs (stn_st : IL.settings * state) (qs : Quantifier.Quant) 
    (ss : SymState TYPES) : Prop :=
    Quantifier.quantD vars uvars qs (fun vars_env meta_env => nstateD meta_env vars_env cs stn_st ss).

  Definition sym_eval_prop sound_or_safe cs meta_env stn path qs_env ss :=
    match sym_eval algos (typeof_env meta_env) path qs_env ss  with
      | Safe qs' ss' =>
        quantD nil meta_env qs' (fun vars_env meta_env =>
          match sound_or_safe with
            | None => False
            | Some st' => nstateD meta_env vars_env cs (stn, st') ss'
          end)
      | SafeUntil qs' ss' is' =>
        quantD nil meta_env qs' (fun vars_env meta_env =>
          exists st' : state,
            nstateD meta_env vars_env cs (stn, st') ss' /\
            istreamD funcs meta_env vars_env is' stn st' sound_or_safe)
    end.

End abstracted.

Theorem nstateD_stateD : forall ts fs ps us vs cs s ss,
  nstateD fs ps (@interp _ _) ST.emp star ex inj not Regs us vs cs s ss
  <->
  @stateD ts fs ps us vs cs s ss.
Proof.
  unfold nstateD, stateD. destruct s; auto.
  destruct ss. destruct SymRegs as [ [ ] ].
  rewrite ExprTac.nexprD_exprD.
  rewrite SEP_TAC.nsexprD_sexprD.
  rewrite ExprTac.nAllProvable_and_AllProvable_and. reflexivity.
Qed.

Local Notation tvWord := (tvType 0).

Definition sym_eval_prop_no_heap (types' : list type) (funcs' : functions (repr bedrock_types_r types'))
  (preds : SEP.predicates (repr bedrock_types_r types'))
  (algos : ILAlgoTypes.AllAlgos (repr bedrock_types_r types'))
  (Regs : state -> regs)
  (interp : codeSpec W (settings * state) ->
            PropX W (settings * state) -> Prop) (emp : hprop)
  (star : hprop -> hprop -> hprop)
  (ex : forall T : Type, (T -> hprop) -> hprop) (inj : Prop -> hprop) (not : Prop -> Prop)
  (sound_or_safe : option state) (cs : codeSpec W (settings * state))
  (meta_env : env (repr bedrock_types_r types')) (stn : settings)
  (path : istream (repr bedrock_types_r (repr bedrock_types_r types')))
  sp rp rv pures :=
  match sym_eval algos (typeof_env meta_env) path QBase {| SymMem := None ; SymRegs := (sp, rp, rv) ; SymPures := pures |} with
    | Safe qs' ss' =>
      quantD nil meta_env qs'
      (fun vars_env meta_env0 : env (repr bedrock_types_r types') =>
        match sound_or_safe with
          | Some st' =>
            nstateD funcs' preds interp emp star ex inj not Regs meta_env0 vars_env cs
            (stn, st') ss'
          | None => False
        end)
    | SafeUntil qs' ss' is' =>
      quantD nil meta_env qs'
      (fun vars_env meta_env0 : env (repr bedrock_types_r types') =>
        exists st' : state,
          nstateD funcs' preds interp emp star ex inj not Regs meta_env0 vars_env cs
          (stn, st') ss' /\
          istreamD (repr (bedrock_funcs_r types') funcs') meta_env0 vars_env
          is' stn st' sound_or_safe)
  end.

Opaque stateD nstateD.

Theorem ApplySymEval_slice_no_heap : forall types (funcs' : functions (repr bedrock_types_r types)) 
  (preds : SEP.predicates (repr bedrock_types_r types))
  (algos : ILAlgoTypes.AllAlgos (repr bedrock_types_r types))
  (algos_correct : @ILAlgoTypes.AllAlgos_correct (repr bedrock_types_r types) (repr (bedrock_funcs_r _) funcs') preds algos)
  stn meta_env sound_or_safe st path,
  istreamD (repr (bedrock_funcs_r _) funcs') meta_env nil path stn st sound_or_safe ->
  forall cs (sp rv rp : Expr.expr (repr bedrock_types_r types)) (pures : list (Expr.expr (repr bedrock_types_r types))),
    exprD (repr (bedrock_funcs_r _) funcs') meta_env nil sp tvWord = Some (Regs st Sp) ->
    exprD (repr (bedrock_funcs_r _) funcs') meta_env nil rv tvWord = Some (Regs st Rv) ->
    exprD (repr (bedrock_funcs_r _) funcs') meta_env nil rp tvWord = Some (Regs st Rp) ->
    Expr.AllProvable (repr (bedrock_funcs_r _) funcs') meta_env nil pures ->
    sym_eval_prop_no_heap (repr (let ts := (@repr type bedrock_types_r types) in
       @Build_Repr (signature ts)
         (@map (signature ts)
            (option (signature ts))
            (@Some (signature ts))
            (Sig ts (tvWord :: tvWord :: @nil tvar) tvWord (@wplus 32)
             :: Sig ts (tvWord :: tvWord :: @nil tvar) tvWord (@wminus 32)
                :: Sig ts (tvWord :: tvWord :: @nil tvar) tvWord (@wmult 32)
                   :: Sig ts (tvType 2 :: tvType 3 :: @nil tvar) tvWord Regs
                      :: Sig ts (tvWord :: tvWord :: @nil tvar) tvProp (@wlt 32)
                         :: Sig ts (tvType 4 :: @nil tvar) tvWord natToW
                            :: @nil (signature ts)))
         (Default_signature ts)) funcs') preds algos Regs (@interp _ _) emp star ex inj not sound_or_safe cs meta_env stn path 
      sp rp rv pures.
Proof.
  Opaque sym_eval Env.repr.
  intros.
  generalize (@stateD_proof_no_heap _ _ preds _ _ _ _ _ H0 H1 H2 _ H3 cs stn).
  clear H0 H1 H2 H3; intro.
  unfold sym_eval_prop_no_heap.
  match goal with
    | |- match ?X with _ => _ end =>
      consider (X) ; intros;
        generalize (@Apply_sym_eval_with_eq _ _ _ _ algos_correct _ _ sound_or_safe _ _ H _ _ _ _ H0 H1); auto
  end.
  { intros. eapply quantD_impl; try eassumption.
    simpl; intros. destruct sound_or_safe; auto. rewrite nstateD_stateD. auto. }
  { intros. eapply quantD_impl; try eassumption.
    simpl; intros. destruct H5. exists x. 
    rewrite nstateD_stateD. auto. }
Qed.

Definition sym_eval_prop_heap (types' : list type) (funcs' : functions (repr bedrock_types_r types'))
  (preds : SEP.predicates (repr bedrock_types_r types'))
  (algos : ILAlgoTypes.AllAlgos (repr bedrock_types_r types'))
  (Regs : state -> regs)
  (interp : codeSpec W (settings * state) ->
            PropX W (settings * state) -> Prop) (emp : hprop)
  (star : hprop -> hprop -> hprop)
  (ex : forall T : Type, (T -> hprop) -> hprop) (inj : Prop -> hprop) (not : Prop -> Prop)
  (sound_or_safe : option state) (cs : codeSpec W (settings * state))
  (meta_env : env (repr bedrock_types_r types')) (stn : settings)
  (path : istream (repr bedrock_types_r (repr bedrock_types_r types')))
  sh sp rp rv pures :=
  let '(vars', hashed) := SH.hash sh in
  match 
    sym_eval algos (typeof_env meta_env) path (QEx (rev vars') QBase) 
       {| SymMem := Some hashed
        ; SymRegs := (sp, rp, rv)
        ; SymPures := pures
       |} 
    with
    | Safe qs' ss' =>
      quantD nil meta_env qs'
      (fun vars_env meta_env0 : env (repr bedrock_types_r types') =>
        match sound_or_safe with
          | Some st' =>
            nstateD funcs' preds interp emp star ex inj not Regs meta_env0 vars_env cs
            (stn, st') ss'
          | None => False
        end)
    | SafeUntil qs' ss' is' =>
      quantD nil meta_env qs'
      (fun vars_env meta_env0 : env (repr bedrock_types_r types') =>
        exists st' : state,
          nstateD funcs' preds interp emp star ex inj not Regs meta_env0 vars_env cs
          (stn, st') ss' /\
          istreamD (repr (bedrock_funcs_r types') funcs') meta_env0 vars_env
          is' stn st' sound_or_safe)
  end.

Theorem ApplySymEval_slice_heap : forall types (funcs' : functions (repr bedrock_types_r types)) 
  (preds : SEP.predicates (repr bedrock_types_r types))
  (algos : ILAlgoTypes.AllAlgos (repr bedrock_types_r types))
  (algos_correct : @ILAlgoTypes.AllAlgos_correct (repr bedrock_types_r types) (repr (bedrock_funcs_r _) funcs') preds algos)
  stn meta_env sound_or_safe st path,
  istreamD (repr (bedrock_funcs_r _) funcs') meta_env nil path stn st sound_or_safe ->
  forall cs (sp rv rp : Expr.expr (repr bedrock_types_r types)) (pures : list (Expr.expr (repr bedrock_types_r types))) sh,
    exprD (repr (bedrock_funcs_r _) funcs') meta_env nil sp tvWord = Some (Regs st Sp) ->
    exprD (repr (bedrock_funcs_r _) funcs') meta_env nil rv tvWord = Some (Regs st Rv) ->
    exprD (repr (bedrock_funcs_r _) funcs') meta_env nil rp tvWord = Some (Regs st Rp) ->
    Expr.AllProvable (repr (bedrock_funcs_r _) funcs') meta_env nil pures ->
    interp cs (![SEP.sexprD (repr (bedrock_funcs_r _) funcs') preds meta_env nil sh] (stn, st)) ->
    (sym_eval_prop_heap (repr (let ts := (@repr type bedrock_types_r types) in
       @Build_Repr (signature ts)
         (@map (signature ts)
            (option (signature ts))
            (@Some (signature ts))
            (Sig ts (tvWord :: tvWord :: @nil tvar) tvWord (@wplus 32)
             :: Sig ts (tvWord :: tvWord :: @nil tvar) tvWord (@wminus 32)
                :: Sig ts (tvWord :: tvWord :: @nil tvar) tvWord (@wmult 32)
                   :: Sig ts (tvType 2 :: tvType 3 :: @nil tvar) tvWord Regs
                      :: Sig ts (tvWord :: tvWord :: @nil tvar) tvProp (@wlt 32)
                         :: Sig ts (tvType 4 :: @nil tvar) tvWord natToW
                            :: @nil (signature ts)))
         (Default_signature ts)) funcs') preds algos Regs (@interp _ _) emp star ex inj not sound_or_safe cs meta_env stn path sh sp rp rv pures).
Proof.
  Opaque sym_eval Env.repr.
  intros.
  unfold sym_eval_prop_heap.
  match goal with
    | [ |- let '(x,y) := ?X in _ ] =>
      consider (X); intros
  end.
  generalize (@stateD_proof _ _ preds _ _ _ _ _ H0 H1 H2 _ H3 sh _ _ H5 cs stn H4).
  clear H0 H1 H2 H3 H4; intro.
  match goal with
    | |- match ?X with _ => _ end =>
      consider (X) ; intros;
        generalize (@Apply_sym_eval_with_eq _ _ _ _ algos_correct _ _ sound_or_safe _ _ H _ _ _ _ H0 H1); auto
  end.
  { intros. eapply quantD_impl; try eassumption.
    simpl; intros. destruct sound_or_safe; auto. rewrite nstateD_stateD. auto. }
  { intros. eapply quantD_impl; try eassumption.
    simpl; intros. destruct H6. exists x. 
    rewrite nstateD_stateD. auto. }
Qed.
  

(*
  Lemma stateD_AllProvable_pures : forall meta_env vars stn_st ss cs,
    stateD funcs preds meta_env vars cs stn_st ss ->
    AllProvable funcs meta_env vars
    match SymMem ss with
      | Some m0 => SH.pures m0 ++ SymPures ss
      | None => SymPures ss
    end.
  Proof.
    Opaque repr.
    clear. unfold stateD. destruct ss; simpl. destruct stn_st. destruct SymRegs. destruct p.
    intuition. destruct SymMem; auto. apply AllProvable_app' in H2; apply AllProvable_app; intuition.
  Qed.

  Theorem Apply_sym_eval_with_eq : forall stn meta_env sound_or_safe st path,   
    istreamD funcs meta_env nil path stn st sound_or_safe ->
    forall cs qs ss res,
      qstateD funcs preds meta_env nil cs (stn,st) qs ss ->
      sym_eval (typeof_env meta_env) path qs ss = res ->
      match res with
        | Safe qs' ss' =>
          quantD nil meta_env qs' (fun vars_env meta_env =>
            match sound_or_safe with
              | None => False
              | Some (st') => stateD funcs preds meta_env vars_env cs (stn, st') ss'
              end)
        | SafeUntil qs' ss' is' =>
          quantD nil meta_env qs' (fun vars_env meta_env =>
            exists st' : state,
              stateD funcs preds meta_env vars_env cs (stn, st') ss' /\
              istreamD funcs meta_env vars_env is' stn st' sound_or_safe)
      end.
  Proof.
    intros. unfold sym_eval in *.
    assert (PC : ProverT_correct
              match ILAlgoTypes.Prover algos with
              | Some p => p
              | None => ReflexivityProver.reflexivityProver
              end (repr (bedrock_funcs_r types') funcs)).
    { generalize (ILAlgoTypes.Acorrect_Prover algos_correct).
      destruct (ILAlgoTypes.Prover algos); intros; auto.
      apply ReflexivityProver.reflexivityProver_correct. }
    generalize dependent (match ILAlgoTypes.Prover algos with
                            | Some p => p
                            | None => ReflexivityProver.reflexivityProver
                          end).
    assert (MC : SymILProofs.MEVAL.MemEvaluator_correct pcT stT
      match ILAlgoTypes.MemEval algos with
      | Some me => me
      | None => MEVAL.Default.MemEvaluator_default (repr BedrockCoreEnv.core TYPES)
      end (repr (bedrock_funcs_r types') funcs) preds tvWord tvWord
      (IL_mem_satisfies (ts:=types')) (IL_ReadWord (ts:=types'))
      (IL_WriteWord (ts:=types')) (IL_ReadByte (ts:=types')) (IL_WriteByte (ts:=types'))).
    { generalize (ILAlgoTypes.Acorrect_MemEval algos_correct).
      destruct (ILAlgoTypes.MemEval algos); auto; intros.
      apply SymIL.MEVAL.Default.MemEvaluator_default_correct. }
    generalize dependent (match ILAlgoTypes.MemEval algos with
                            | Some me => me
                            | None => MEVAL.Default.MemEvaluator_default (repr BedrockCoreEnv.core TYPES)
                          end).
    match goal with
      | [ |- context [ ?X ] ] =>
        match X with 
          | match ILAlgoTypes.Hints _ with _ => _ end =>
            assert (LC : SymILProofs.MEVAL.LearnHook_correct (types_ := TYPES) (tvType 0) (tvType 1) X
              (stateD funcs preds) (repr (bedrock_funcs_r types') funcs) preds); [ | generalize dependent X ]
        end
    end.
    { generalize (ILAlgoTypes.Acorrect_Hints algos_correct).     
      destruct (ILAlgoTypes.Hints algos); auto; intros.
      { apply (@unfolderLearnHook_correct types' h funcs preds H1). } 
      { apply SymIL.MEVAL.LearnHookDefault.LearnHook_default_correct. } }
    intros l LC m MC p ? PC.
    match goal with 
      | [ H : context [ l ?A ?B ?C ?D ?E ?F ] |- _ ] =>
        consider (l A B C D E F); intros
    end.
    unfold qstateD in *. destruct res.
    Opaque stateD.
    { destruct (SymILProofs.SymIL_Correct.sym_evalStream_quant_append _ _ _ _ _ _ _ _ _ H2).
      subst. rewrite <- appendQ_assoc. rewrite quantD_app. eapply quantD_impl; eauto; intros. clear H0.
      simpl in *.
      match goal with 
        | [ H : context [ @Summarize _ ?A ?B ] |- _ ] => 
          assert (AP : AllProvable funcs (meta_env ++ b) a B); [ eauto using stateD_AllProvable_pures |
            assert (VF : Valid PC (meta_env ++ b) a (Summarize A B)); 
              [ clear H; eauto using Summarize_correct | generalize dependent (Summarize A B); generalize dependent B ; intros ] ]
      end.
      eapply (@SymILProofs.MEVAL.hook_sound _ _ _ _ _ _ _ _ LC _ PC (meta_env ++ b) a cs (stn,st)) in H5; eauto.
      2: etransitivity; [ | eapply H1 ]. 2: f_equal; eauto. 2: rewrite typeof_env_app; f_equal; auto.
      rewrite quantD_app. eapply quantD_impl; eauto; intros. simpl in *.

      eapply (@SymILProofs.SymIL_Correct.evalStream_correct_Safe TYPES funcs preds _ PC _ MC _ LC sound_or_safe cs
        stn path f s QBase x s0 ((typeof_env meta_env ++ gatherAll qs) ++ gatherAll q) (gatherEx qs ++ gatherEx q) (appendQ q qs)
        H2).
      { repeat (progress simpl || rewrite typeof_env_app || rewrite app_nil_r); f_equal; auto. f_equal; auto. }
      { repeat (progress simpl || rewrite typeof_env_app || rewrite app_nil_r); f_equal; auto. }
      { apply SymILProofs.SymIL_Correct.istreamD_weaken with (B := b ++ b0) (D := a ++ a0) in H.
        rewrite repr_idempotent. rewrite app_ass. apply H. }
      { simpl. intuition. eapply Valid_weaken. eauto. } }
    { destruct (SymILProofs.SymIL_Correct.sym_evalStream_quant_append _ _ _ _ _ _ _ _ _ H2).
      subst. rewrite <- appendQ_assoc. rewrite quantD_app. eapply quantD_impl; eauto; intros. clear H0.
      simpl in *.
      match goal with 
        | [ H : context [ @Summarize _ ?A ?B ] |- _ ] => 
          assert (AP : AllProvable funcs (meta_env ++ b) a B); [ eauto using stateD_AllProvable_pures |
            assert (VF : Valid PC (meta_env ++ b) a (Summarize A B)); 
              [ clear H; eauto using Summarize_correct | generalize dependent (Summarize A B); generalize dependent B ; intros ] ]
      end.
      eapply (@SymILProofs.MEVAL.hook_sound _ _ _ _ _ _ _ _ LC _ PC (meta_env ++ b) a cs (stn,st)) in H5; eauto.
      2: etransitivity; [ | eapply H1 ]. 2: f_equal; eauto. 2: rewrite typeof_env_app; f_equal; auto.
      rewrite quantD_app. eapply quantD_impl; eauto; intros. simpl in *.

      eapply (@SymILProofs.SymIL_Correct.evalStream_correct_SafeUntil TYPES funcs preds _ PC _ MC _ LC sound_or_safe cs
        stn path f s QBase x s0); eauto.  (*((typeof_env meta_env ++ gatherAll qs) ++ gatherAll q) (gatherEx qs ++ gatherEx q) (appendQ q qs)
        H2). *)
      { repeat (progress simpl || rewrite typeof_env_app || rewrite app_nil_r); f_equal; auto. f_equal; auto. }
      { repeat (progress simpl || rewrite typeof_env_app || rewrite app_nil_r); f_equal; auto. }
      { apply SymILProofs.SymIL_Correct.istreamD_weaken with (B := b ++ b0) (D := a ++ a0) in H.
        rewrite repr_idempotent. rewrite app_ass. apply H. }
      { simpl. intuition. eapply Valid_weaken. eauto. } }
  Qed.

  Theorem Apply_sym_eval : forall stn meta_env sound_or_safe st path,
    istreamD funcs meta_env nil path stn st sound_or_safe ->
    forall cs qs ss,
      qstateD funcs preds meta_env nil cs (stn,st) qs ss ->
      match sym_eval (typeof_env meta_env) path qs ss with
        | Safe qs' ss' =>
          quantD nil meta_env qs' (fun vars_env meta_env =>
            match sound_or_safe with
              | None => False
              | Some (st') => stateD funcs preds meta_env vars_env cs (stn, st') ss'
              end)
        | SafeUntil qs' ss' is' =>
          quantD nil meta_env qs' (fun vars_env meta_env =>
            exists st' : state,
              stateD funcs preds meta_env vars_env cs (stn, st') ss' /\
              istreamD funcs meta_env vars_env is' stn st' sound_or_safe)
      end.
  Proof. intros. eapply Apply_sym_eval_with_eq; eauto. Qed.

End apply_stream_correctness.
*)
