Require Import List Word Memory.
Require Import PropX.
Require Import Env.

Require Import MirrorShard.Expr.
Require Import MirrorShard.SepTheory.
Require Import MirrorShard.SepHeap.
Require Import MirrorShard.Quantifier.
Require Import MirrorShard.Prover.

Set Implicit Arguments.
Set Strict Implicit.

Module SymbolicEvaluator (ST : SepTheory) (SEP : SepExpr.SepExpr ST) (SH : SepHeap ST SEP).

  (** Learn hook
   ** - This is the bit of code that gets run when new pure facts are
   **   learned during symbolic evaluation
   **)
  Section LearnHook.
    Variable types_ : list type.
    Variable SymState : Type.

    Definition LearnHook : Type := 
      forall P : ProverT, variables -> variables -> SymState -> Facts P -> list expr -> SymState * Quant.

    Variables pcT stT : tvar.

    Record LearnHook_correct (L : LearnHook) 
      (stateD : env types_ -> env types_ -> 
        codeSpec (tvarD types_ pcT) (tvarD types_ stT) -> tvarD types_ stT -> SymState -> Prop)
      (funcs : functions types_) 
      (preds : SEP.predicates types_) : Prop :=
    { hook_sound : forall P (PC : ProverT_correct P funcs),
      forall uvars vars cs stn_st ss ss' pp new_facts quant,
        stateD uvars vars cs stn_st ss ->
        Valid PC uvars vars pp ->
        AllProvable funcs uvars vars new_facts ->
        L P (typeof_env uvars) (typeof_env vars) ss pp new_facts = (ss', quant) ->
        quantD vars uvars quant (fun vars uvars => stateD uvars vars cs stn_st ss')
    }.
  End LearnHook.

  Module LearnHookDefault.
    Definition LearnHook_default (State : Type) : 
      LearnHook State :=
      fun _ _ _ x _ _ => (x, QBase).
    
    Definition LearnHook_default_correct types pcT stT State stateD funcs preds :
      @LearnHook_correct types pcT stT State (@LearnHook_default _) stateD funcs preds.
    Proof.
      unfold LearnHook_default; econstructor; intros; subst; auto.
      inversion H2. subst; simpl. auto.
    Qed.
  End LearnHookDefault.

  (** Memory Evaluator
   ** - This is the bit of code that gets run when we try to read
   **   or write to memory.
   **)
  Section MemEvaluator.
    Variable types : list type.
    Variables pcT stT : tvar. (** TODO: maybe we can get rid of this? **)

    Record MemEvaluator : Type :=
    { sread_word : forall (P : ProverT), Facts P -> 
      expr -> SH.SHeap -> option expr
    ; swrite_word : forall (P : ProverT), Facts P ->
      expr -> expr -> SH.SHeap -> option SH.SHeap

    ; sread_byte : forall (P : ProverT), Facts P -> 
      expr -> SH.SHeap -> option expr
    ; swrite_byte : forall (P : ProverT), Facts P ->
      expr -> expr -> SH.SHeap -> option SH.SHeap
    }.

    Variable eval : MemEvaluator.

    Variable funcs : functions types.
    Variable preds : SEP.predicates types.

    Variable stn_st : Type.
    
    Variables ptrT valT : tvar.

    Hypothesis mem_satisfies : PropX.codeSpec (tvarD types pcT) (tvarD types stT) -> ST.hprop -> stn_st -> Prop.
    Hypothesis ReadWord : stn_st -> tvarD types ptrT -> option (tvarD types valT).
    Hypothesis WriteWord : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.
    Hypothesis ReadByte : stn_st -> tvarD types ptrT -> option (tvarD types valT).
    Hypothesis WriteByte : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.

    Record MemEvaluator_correct : Type :=
    { ReadCorrect :
      forall (P : ProverT) (PE : ProverT_correct P funcs),
        forall facts pe ve SH,
          sread_word eval P facts pe SH = Some ve ->
          forall uvars vars cs p stn_m,
            Valid PE uvars vars facts ->
            exprD funcs uvars vars pe ptrT = Some p ->
            mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH)) stn_m ->
            match exprD funcs uvars vars ve valT with
              | Some v =>
                ReadWord stn_m p = Some v
              | _ => False
            end
    ; WriteCorrect :
      forall (P : ProverT) (PE : ProverT_correct P funcs),
        forall uvars vars cs facts pe ve SH SH',
          swrite_word eval P facts pe ve SH = Some SH' ->
          Valid PE uvars vars facts ->
          forall p v,
            exprD funcs uvars vars pe ptrT = Some p ->
            exprD funcs uvars vars ve valT = Some v ->
            forall stn_m,
            mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH)) stn_m ->
            match WriteWord stn_m p v with
              | None => False
              | Some stn_m' =>
                mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH')) stn_m'
            end

    ; ReadByteCorrect :
      forall (P : ProverT) (PE : ProverT_correct P funcs),
        forall facts pe ve SH,
          sread_byte eval P facts pe SH = Some ve ->
          forall uvars vars cs p stn_m,
            Valid PE uvars vars facts ->
            exprD funcs uvars vars pe ptrT = Some p ->
            mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH)) stn_m ->
            match exprD funcs uvars vars ve valT with
              | Some v =>
                ReadByte stn_m p = Some v
              | _ => False
            end
    ; WriteByteCorrect :
      forall (P : ProverT) (PE : ProverT_correct P funcs),
        forall uvars vars cs facts pe ve SH SH',
          swrite_byte eval P facts pe ve SH = Some SH' ->
          Valid PE uvars vars facts ->
          forall p v,
            exprD funcs uvars vars pe ptrT = Some p ->
            exprD funcs uvars vars ve valT = Some v ->
            forall stn_m,
            mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH)) stn_m ->
            match WriteByte stn_m p v with
              | None => False
              | Some stn_m' =>
                mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH')) stn_m'
            end
    }.
  End MemEvaluator.

  Record MemEvaluatorPackage (tr : Repr type) (pc st ptr val : tvar) 
    (sat : forall ts, codeSpec (tvarD (repr tr ts) pc) (tvarD (repr tr ts) st) -> 
      ST.hprop -> tvarD (repr tr ts) st -> Prop) 
    (read  : forall ts, tvarD (repr tr ts) st -> tvarD (repr tr ts) ptr -> option (tvarD (repr tr ts) val))
    (write : forall ts, tvarD (repr tr ts) st -> tvarD (repr tr ts) ptr -> tvarD (repr tr ts) val -> option (tvarD (repr tr ts) st))
    (readByte  : forall ts, tvarD (repr tr ts) st -> tvarD (repr tr ts) ptr -> option (tvarD (repr tr ts) val))
    (writeByte : forall ts, tvarD (repr tr ts) st -> tvarD (repr tr ts) ptr -> tvarD (repr tr ts) val -> option (tvarD (repr tr ts) st))
    : Type :=
  { MemEvalTypes : Repr type
  ; MemEvalFuncs : forall ts, Repr (signature (repr tr (repr MemEvalTypes ts)))
  ; MemEvalPreds : forall ts, Repr (SEP.predicate (repr tr (repr MemEvalTypes ts)))
  ; MemEval : MemEvaluator
  ; MemEval_correct : forall ts fs ps, 
    @MemEvaluator_correct (repr tr (repr MemEvalTypes ts)) pc st MemEval
      (repr (MemEvalFuncs ts) fs) (repr (MemEvalPreds ts) ps)
      (tvarD (repr tr (repr MemEvalTypes ts)) st) ptr val
      (sat (repr MemEvalTypes ts)) (read (repr MemEvalTypes ts)) (write (repr MemEvalTypes ts))
      (readByte (repr MemEvalTypes ts)) (writeByte (repr MemEvalTypes ts))
  }.

  Module Default.
    Section with_prover.
      Variable types : list type.
      Variables pcT stT : tvar.
      Variable prover : ProverT.
      
      Definition smemeval_read_word_default (_ : Facts prover) (_ : expr)
        (_ : SH.SHeap) : option expr :=
        None.

      Definition smemeval_write_word_default (_ : Facts prover)
        (_ : expr) (_ : expr) (_ : SH.SHeap)
        : option SH.SHeap :=
        None.
    End with_prover.

    Definition MemEvaluator_default : MemEvaluator.
      constructor.
      apply smemeval_read_word_default.
      apply smemeval_write_word_default.
      apply smemeval_read_word_default.
      apply smemeval_write_word_default.
    Defined.

    Theorem MemEvaluator_default_correct types' (pcT stT : tvar) funcs preds X Y Z A B C D E :
      @MemEvaluator_correct types' pcT stT MemEvaluator_default funcs preds X Y Z A B C D E.
      econstructor.
      simpl; unfold smemeval_read_word_default, smemeval_write_word_default; simpl; intros; exfalso; inversion H.
      simpl; unfold smemeval_read_word_default, smemeval_write_word_default; simpl; intros; exfalso; inversion H.
      simpl; unfold smemeval_read_word_default, smemeval_write_word_default; simpl; intros; exfalso; inversion H.
      simpl; unfold smemeval_read_word_default, smemeval_write_word_default; simpl; intros; exfalso; inversion H.
    Qed.

    Ltac unfolder H :=
      cbv delta 
        [ smemeval_read_word_default
          smemeval_write_word_default
          MemEvaluator_default
        ] in H.

    Definition package tr pcT stT ptr val X Y Z A B : @MemEvaluatorPackage tr pcT stT ptr val X Y Z A B :=
      {| MemEvalTypes := nil_Repr EmptySet_type
       ; MemEvalFuncs := fun ts => nil_Repr (Default_signature _)
       ; MemEvalPreds := fun ts => nil_Repr (SEP.Default_predicate _)
       ; MemEval := MemEvaluator_default
       ; MemEval_correct := fun ts fs ps => MemEvaluator_default_correct _ _ _ _ _ _ _ _ _ _ _
       |}.

  End Default.

  (** Evaluators for single predicates
   ** - this abstracts the common case when we are considering
   **   a single predicate in isolation
   ** - TODO: I do not know how to make symbolic memory work with 
   **   this definition. I want to use the predicates in SepTheoryX
   **   but there is no generic reading function & I can't specialize
   **   until I know what [valT] refers to.
   **)
  Module PredEval.
    Module SF := SepExpr.SepExprFacts ST SEP.

    Section typed.
      Variable types : list type.

      Record MemEvalPred : Type :=
      { pred_read_word  : 
        forall (P : ProverT) (facts : Facts P) (args : exprs) (p : expr),
          option expr
      ; pred_write_word : 
        forall (P : ProverT) (facts : Facts P) (args : exprs) (p v : expr),
          option (exprs)

      ; pred_read_byte  : 
        forall (P : ProverT) (facts : Facts P) (args : exprs) (p : expr),
          option expr
      ; pred_write_byte : 
        forall (P : ProverT) (facts : Facts P) (args : exprs) (p v : expr),
          option (exprs)
      }.

      Variables pcT stT : tvar.

      Variable stn_st : Type.
      Variables ptrT valT : tvar.

      Hypothesis mem_satisfies : PropX.codeSpec (tvarD types pcT) (tvarD types stT) -> ST.hprop -> stn_st -> Prop.
      Hypothesis ReadWord : stn_st -> tvarD types ptrT -> option (tvarD types valT).
      Hypothesis WriteWord : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.
      Hypothesis ReadByte : stn_st -> tvarD types ptrT -> option (tvarD types valT).
      Hypothesis WriteByte : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.

      Variable me : MemEvalPred.

      Record MemEvalPred_correct (Predicate : SEP.predicate types)
        (funcs : functions types) : Prop :=
      { sym_read_word_correct : forall P (PE : ProverT_correct P funcs),
        forall args uvars vars cs facts pe p ve stn_st Q,
          pred_read_word me P facts args pe = Some ve ->
          Valid PE uvars vars facts ->
          exprD funcs uvars vars pe ptrT = Some p ->
          match 
            applyD types (exprD funcs uvars vars) (SEP.SDomain Predicate) args _ (SEP.SDenotation Predicate)
            with
            | None => False
            | Some p => mem_satisfies cs (ST.star p Q) stn_st
          end ->
          match exprD funcs uvars vars ve valT with
            | Some v =>
              ReadWord stn_st p = Some v
            | _ => False
          end
       ; sym_write_word_correct : forall P (PE : ProverT_correct P funcs),
         forall args uvars vars cs facts pe p ve v stn_st args' Q,
           pred_write_word me P facts args pe ve = Some args' ->
           Valid PE uvars vars facts ->
           exprD funcs uvars vars pe ptrT = Some p ->
           exprD funcs uvars vars ve valT = Some v ->
           match
             applyD types (@exprD _ funcs uvars vars) (SEP.SDomain Predicate) args _ (SEP.SDenotation Predicate)
             with
             | None => False
             | Some p => mem_satisfies cs (ST.star p Q) stn_st
           end ->
           match 
             applyD types (@exprD _ funcs uvars vars) (SEP.SDomain Predicate) args' _ (SEP.SDenotation Predicate)
             with
             | None => False
             | Some pr => 
               match WriteWord stn_st p v with
                 | None => False
                 | Some sm' => mem_satisfies cs (ST.star pr Q) sm'
               end
           end

       ; sym_read_byte_correct : forall P (PE : ProverT_correct P funcs),
        forall args uvars vars cs facts pe p ve stn_st Q,
          pred_read_byte me P facts args pe = Some ve ->
          Valid PE uvars vars facts ->
          exprD funcs uvars vars pe ptrT = Some p ->
          match 
            applyD types (exprD funcs uvars vars) (SEP.SDomain Predicate) args _ (SEP.SDenotation Predicate)
            with
            | None => False
            | Some p => mem_satisfies cs (ST.star p Q) stn_st
          end ->
          match exprD funcs uvars vars ve valT with
            | Some v =>
              ReadByte stn_st p = Some v
            | _ => False
          end
       ; sym_write_byte_correct : forall P (PE : ProverT_correct P funcs),
         forall args uvars vars cs facts pe p ve v stn_st args' Q,
           pred_write_byte me P facts args pe ve = Some args' ->
           Valid PE uvars vars facts ->
           exprD funcs uvars vars pe ptrT = Some p ->
           exprD funcs uvars vars ve valT = Some v ->
           match
             applyD types (@exprD _ funcs uvars vars) (SEP.SDomain Predicate) args _ (SEP.SDenotation Predicate)
             with
             | None => False
             | Some p => mem_satisfies cs (ST.star p Q) stn_st
           end ->
           match 
             applyD types (@exprD _ funcs uvars vars) (SEP.SDomain Predicate) args' _ (SEP.SDenotation Predicate)
             with
             | None => False
             | Some pr => 
               match WriteByte stn_st p v with
                 | None => False
                 | Some sm' => mem_satisfies cs (ST.star pr Q) sm'
               end
           end
      }.
    End typed.

    Section search_read_write.
      Variable types : list type.
      Variable T : Type.
      Variable F : exprs -> option T.
      Variable F_upd : exprs -> option (exprs).

      Fixpoint fold_args (es : list (exprs)) : option T :=
        match es with 
          | nil => None
          | a :: b => 
            match F a with
              | None => fold_args b
              | Some r => Some r
            end
        end.
      
      Theorem fold_args_correct : forall es v,
        fold_args es = Some v ->
        exists k, In k es /\ F k = Some v.
      Proof.
        clear. induction es.
        simpl; congruence.
        simpl. case_eq (F a); intros.
        inversion H0. subst. eauto.
        eapply IHes in H0. destruct H0.
        exists x. tauto.
      Qed.


      Fixpoint fold_args_update (es : list (exprs)) : option (list (exprs)) :=
        match es with 
          | nil => None
          | a :: b => 
            match F_upd a with
              | None => match fold_args_update b with
                          | None => None
                          | Some b => Some (a :: b)
                        end
              | Some r => Some (r :: b)
            end
        end.
      
      Theorem fold_args_update_correct : forall es es',
        fold_args_update es = Some es' ->
        exists pre, exists post, exists k, exists k',
          es = pre ++ k :: post /\
          F_upd k = Some k' /\
          es' = pre ++ k' :: post.
      Proof.
        clear. induction es.
        simpl; congruence.
        simpl. case_eq (F_upd a); intros.
        inversion H0. subst. do 4 eexists; intuition eauto.
        instantiate (2 := nil). reflexivity. reflexivity.

        generalize dependent H0.
        case_eq (fold_args_update es); intros.
        inversion H1; subst. eapply IHes in H0.
        do 4 destruct H0. exists (a :: x). exists x0.
        eexists; eexists; intuition; subst; eauto. reflexivity.

        congruence.
      Qed.

    End search_read_write.

    Section To_MemEvaluator.
      Variable types : list type.
      Variables pcT stT : tvar.
      
      Variable mep : MemEvalPred.
      Variable predIndex : nat.

      Definition MemEvalPred_to_MemEvaluator : MemEvaluator :=
        {| sread_word := fun (P : ProverT) (F : Facts P) (p : expr) (h : SH.SHeap) =>
           let impures := SH.impures h in
           let argss := FM.find predIndex impures in
           match argss with
             | None => None
             | Some argss => fold_args (fun args => @pred_read_word mep P F args p) argss
           end
         ; swrite_word := fun (P : ProverT) (F : Facts P) (p v : expr) (h : SH.SHeap) =>
           let impures := SH.impures h in
           let argss := FM.find predIndex impures in
           match argss with
             | None => None
             | Some argss =>
               match fold_args_update (fun args => @pred_write_word mep P F args p v) argss with
                 | None => None
                 | Some argss =>
                   Some {| SH.impures := FM.add predIndex argss impures
                         ; SH.pures   := SH.pures h
                         ; SH.other   := SH.other h
                         |}
               end
           end

         ; sread_byte := fun (P : ProverT) (F : Facts P) (p : expr) (h : SH.SHeap) =>
           let impures := SH.impures h in
           let argss := FM.find predIndex impures in
           match argss with
             | None => None
             | Some argss => fold_args (fun args => @pred_read_byte mep P F args p) argss
           end
         ; swrite_byte := fun (P : ProverT) (F : Facts P) (p v : expr) (h : SH.SHeap) =>
           let impures := SH.impures h in
           let argss := FM.find predIndex impures in
           match argss with
             | None => None
             | Some argss =>
               match fold_args_update (fun args => @pred_write_byte mep P F args p v) argss with
                 | None => None
                 | Some argss =>
                   Some {| SH.impures := FM.add predIndex argss impures
                         ; SH.pures   := SH.pures h
                         ; SH.other   := SH.other h
                         |}
               end
           end
         |}.
    
      (** Correctness **)
      Variable funcs : functions types.
      Variable preds : SEP.predicates types.

      Variable stn_st : Type.
    
      Variables ptrT valT : tvar.

      Hypothesis mem_satisfies : PropX.codeSpec (tvarD types pcT) (tvarD types stT) -> ST.hprop -> stn_st -> Prop.
      Hypothesis ReadWord : stn_st -> tvarD types ptrT -> option (tvarD types valT).
      Hypothesis WriteWord : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.
      Hypothesis ReadByte : stn_st -> tvarD types ptrT -> option (tvarD types valT).
      Hypothesis WriteByte : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.

      Variable pred : SEP.predicate types.
      Hypothesis predAt : nth_error preds predIndex = Some pred.
      Hypothesis pred_correct :
        @MemEvalPred_correct types pcT stT stn_st ptrT valT mem_satisfies
        ReadWord WriteWord ReadByte WriteByte mep pred funcs.

      Lemma in_split : forall T (x : T) ls,
        In x ls -> exists a b, ls = a ++ x :: b.
      Proof.
        clear. induction ls. destruct 1.
        intros. destruct H. subst. exists nil. simpl; eauto.
        apply IHls in H. do 2 destruct H. subst; eauto. exists (a :: x0). simpl; eauto.
      Qed.

      (** This is all going to get put in a record **)
      Hypothesis mem_satisfies_himp : forall cs P Q stn_st,
        mem_satisfies cs P stn_st ->
        ST.himp P Q ->
        mem_satisfies cs Q stn_st.
      Hypothesis mem_satisfies_pure : forall cs p P stn_st,
        mem_satisfies cs (ST.star (ST.inj p) P) stn_st ->
        p.

      Lemma pull_single : forall cs uvars vars SH x x1 x0 stn_st,
        FM.find predIndex (SH.impures SH) = Some (x0 ++ x :: x1) ->
        mem_satisfies cs (SEP.sexprD funcs preds uvars vars (SH.sheapD SH)) stn_st ->
        mem_satisfies cs (SEP.sexprD funcs preds uvars vars
          (SEP.Star (SEP.Func predIndex x) 
            (SH.starred (SEP.Func predIndex) x0 (SH.starred (SEP.Func predIndex) x1
              (SH.sheapD {| SH.impures := FM.remove predIndex (SH.impures SH)
                ; SH.pures := SH.pures SH
                ; SH.other := SH.other SH
              |}))))) stn_st.
      Proof.
        intros. 
        assert (SEP.heq funcs preds uvars vars
          (SH.sheapD SH) 
          (SEP.Star (SEP.Func predIndex x) 
            (SH.starred (SEP.Func predIndex) x0 (SH.starred (SEP.Func predIndex) x1
              (SH.sheapD {| SH.impures := FM.remove predIndex (SH.impures SH)
                ; SH.pures := SH.pures SH
                ; SH.other := SH.other SH
              |}))))).
        { rewrite SH.starred_base. rewrite SH.starred_base.
          repeat rewrite SH.sheapD_def. simpl. SF.heq_canceler.
          rewrite SH.impuresD_Add with (f := predIndex) (argss := x0 ++ x :: x1).
          rewrite SH.starred_def. rewrite fold_right_app. simpl.
          rewrite <- SH.starred_def. rewrite SH.starred_base. rewrite <- SH.starred_def.
          SF.heq_canceler. 
          { unfold MM.PROPS.Add. intros. repeat (rewrite MM.FACTS.add_o || rewrite MM.FACTS.remove_o).
            destruct (MF.FACTS.eq_dec predIndex y); subst; auto. }
          { intro. apply MM.FACTS.remove_in_iff in H1. intuition; congruence. } }
        eapply mem_satisfies_himp; eauto. apply SF.heq_himp; auto.
      Qed.

      Theorem MemEvaluator_MemEvalPred_correct : @MemEvaluator_correct types pcT stT MemEvalPred_to_MemEvaluator
        funcs preds stn_st ptrT valT mem_satisfies ReadWord WriteWord ReadByte WriteByte.
      Proof.
        constructor; simpl.

        { intros. revert H. case_eq (FM.find predIndex (SH.impures SH)); try congruence; intros.
          eapply fold_args_correct in H3. destruct H3. intuition.
          apply in_split in H4. destruct H4. destruct H3. subst.
          eapply pull_single in H; eauto.
          simpl in *. rewrite predAt in H.
          eapply sym_read_word_correct with (cs := cs) (Q := SEP.sexprD funcs preds uvars vars
               (SH.starred (SEP.Func predIndex) x0
                  (SH.starred (SEP.Func predIndex) x1
                     (SH.sheapD
                        {|
                        SH.impures := FM.remove (elt:=
                                        list (exprs)) predIndex
                                        (SH.impures SH);
                        SH.pures := SH.pures SH;
                        SH.other := SH.other SH |})))) in H5; eauto.
          revert H. match goal with 
                       | [ |- context [ match ?X with | _ => _ end ] ] => case_eq X
                     end; intros; auto.
          apply mem_satisfies_pure in H3. red in H3. auto. }

        { intros. revert H.
          case_eq (FM.find predIndex (SH.impures SH)); try congruence.
          do 2 intro.
          case_eq (fold_args_update (fun args => pred_write_word mep P facts args pe ve) l); try congruence; intros.
          inversion H5; clear H5; subst.
          apply fold_args_update_correct in H4. do 4 destruct H4; intuition; subst.
          eapply pull_single in H; eauto. simpl in H.
          rewrite predAt in H.
          eapply sym_write_word_correct with (cs := cs) 
            (Q := (SEP.sexprD funcs preds uvars vars
              (SH.starred (SEP.Func predIndex) x
                 (SH.starred (SEP.Func predIndex) x0
                    (SH.sheapD
                       {|
                       SH.impures := FM.remove (elt:=
                                       list (exprs)) predIndex
                                       (SH.impures SH);
                       SH.pures := SH.pures SH;
                       SH.other := SH.other SH |}))))) 
            in H4; eauto.
          2: instantiate (1 := stn_m).
          revert H4.
          match goal with 
            | [ |- match ?X with _ => _ end -> _ ] => 
              case_eq X; try contradiction
          end; intros.
          revert H5. case_eq (WriteWord stn_m p v); try contradiction; intros.
          eapply mem_satisfies_himp with (P := 
            (SEP.sexprD funcs preds uvars vars
              (SEP.Star (SEP.Func predIndex x2)
            (SH.starred (SEP.Func predIndex) x
               (SH.starred (SEP.Func predIndex) x0
                  (SH.sheapD
                     {|
                     SH.impures := FM.remove (elt:=
                                     list (exprs)) predIndex
                                     (SH.impures SH);
                     SH.pures := SH.pures SH;
                     SH.other := SH.other SH |})))))).
          simpl. rewrite predAt. rewrite H4. eauto.
          match goal with
            | [ |- ST.himp (SEP.sexprD ?F ?P ?U ?G ?L) (SEP.sexprD _ _ _ _ ?R) ] =>
              change (SEP.himp F P U G L R)
          end.
          apply SF.heq_himp. do 2 rewrite SH.starred_base.
          repeat rewrite SH.sheapD_def; simpl. symmetry.
          rewrite SH.impuresD_Add with (f := predIndex) (argss := x ++ x2 :: x0) (i := FM.remove predIndex (SH.impures SH)).
          rewrite SH.starred_def. rewrite fold_right_app. simpl. rewrite <- SH.starred_def. rewrite SH.starred_base.
          rewrite <- SH.starred_def. SF.heq_canceler.
          { unfold MM.PROPS.Add. intros; repeat (rewrite MM.FACTS.add_o || rewrite MM.FACTS.remove_o).
            destruct (MF.FACTS.eq_dec predIndex y); auto. }
          { intro. apply MM.FACTS.remove_in_iff in H7; intuition congruence. }
          revert H.
          match goal with
            | [ |- context [ match ?X with _ => _ end ] ] => 
              case_eq X
          end; intros; eauto.
          apply mem_satisfies_pure in H5. eapply H5. }

        { intros. revert H. case_eq (FM.find predIndex (SH.impures SH)); try congruence; intros.
          eapply fold_args_correct in H3. destruct H3. intuition.
          apply in_split in H4. destruct H4. destruct H3. subst.
          eapply pull_single in H; eauto.
          simpl in *. rewrite predAt in H.
          eapply sym_read_byte_correct with (cs := cs) (Q := SEP.sexprD funcs preds uvars vars
               (SH.starred (SEP.Func predIndex) x0
                  (SH.starred (SEP.Func predIndex) x1
                     (SH.sheapD
                        {|
                        SH.impures := FM.remove (elt:=
                                        list (exprs)) predIndex
                                        (SH.impures SH);
                        SH.pures := SH.pures SH;
                        SH.other := SH.other SH |})))) in H5; eauto.
          revert H. match goal with 
                       | [ |- context [ match ?X with | _ => _ end ] ] => case_eq X
                     end; intros; auto.
          apply mem_satisfies_pure in H3. eapply H3. }

        { intros. revert H.
          case_eq (FM.find predIndex (SH.impures SH)); try congruence.
          do 2 intro.
          case_eq (fold_args_update (fun args => pred_write_byte mep P facts args pe ve) l); try congruence; intros.
          inversion H5; clear H5; subst.
          apply fold_args_update_correct in H4. do 4 destruct H4; intuition; subst.
          eapply pull_single in H; eauto. simpl in H.
          rewrite predAt in H.
          eapply sym_write_byte_correct with (cs := cs) 
            (Q := (SEP.sexprD funcs preds uvars vars
              (SH.starred (SEP.Func predIndex) x
                 (SH.starred (SEP.Func predIndex) x0
                    (SH.sheapD
                       {|
                       SH.impures := FM.remove (elt:=
                                       list (exprs)) predIndex
                                       (SH.impures SH);
                       SH.pures := SH.pures SH;
                       SH.other := SH.other SH |}))))) 
            in H4; eauto.
          2: instantiate (1 := stn_m).
          revert H4.
          match goal with 
            | [ |- match ?X with _ => _ end -> _ ] => 
              case_eq X; try contradiction
          end; intros.
          revert H5. case_eq (WriteByte stn_m p v); try contradiction; intros.
          eapply mem_satisfies_himp with (P := 
            (SEP.sexprD funcs preds uvars vars
              (SEP.Star (SEP.Func predIndex x2)
            (SH.starred (SEP.Func predIndex) x
               (SH.starred (SEP.Func predIndex) x0
                  (SH.sheapD
                     {|
                     SH.impures := FM.remove (elt:=
                                     list (exprs)) predIndex
                                     (SH.impures SH);
                     SH.pures := SH.pures SH;
                     SH.other := SH.other SH |})))))).
          simpl. rewrite predAt. rewrite H4. eauto.
          match goal with
            | [ |- ST.himp (SEP.sexprD ?F ?P ?U ?G ?L) (SEP.sexprD _ _ _ _ ?R) ] =>
              change (SEP.himp F P U G L R)
          end.
          apply SF.heq_himp. do 2 rewrite SH.starred_base.
          repeat rewrite SH.sheapD_def; simpl. symmetry.
          rewrite SH.impuresD_Add with (f := predIndex) (argss := x ++ x2 :: x0) (i := FM.remove predIndex (SH.impures SH)).
          rewrite SH.starred_def. rewrite fold_right_app. simpl. rewrite <- SH.starred_def. rewrite SH.starred_base.
          rewrite <- SH.starred_def. SF.heq_canceler.
          { unfold MM.PROPS.Add. intros; repeat (rewrite MM.FACTS.add_o || rewrite MM.FACTS.remove_o).
            destruct (MF.FACTS.eq_dec predIndex y); auto. }
          { intro. apply MM.FACTS.remove_in_iff in H7; intuition congruence. }
          revert H.
          match goal with
            | [ |- context [ match ?X with _ => _ end ] ] => 
              case_eq X
          end; intros; eauto.
          apply mem_satisfies_pure in H5. eapply H5. }
      Qed.
          
    End To_MemEvaluator.

  End PredEval.

  Module Composite.
    Section typed.
      Variable types : list type.
      Variable pcT stT : tvar.

      Definition MemEvaluator_composite (l r : MemEvaluator) : MemEvaluator :=
        {| sread_word := fun P f e h => 
           match sread_word l P f e h with
             | None => sread_word r P f e h
             | Some v => Some v
           end
         ; swrite_word := fun P f p v h => 
           match swrite_word l P f p v h with
             | None => swrite_word r P f p v h
             | Some v => Some v
           end

         ; sread_byte := fun P f e h => 
           match sread_byte l P f e h with
             | None => sread_byte r P f e h
             | Some v => Some v
           end
         ; swrite_byte := fun P f p v h => 
           match swrite_byte l P f p v h with
             | None => swrite_byte r P f p v h
             | Some v => Some v
           end
         |}.

      Variables evalL evalR : MemEvaluator.

      Variable funcs : functions types.
      Variable preds : SEP.predicates types.

      Variable stn_st : Type.
    
      Variables ptrT valT : tvar.

      Hypothesis mem_satisfies : PropX.codeSpec (tvarD types pcT) (tvarD types stT) -> ST.hprop -> stn_st -> Prop.
      Hypothesis ReadWord : stn_st -> tvarD types ptrT -> option (tvarD types valT).
      Hypothesis WriteWord : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.
      Hypothesis ReadByte : stn_st -> tvarD types ptrT -> option (tvarD types valT).
      Hypothesis WriteByte : stn_st -> tvarD types ptrT -> tvarD types valT -> option stn_st.

      Hypothesis Lcorr : MemEvaluator_correct _ _ evalL funcs preds ptrT valT
        mem_satisfies ReadWord WriteWord ReadByte WriteByte.
      Hypothesis Rcorr : MemEvaluator_correct _ _ evalR funcs preds ptrT valT
        mem_satisfies ReadWord WriteWord ReadByte WriteByte.

      Theorem MemEvaluator_correct_composite : @MemEvaluator_correct types pcT stT (MemEvaluator_composite evalL evalR)
        funcs preds stn_st ptrT valT mem_satisfies ReadWord WriteWord ReadByte WriteByte.
      Proof.
        unfold MemEvaluator_composite. econstructor; intros; simpl in *;
        repeat match goal with 
                 | [ H : match ?X with None => _ | Some _ => _ end = Some _ |- _ ] => revert H; case_eq X; intros
                 | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
                 | [ |- _ ] => 
                   eapply ReadCorrect; [ | eassumption | | | ]; eauto
                 | [ |- _ ] => 
                   eapply WriteCorrect; [ | eassumption | | | | ]; eauto
                 | [ |- _ ] => 
                   eapply ReadByteCorrect; [ | eassumption | | | ]; eauto
                 | [ |- _ ] => 
                   eapply WriteByteCorrect; [ | eassumption | | | | ]; eauto
               end.
      Qed.
    End typed.
  End Composite.

End SymbolicEvaluator.
