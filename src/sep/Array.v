Require Import Bool List.
Require Import ExtLib.Tactics.Consider.
Require Import MirrorShard.Expr.
Require Import MirrorShard.SepExpr.
Require Import MirrorShard.Env MirrorShard.Prover.
Require Import SymEval.
Require Import Word Memory IL SepIL SymIL ILEnv.
Require Import PropX PropXTac Nomega NArith.

Set Implicit Arguments.

Definition array (ws : list W) (p : W) : HProp := ptsto32m _ p O ws.

Fixpoint div4 (n : nat) : option nat :=
  match n with
    | O => Some O
    | S (S (S (S n'))) => match div4 n' with
                            | None => None
                            | Some n'' => Some (S n'')
                          end
    | _ => None
  end.

Fixpoint selN (ws : list W) (n : nat) : W :=
  match ws with
    | nil => wzero _
    | w :: ws' => match n with
                    | O => w
                    | S n' => selN ws' n'
                  end
  end.

Definition sel (ws : list W) (a : W) : W :=
  selN ws (wordToNat a).

Fixpoint updN (ws : list W) (n : nat) (v : W) : list W :=
  match ws with
    | nil => nil
    | w :: ws' => match n with
                    | O => v :: ws'
                    | S n' => w :: updN ws' n' v
                  end
  end.

Definition upd (ws : list W) (a v : W) : list W :=
  updN ws (wordToNat a) v.

Definition bedrock_type_listW : type :=
  {| Expr.Impl := list W
   ; Expr.Eqb := (fun _ _ => false)
   ; Expr.Eqb_correct := @ILEnv.all_false_compare _ |}.

Definition types_r : Env.Repr Expr.type :=
  Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in 
    let lst := 
      Some ILEnv.bedrock_type_W ::
      Some ILEnv.bedrock_type_setting_X_state ::
      None ::
(*      None :: *)
      None ::
      Some ILEnv.bedrock_type_nat ::
      Some bedrock_type_listW :: nil
    in Env.listOptToRepr lst EmptySet_type.

Local Notation "'pcT'" := (tvType 0).
Local Notation "'stT'" := (tvType 1).
Local Notation "'wordT'" := (tvType 0).
Local Notation "'natT'" := (tvType 4).
Local Notation "'listWT'" := (tvType 5).

Local Notation "'wplusF'" := 0.
Local Notation "'wmultF'" := 2.
Local Notation "'wltF'" := 4.
Local Notation "'natToWF'" := 5.
Local Notation "'lengthF'" := 8.
Local Notation "'selF'" := 9.
Local Notation "'updF'" := 10.

Section parametric.
  Variable types' : list type.
  Definition types := repr types_r types'.
  Variable Prover : ProverT.

  Definition natToW_r : signature types.
    refine {| Domain := natT :: nil; Range := wordT |}.
    exact natToW.
  Defined.

  Definition wlength_r : signature types.
    refine {| Domain := listWT :: nil; Range := natT |}.
    exact (@length _).
  Defined.

  Definition sel_r : signature types.
    refine {| Domain := listWT :: wordT :: nil; Range := wordT |}.
    exact sel.
  Defined.

  Definition upd_r : signature types.
    refine {| Domain := listWT :: wordT :: wordT :: nil; Range := listWT |}.
    exact upd.
  Defined.

  Definition funcs_r : Env.Repr (signature types) :=
    Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in 
      let lst := 
        Some (ILEnv.wplus_r types) ::
        None ::
        Some (ILEnv.wmult_r types) ::
(*        None :: *)
        None ::
        Some (ILEnv.wlt_r types) ::
        Some (ILEnv.natToW_r types) ::
        Some (O_r types) ::
        Some (S_r types) ::
        Some wlength_r ::
        Some sel_r ::
        Some upd_r ::
        nil
      in Env.listOptToRepr lst (Default_signature _).

  Definition deref (e : expr) : option (expr * expr) :=
    match e with
      | Func wplusF (base :: offset :: nil) =>
        match offset with
          | Func wmultF (Func natToWF (k :: nil) :: offset :: nil) =>
            match toConst_nat k with
              | None => None
              | Some k => 
                match k with
                  | 4 => Some (base, offset)
                  | _ => None
                end
            end
          | Func natToWF (k :: nil) =>
            match toConst_nat k with
              | Some k => 
                match div4 k with
                  | None => None
                  | Some k' => Some (base, Func natToWF (toExpr_nat k' :: nil))
                end
              | None => None
            end
          | _ => None
        end
      | _ => None
    end.

  Definition sym_read (summ : Prover.(Facts)) (args : list expr) (p : expr)
    : option expr :=
    match args with
      | ws :: p' :: nil =>
        match deref p with
          | None => None
          | Some (base, offset) =>
            if Prover.(Prove) summ (Equal wordT p' base)
              && Prover.(Prove) summ (Func wltF (offset :: Func natToWF (Func lengthF (ws :: nil)
                :: nil) :: nil))
              then Some (Func selF (ws :: offset :: nil))
              else None
        end
      | _ => None
    end.

  Definition sym_write (summ : Prover.(Facts)) (args : list expr) (p v : expr)
    : option (list expr) :=
    match args with
      | ws :: p' :: nil =>
        match deref p with
          | None => None
          | Some (base, offset) =>
            if Prover.(Prove) summ (Equal wordT p' base)
              && Prover.(Prove) summ (Func wltF (offset :: Func natToWF (Func lengthF (ws :: nil)
                :: nil) :: nil))
              then Some (Func updF (ws :: offset :: v :: nil) :: p' :: nil)
              else None
        end
      | _ => None
    end.
End parametric.

Definition MemEval : MEVAL.PredEval.MemEvalPred.
  apply MEVAL.PredEval.Build_MemEvalPred.
  apply sym_read.
  apply sym_write.
  exact (fun _ _ _ _ => None).
  exact (fun _ _ _ _ _ => None).
Defined.

Ltac destr' E := destruct E. (*case_eq E; intros;
  try match goal with
        | [ H : _ = _ |- _ ] => rewrite H in *
      end.*)

Ltac destr simp E :=
  match E with
    | context[match _ with None => _ | _ => _ end] => fail 1
    | div4 _ => fail 1
    | toConst_nat _ => fail 1
    | _ => destr' E; discriminate || tauto
    | _ => destr' E; try (discriminate || tauto); [simp]
  end.

Ltac destr2 simp E :=
  match E with
    | context[match _ with None => _ | _ => _ end] => fail 1
    | div4 _ => fail 1
    | _ => destr' E; try (discriminate || tauto); [simp]
    | _ => destr' E; try (discriminate || tauto); [ | ]; simp
  end.

Ltac stripSuffix E :=
  match E with
    | ?E = _ => stripSuffix E
    | ?E _ => stripSuffix E
    | ?E _ _ => stripSuffix E
    | _ => E
  end.

Ltac doMatch simp P :=
  match P with
    | match ?E with 0 => _ | _ => _ end => destr2 simp E
    | match ?E with nil => _ | _ => _ end => destr simp E
    | match ?E with Var _ => _ | _ => _ end => destr2 simp E 
    | match ?E with tvProp => _ | _ => _ end => destr simp E
    | match ?E with None => _ | _ => _ end => destr simp E
    | match ?E with left _ => _ | _ => _ end => destr2 simp E
  end.

Ltac deconstruct' simp := 
  match goal with
    | [ H : Some _ = Some _ |- _ ] => injection H; clear H; intros; subst; simp
    | [ H : ?P |- _ ] =>
      let P := stripSuffix P in
         doMatch simp P
      || match P with
           | match ?P with None => _ | _ => _ end =>
             let P := stripSuffix P in
             doMatch simp P
         end
  end.

Ltac deconstruct := repeat deconstruct' ltac:(simpl in *).

Section correctness.
  Variable types' : list type.
  Definition types0 := types types'.

  Definition ssig : SEP.predicate types0.
    refine (SEP.PSig _ (listWT :: wordT :: nil) _).
    exact array.
  Defined.

  Definition ssig_r : Env.Repr (SEP.predicate types0) :=
    Eval cbv beta iota zeta delta [ Env.listOptToRepr ] in 
      let lst := 
        None :: Some ssig :: nil
      in Env.listOptToRepr lst (SEP.Default_predicate _).

  Variable funcs' : functions types0.
  Definition funcs := Env.repr (funcs_r _) funcs'.

  Variable Prover : ProverT.
  Variable Prover_correct : ProverT_correct Prover funcs.

  Lemma div4_correct' : forall n0 n m, (n < n0)%nat
    -> div4 n = Some m
    -> n = 4 * m.
    induction n0; simpl; intuition.
    destruct n; simpl in *.
    injection H0; omega.
    repeat destr ltac:(simpl in *) n.
    specialize (IHn0 n).
    destruct (div4 n).
    injection H0.
    rewrite (IHn0 n1); auto; omega.
    discriminate.
  Qed.

  Lemma div4_correct : forall n m, div4 n = Some m
    -> n = 4 * m.
    intros; eapply div4_correct'; eauto.
  Qed.    

  Lemma deref_correct : forall uvars vars e w base offset,
    exprD funcs uvars vars e wordT = Some w
    -> deref e = Some (base, offset)
    -> exists wb, exists wo,
      exprD funcs uvars vars base wordT = Some wb
      /\ exprD funcs uvars vars offset wordT = Some wo
      /\ w = wb ^+ $4 ^* wo.
    destruct e; simpl; intuition; try discriminate.
    repeat (deconstruct' ltac:(simpl in *); []).
    case_eq (exprD funcs uvars vars e wordT); intros;
      match goal with
        | [ H : _ = _ |- _ ] => rewrite H in *
      end; try discriminate.
    destruct f; try discriminate.
    { destruct l; try discriminate.
      destruct e0; try discriminate.
      do 6 (destruct f; try discriminate).
      do 2 (destruct l0; try discriminate).
      do 2 (destruct l; try discriminate).
      Require Import ExtLib.Tactics.Consider.
      consider (toConst_nat e0); intros; try discriminate.
      generalize  (@toConst_nat_sound types0 funcs _ n H0 uvars vars).
      match goal with
        | |- _ -> ?X =>
          change (exprD funcs uvars vars e0 natT = Some n -> X)
      end.
      intro H3. simpl in H. rewrite H3 in *.
      do 5 (destruct n; try discriminate).
      inversion H2; clear H2; subst.
      rewrite H1 in *.
      destruct (exprD funcs uvars vars offset wordT); try discriminate.
      inversion H; clear H; subst.
      do 2 eexists. split; eauto. }
    { do 3 (destruct f; try discriminate).
      do 2 (destruct l; try discriminate).
      consider (toConst_nat e0); intros; try discriminate.
      generalize  (@toConst_nat_sound types0 funcs _ n H0 uvars vars).
      match goal with
        | |- _ -> ?X =>
          change (exprD funcs uvars vars e0 natT = Some n -> X)
      end.
      match goal with
        | [ _ : context[div4 ?N] |- _ ] => 
          specialize (div4_correct N); destruct (div4 N)
      end; try discriminate.
      inversion H2; clear H2; subst; intros.
      simpl in *.
      specialize (H2 _ (refl_equal _)); subst.
      rewrite H1 in *. rewrite H3 in *.
      generalize (@toExpr_nat_sound types0 funcs n0 uvars vars).
      match goal with
        | |- _ -> ?X =>
          change (exprD funcs uvars vars (toExpr_nat n0) natT = Some n0 -> X)
      end.
      intro. rewrite H2.
      repeat (esplit || eassumption).
      inversion H; clear H; subst.
      replace (n0 + (n0 + (n0 + (n0 + 0)))) with (n0 * 4) by omega.
      rewrite natToW_times4.
      W_eq. }
  Qed.

  Fixpoint ptsto32m' sos (a : W) (offset : nat) (vs : list W) : hpropB sos :=
    match vs with
      | nil => Emp
      | v :: vs' => (a ^+ $(offset)) =*> v * ptsto32m' sos a (4 + offset) vs'
    end%Sep.

  Theorem ptsto32m'_in : forall a cs stn vs offset m,
    interp cs (ptsto32m _ a offset vs stn m)
    -> interp cs (ptsto32m' _ a offset vs stn m).
  Proof.
    induction vs.

    auto.

    unfold ptsto32m, ptsto32m'.
    fold ptsto32m; fold ptsto32m'.
    destruct vs; destruct offset; intros.

    replace (a ^+ $0) with a by W_eq.
    simpl.
    propxFo.
    exists m.
    exists smem_emp; intuition.
    apply split_comm; apply split_emp. 
    reflexivity.
    
    unfold ptsto32m'.
    apply simplify_bwd.
    exists m.
    exists smem_emp; intuition.
    split.
    apply split_comm; apply split_emp. reflexivity.
    split. 
    apply simplify_fwd; assumption.
    split.
    constructor.
    reflexivity.

    replace (a ^+ $0) with a by W_eq.
    apply simplify_fwd in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    apply simplify_bwd in H0.
    apply simplify_bwd in H1.
    apply simplify_bwd.
    exists x.
    exists x0.
    split; auto.
    split.
    apply simplify_fwd; assumption.
    apply simplify_fwd; auto.

    apply simplify_fwd in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H0.
    apply simplify_bwd in H0.
    apply simplify_bwd in H1.
    apply simplify_bwd.
    exists x.
    exists x0.
    split; auto.
    split.
    apply simplify_fwd; assumption.
    apply simplify_fwd; auto.
  Qed.

  Lemma smem_read_correct'' : forall cs base stn ws offset i m,
    interp cs (ptsto32m' _ base (offset * 4) ws stn m)
    -> (i < length ws)%nat
    -> smem_read_word stn (base ^+ $((offset + i) * 4)) m = Some (selN ws i).
  Proof.
    induction ws.

    simpl length.
    intros.
    elimtype False.
    nomega.

    simpl length.
    unfold ptsto32m'.
    fold ptsto32m'.
    intros.
    destruct i; simpl selN.
    replace (offset + 0) with offset by omega.
    apply simplify_fwd in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H1.
    destruct H1.
    simpl in H.
    eapply MSMF.split_multi_read; eauto.

    apply simplify_fwd in H.
    destruct H.
    destruct H.
    destruct H.
    destruct H1.
    apply simplify_bwd in H2.
    replace (4 + offset * 4) with (S offset * 4) in H2 by omega.
    eapply (IHws _ i) in H2.
    eapply split_comm in H.
    eapply MSMF.split_multi_read in H; eauto. unfold smem_read_word in H2.
    replace (offset + S i) with (S offset + i) by omega. auto. omega.
  Qed.

  Lemma smem_get_disjoint : forall a w1 w2 dom m1 m2,
    disjoint' dom m1 m2
    -> smem_get' dom a m1 = Some w1
    -> smem_get' dom a m2 = Some w2
    -> False.
  Proof.
    induction dom; simpl; intuition.
    discriminate.
    destruct (M.addr_dec a0 a); subst; try congruence.
    eauto.
    destruct (M.addr_dec a0 a); subst; try congruence.
    eauto.
  Qed.

  Lemma smem_read_word_disjoint : forall a m m1 m2 w1 w2 addrs,
    split m m1 m2
    -> smem_read_word addrs a m1 = Some w1
    -> smem_read_word addrs a m2 = Some w2
    -> False.
  Proof.
    unfold smem_read_word; intros. 
    unfold MultiMem.multi_read in *.
    generalize (split_disjoint _ _ _ H). clear H. intros. simpl in *.

    consider (smem_get a m1); intros; try congruence.
    assert (in_domain a m1). red. congruence.
    eapply H in H3. apply H3. red. 
    consider (smem_get a m2); try congruence.
  Qed.

  Lemma array_bound' : forall cs base stn ws m i,
    (0 < i < length ws)%nat
    -> base ^+ $(i * 4) = base
    -> interp cs (ptsto32m' _ base 0 ws stn m)
    -> False.
    destruct ws; simpl length; intros.

    elimtype False; omega.

    simpl in H1.
    propxFo.
    destruct i; try omega.
    generalize (@smem_read_correct'' cs base stn ws 1 i x0).
    simpl plus.
    rewrite H0.
    rewrite wplus_comm in H4.
    rewrite wplus_unit in H4.
    intuition.
    assert (i < length ws)%nat by omega; intuition.
    eapply smem_read_word_disjoint; eauto.
  Qed.

  Lemma pow2_pos : forall n, (pow2 n > 0)%nat.
    induction n; simpl; omega.
  Qed.

  Lemma pow2_monotone : forall n m,
    (n < m)%nat
    -> (pow2 n < pow2 m)%nat.
    induction 1; simpl; intuition.
    specialize (pow2_pos n).
    omega.
  Qed.

  Lemma pow2_mult : forall m n,
    pow2 n * pow2 m = pow2 (n + m).
    induction n; simpl; intuition.
    repeat rewrite <- IHn.
    repeat rewrite <- plus_n_O.
    apply Mult.mult_plus_distr_r.
  Qed.      

  Lemma array_bound : forall cs ws base stn m,
    interp cs (array ws base stn m)
    -> (length ws < pow2 32)%nat.
  Proof. 
    intros.
    Require Import Arith.
    destruct (lt_dec (length ws) (pow2 32)); auto.
    elimtype False.
    apply ptsto32m'_in in H.
    apply (@array_bound' _ _ _ _ _ (pow2 30)) in H; auto.
    split.
    unfold pow2; omega.
    specialize (@pow2_monotone 30 32).
    omega.
    change (pow2 30 * 4) with (pow2 30 * pow2 2).
    rewrite pow2_mult.
    simpl plus.
    clear.
    rewrite wplus_alt.
    unfold wplusN, wordBinN.
    rewrite natToWord_pow2.
    rewrite roundTrip_0.
    rewrite plus_0_r.
    apply natToWord_wordToNat.
  Qed.

  Lemma smem_read_correct' : forall cs base stn ws i m,
    interp cs (array ws base stn m)
    -> i < $(length ws)
    -> smem_read_word stn (base ^+ $4 ^* i) m = Some (sel ws i).
  Proof.
    unfold sel; intros; rewrite <- (@smem_read_correct'' cs base stn ws 0 (wordToNat i) m).
    f_equal.
    simpl plus.
    rewrite natToW_times4.
    unfold natToW.
    rewrite natToWord_wordToNat.
    W_eq.

    apply ptsto32m'_in; auto. 

    red in H0.
    apply Nlt_out in H0.
    repeat rewrite wordToN_nat in *.
    repeat rewrite Nat2N.id in *.
    rewrite wordToNat_natToWord_idempotent in H0; auto.
    apply array_bound in H.
    apply Nlt_in.
    rewrite Nat2N.id.
    rewrite Npow2_nat.
    assumption.
  Qed.

  Lemma sym_read_correct : forall args uvars vars cs summ pe p ve m stn,
    sym_read Prover summ args pe = Some ve ->
    Valid Prover_correct uvars vars summ ->
    exprD funcs uvars vars pe wordT = Some p ->
    match 
      applyD types0 (exprD funcs uvars vars) (SEP.SDomain ssig) args _ (SEP.SDenotation ssig)
      with
      | None => False
      | Some p => PropX.interp cs (p stn m)
    end ->
    match exprD funcs uvars vars ve wordT with
      | Some v =>
        smem_read_word stn p m = Some v
      | _ => False
    end.
  Proof.
    simpl; intuition.
    do 3 (destruct args; simpl in *; intuition; try discriminate).
    generalize (deref_correct uvars vars pe); destr ltac:(simpl in *) (deref pe); intro Hderef.
    destruct p0.
    match goal with
      | [ _ : (if ?E then _ else _) = Some _ |- _ ] => case_eq E; intro Heq; rewrite Heq in *
    end; try discriminate.
    eapply andb_true_iff in Heq. destruct Heq.
    eapply Prove_correct in H3. 2: eassumption.
    eapply Prove_correct in H4. 2: eassumption.
    unfold ValidProp in *. simpl in *.
    inversion H; clear H; subst.
    specialize (Hderef _ _ _ H1 eq_refl).
    destruct Hderef. destruct H. destruct H. destruct H5.
    unfold Provable in *; simpl in *.
    rewrite H in *. rewrite H5 in *.
    consider (exprD funcs uvars vars e listWT); intros; try solve [ intuition ].
    consider (exprD funcs uvars vars e0 wordT); intros; try solve [ intuition ].
    specialize (H7 (ex_intro _ _ (refl_equal _))).
    specialize (H4 (ex_intro _ _ (refl_equal _))); subst.
    eapply smem_read_correct'; eauto.
  Qed.

  Theorem ptsto32m'_out : forall a cs stn vs offset m,
    interp cs (ptsto32m' _ a offset vs stn m)
    -> interp cs (ptsto32m _ a offset vs stn m).
  Proof.
    induction vs.

    auto.

    unfold ptsto32m, ptsto32m'.
    fold ptsto32m; fold ptsto32m'.
    destruct vs; destruct offset; intros.

    replace (a ^+ $0) with a in * by W_eq.
    simpl.
    propxFo.
    { rewrite <- H1.
      f_equal.
      eapply split_emp. subst.
      apply split_comm; eauto. }
    { apply split_comm in H3.
      subst. eapply split_emp in H3. red in H3. subst.
      specialize (H7 a'). intuition. }

    { apply simplify_fwd in H.
      destruct H.
      destruct H.
      destruct H.
      destruct H0.
      apply simplify_bwd in H0.
      replace m with x; auto.
      symmetry; eapply split_emp.
      apply split_comm; eauto.    
      simpl in H. simpl in H1. intuition; subst; auto. }

    { replace (a ^+ $0) with a in * by W_eq.
      apply simplify_fwd in H.
      apply simplify_bwd.
      destruct H.
      destruct H.
      destruct H.
      destruct H0.
      exists x; exists x0; split.
      auto.
      split; auto.
      apply simplify_fwd.
      apply simplify_bwd in H1.
      auto. }

    { apply simplify_fwd in H.
      apply simplify_bwd.
      destruct H.
      destruct H.
      destruct H.
      destruct H0.
      exists x; exists x0; split.
      auto.
      split; auto.
      apply simplify_fwd.
      apply simplify_bwd in H1.
      auto. }
    Qed.

  Lemma smem_write_correct'' : forall cs base stn v ws i m offset,
    (i < length ws)%nat
    -> interp cs (ptsto32m' _ base (offset * 4) ws stn m)
    -> exists m', smem_write_word stn (base ^+ $4 ^* $(offset + i)) v m = Some m'
      /\ PropX.interp cs ((ptsto32m' _ base (offset * 4) (updN ws i v)) stn m').
  Proof.
    induction ws; simpl length; intros.

    inversion H.

    unfold ptsto32m' in *.
    fold ptsto32m' in *.
    destruct i; simpl updN.
    { rewrite wmult_comm.
      rewrite <- natToW_times4.
      replace (offset + 0) with offset by omega.
      unfold ptsto32m'.
      fold ptsto32m'.
      apply simplify_fwd in H0.
      destruct H0.
      destruct H0.
      destruct H0.
      destruct H1.
      hnf in H1.
      unfold natToW.
      destruct H1.
      
      unfold smem_read_word in *.

      match goal with 
        | _ : ?X = Some _ |- _ =>
          assert (X <> None) by congruence
      end.
      specialize (@MSMF.smem_set_get_valid_multi W 4 (fun a : W =>
                                                        let '(a0, b, c, d) := footprint_w a in (a0, (b, (c, (d, tt)))))
                                                 (fun v : MultiMem.vector B 4 =>
                                                    let '(a, (b, (c, (d, _)))) := v in implode stn (a, b, c, d))
                                                 (fun v0 : W =>
                                                    let '(a0, b, c, d) := explode stn v0 in (a0, (b, (c, (d, tt)))))
                                                 (base ^+ $ (offset * 4)) v x H4); clear H4; intro.
      match goal with 
        | _ : not (?X = None) |- _ =>
          consider X; try congruence; intros
      end.
      clear H5.
      simpl in H0.
      generalize H4.
      eapply MSMF.split_multi_write in H4; try solve [ intuition eauto ].
      destruct H4. destruct H4. intro.
      exists (join s x0); split. 
      { destruct H4; subst; auto. }
      { unfold starB, star, STK.istar.
        eapply Exists_I with (B := s). eapply Exists_I with (B := x0).
        eapply And_I.
        apply Inj_I. destruct H4; split; auto.
        eapply And_I. 2: propxFo.
        apply Inj_I.
        split.
        { unfold smem_read_word, MultiMem.multi_read.
          eapply MSMF.smem_read_write_eq_multi' with (k := (fun v0 : MultiMem.vector B 4 =>
      let '(a0, (b, (c, (d, _)))) := v0 in implode stn (a0, b, c, d))) in H6.
          clear - H6. etransitivity. eapply H6. f_equal.
          clear. consider (explode stn v); simpl. destruct p as [ [ ] ]. intros. 
          rewrite <- H. eapply implode_explode.
          Theorem footprint_w_NoDup : forall p,
                                        MultiMem.NoDup_v M.addr 4
                                                         (let '(a0, b, c, d) := footprint_w p in
                                                          (a0, (b, (c, (d, tt))))).
          Proof.
            clear. Opaque natToWord. simpl; intros.
            cut (MultiMem.NoDup_v M.addr 4
                                     (p ^+ $(0), (p ^+ $ (1), (p ^+ $ (2), (p ^+ $ (3), tt))))).
            rewrite Word.wplus_comm. rewrite Word.wplus_unit. auto.
            repeat constructor; simpl; intuition; auto;
            match goal with
              | H0 : _ = _ |- _ =>
                do 2 (rewrite (Word.wplus_comm p) in H0); apply Word.wplus_cancel in H0; inversion H0
            end.
          Qed.
          eapply footprint_w_NoDup. }
        { intro. specialize (H3 a'). intuition.
          erewrite <- MSMF.smem_multi_write_footprint.
          eassumption. eapply H6.
          clear - H8 H7 H9 H11. simpl. intuition. } } }
    { simpl.
      eapply STK.interp_star in H0. do 3 destruct H0. destruct H1.
      replace (base ^+ $ (4) ^* $ (offset + S i)) with
              (base ^+ $ (4) ^* $ ((S offset) + i)) in H2 by (f_equal; f_equal; f_equal; omega).
      assert (i < length ws)%nat by omega.
      destruct (@IHws i x0 (S offset) H3 H2).
      destruct H4. replace (offset + S i)%nat with (S offset + i)%nat by omega.
      generalize H4; intro.
      eapply MSMF.split_multi_write in H4. 2: eapply split_comm; eassumption.
      destruct H4. intuition. eexists. split. eapply H8.
      eapply Exists_I with (B := x).
      eapply Exists_I with (B := x1).
      eapply And_I.
      2: eapply And_I; eauto.
      eapply Inj_I. eapply split_comm; auto. }
  Qed.

  Lemma smem_write_correct' : forall i ws cs base stn m v,
    i < natToW (length ws)
    -> interp cs (array ws base stn m)
    -> exists m', smem_write_word stn (base ^+ $4 ^* i) v m = Some m'
      /\ PropX.interp cs ((array (upd ws i v) base) stn m').
  Proof.
    intros.
    destruct (@smem_write_correct'' cs base stn v ws (wordToNat i) m 0).
    
    red in H.
    apply Nlt_out in H.
    repeat rewrite wordToN_nat in *.
    repeat rewrite Nat2N.id in *.
    rewrite wordToNat_natToWord_idempotent in H; auto.
    apply array_bound in H0.
    apply Nlt_in.
    rewrite Nat2N.id.
    rewrite Npow2_nat.
    assumption. 

    apply ptsto32m'_in; auto.

    intuition.
    simpl plus in *.
    simpl mult in *.
    rewrite natToWord_wordToNat in H2.
    exists x; split; auto.
    apply ptsto32m'_out; auto.
  Qed.

  Lemma sym_write_correct : forall args uvars vars cs summ pe p ve v m stn args',
    sym_write Prover summ args pe ve = Some args' ->
    Valid Prover_correct uvars vars summ ->
    exprD funcs uvars vars pe wordT = Some p ->
    exprD funcs uvars vars ve wordT = Some v ->
    match
      applyD types0 (@exprD _ funcs uvars vars) (SEP.SDomain ssig) args _ (SEP.SDenotation ssig)
      with
      | None => False
      | Some p => PropX.interp cs (p stn m)
    end ->
    match 
      applyD types0 (@exprD _ funcs uvars vars) (SEP.SDomain ssig) args' _ (SEP.SDenotation ssig)
      with
      | None => False
      | Some pr => 
        match smem_write_word stn p v m with
          | None => False
          | Some sm' => PropX.interp cs (pr stn sm')
        end
    end.
  Proof.
    simpl; intuition.
    do 3 (destruct args; simpl in *; intuition; try discriminate).
    generalize (deref_correct uvars vars pe); destr ltac:(simpl in *) (deref pe); intro Hderef.
    destruct p0.

    repeat match goal with
             | [ H : Valid _ _ _ _, _ : context[Prove Prover ?summ ?goal] |- _ ] =>
               match goal with
                 | [ _ : context[ValidProp _ _ _ goal] |- _ ] => fail 1
                 | _ => specialize (Prove_correct Prover_correct summ H (goal := goal)); intro
               end
           end; unfold ValidProp in *; simpl in *.

    match goal with
      | [ _ : (if ?E then _ else _) = Some _ |- _ ] => case_eq E; intro Heq; rewrite Heq in *
    end; try discriminate.
    unfold types0 in *; simpl in *.
    unfold Provable in *; simpl in *.
    deconstruct.
    repeat match goal with
             | [ H : _ |- _ ] => apply andb_prop in H; intuition
           end.
    rewrite H1 in *.
    rewrite H2 in *.
    specialize (Hderef _ _ _ (refl_equal _) (refl_equal _)); destruct Hderef as [ ? [ ] ]; intuition.
    subst.
    simpl in *.
    rewrite H8 in *.
    rewrite H5 in *.
    specialize (H7 (ex_intro _ _ (refl_equal _))).
    specialize (H4 (ex_intro _ _ (refl_equal _))); subst.
    red in H3.

    eapply smem_write_correct' in H3; eauto.
    destruct H3; intuition.
    rewrite H7; assumption.
  Qed.
End correctness.

Definition MemEvaluator : MEVAL.MemEvaluator :=
  Eval cbv beta iota zeta delta [ MEVAL.PredEval.MemEvalPred_to_MemEvaluator ] in 
    @MEVAL.PredEval.MemEvalPred_to_MemEvaluator MemEval 1.

Theorem MemEvaluator_correct types' funcs' preds'
  : @MEVAL.MemEvaluator_correct (Env.repr types_r types') (tvType 0) (tvType 1) 
  MemEvaluator (funcs funcs') (Env.repr (ssig_r _) preds')
  (IL.settings * IL.state) (tvType 0) (tvType 0)
  (@IL_mem_satisfies (types types')) (@IL_ReadWord (types types')) (@IL_WriteWord (types types'))
  (@IL_ReadByte (types types')) (@IL_WriteByte (types types')).
Proof.
  intros. eapply (@MemPredEval_To_MemEvaluator_correct (types types')); try reflexivity;
  intros; unfold MemEval in *; simpl in *; try discriminate.
  { generalize (@sym_read_correct types' funcs' P PE). simpl in *. intro.
    eapply H3 in H; eauto. }
  { generalize (@sym_write_correct types' funcs' P PE). simpl in *. intro.
    eapply H4 in H; eauto. }
Qed.

Definition pack : MEVAL.MemEvaluatorPackage types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0)
  IL_mem_satisfies IL_ReadWord IL_WriteWord IL_ReadByte IL_WriteByte :=

  @MEVAL.Build_MemEvaluatorPackage types_r (tvType 0) (tvType 1) (tvType 0) (tvType 0) 
  IL_mem_satisfies IL_ReadWord IL_WriteWord IL_ReadByte IL_WriteByte
  types_r
  funcs_r
  (fun ts => Env.listOptToRepr (None :: Some (ssig ts) :: nil)
    (SEP.Default_predicate (Env.repr types_r ts)))
  MemEvaluator
  (fun ts fs ps => MemEvaluator_correct _ _).
