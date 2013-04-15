Require Import AutoSepExt.
Export AutoSepExt.

Ltac refold' A :=
  progress change (fix length (l : list A) : nat :=
    match l with
      | nil => 0
      | _ :: l' => S (length l')
    end) with (@length A) in *
  || (progress change (fix app (l0 m : list A) : list A :=
    match l0 with
      | nil => m
      | a1 :: l1 => a1 :: app l1 m
    end) with (@app A) in *)
  || (progress change (fix rev (l : list W) : list W :=
    match l with
      | nil => nil
      | x8 :: l' => (rev l' ++ x8 :: nil)%list
    end) with (@rev A) in *)
  || (progress change (fix rev_append (l l' : list A) : list A :=
    match l with
      | nil => l'
      | a1 :: l0 => rev_append l0 (a1 :: l')
    end) with (@rev_append A) in *).

Ltac refold :=
  fold plus in *; fold minus in *;
    repeat match goal with
             | [ _ : list ?A |- _ ] =>
               match A with
                 | _ => refold' A
                 | W => refold' (word 32)
               end
             | [ |- context[match ?X with nil => ?D | x :: _ => x end] ] =>
               change (match X with nil => D | x :: _ => x end) with (List.hd D X)
             | [ |- context[match ?X with nil => nil | _ :: x => x end] ] =>
               change (match X with nil => nil | _ :: x => x end) with (List.tl X)
           end.

Require Import Bool.
Require Import Conditional Lambda.
Export Conditional Lambda.

Ltac vcgen_simp := cbv beta iota zeta delta [map app imps
  LabelMap.add Entry Blocks Postcondition VerifCond
  Straightline_ Seq_ Diverge_ Fail_ Skip_ Assert_
  Structured.If_ Structured.While_ Goto_ Structured.Call_ IGoto
  setArgs Programming.Reserved Programming.Formals Programming.Precondition
  importsMap fullImports buildLocals blocks union Nplus Nsucc length N_of_nat
  List.fold_left ascii_lt string_lt label'_lt
  LabelKey.compare' LabelKey.compare LabelKey.eq_dec
  LabelMap.find
  toCmd Seq Instr Diverge Fail Skip Assert_
  Programming.If_ Programming.While_ Goto Programming.Call_ RvImm'
  Assign' localsInvariant
  regInL lvalIn immInR labelIn variableSlot string_eq ascii_eq
  andb eqb qspecOut
  ICall_ Structured.ICall_
  Assert_ Structured.Assert_
  LabelMap.Raw.find LabelMap.this LabelMap.Raw.add
  LabelMap.empty LabelMap.Raw.empty string_dec
  Ascii.ascii_dec string_rec string_rect sumbool_rec sumbool_rect Ascii.ascii_rec Ascii.ascii_rect
  Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym
  fst snd labl
  Ascii.N_of_ascii Ascii.N_of_digits N.compare Nmult Pos.compare Pos.compare_cont
  Pos.mul Pos.add LabelMap.Raw.bal
  Int.Z_as_Int.gt_le_dec Int.Z_as_Int.ge_lt_dec LabelMap.Raw.create
  ZArith_dec.Z_gt_le_dec Int.Z_as_Int.plus Int.Z_as_Int.max LabelMap.Raw.height
  ZArith_dec.Z_gt_dec Int.Z_as_Int._1 BinInt.Z.add Int.Z_as_Int._0 Int.Z_as_Int._2 BinInt.Z.max
  ZArith_dec.Zcompare_rec ZArith_dec.Z_ge_lt_dec BinInt.Z.compare ZArith_dec.Zcompare_rect
  ZArith_dec.Z_ge_dec label'_eq label'_rec label'_rect
  COperand1 CTest COperand2 Pos.succ
  makeVcs

  Cond_ Cond
  Lambda__ Lambda_
].

Ltac vcgen :=
(*TIME time "vcgen:structured_auto" ( *)
  structured_auto vcgen_simp 
(*TIME ) *);
(*TIME time "vcgen:finish" ( *)
  autorewrite with sepFormula in *; simpl in *;
(*    change (@starB nil) with (ST.star) in * ; *)
    unfold hvarB, hpropB in *; fold hprop in *; refold
(*TIME ) *).

Hint Extern 1 => tauto : contradiction.
Hint Extern 1 => congruence : contradiction.

Ltac sep_easy := auto with contradiction.

Lemma frame_reflexivity : forall p q,
  q = (fun pr => p (fst pr) (snd pr))
  -> himp p (fun st m => q (st, m)).
  intros; hnf; simpl; intros; subst.
  apply Imply_I; eauto.
Qed.

Ltac rereg :=
  repeat match goal with
           | [ _ : context[Regs (match ?st with
                                   | (_, y) => y
                                 end) ?r] |- _ ] =>
             change (Regs (let (_, y) := st in y) r) with (st#r) in *
           | [ |- context[Regs (match ?st with
                                  | (_, y) => y
                                end) ?r] ] =>
             change (Regs (let (_, y) := st in y) r) with (st#r) in *
         end.
  
Ltac sep_firstorder := sep_easy;
  repeat match goal with
           | [ H : Logic.ex _ |- _ ] => destruct H
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ |- Logic.ex _ ] => sep_easy; eexists
           | [ |- _ /\ _ ] => split
           | [ |- forall x, _ ] => intro
           | [ |- _ = _ ] => reflexivity
           | [ |- himp _ _ ] => reflexivity
             || (apply frame_reflexivity; try match goal with
                                                | [ |- _ = ?X ] => instantiate (1 := X)
                                              end; apply refl_equal)
         end; sep_easy; autorewrite with sepFormula; rereg; try subst.

Require Import NArith.
Import TacPackIL.

Ltac clear_junk :=
  repeat match goal with
           | [ H : True |- _ ] => clear H
           | [ H : ?X = ?X |- _ ] => clear H
           | [ H : ?X, H' : ?X |- _ ] => clear H'
         end.

Ltac evaluate ext :=
  repeat match goal with
           | [ H : ?P -> False |- _ ] => change (not P) in H
         end;
  ILTac.sym_eval ltac:(ILTacCommon.isConst) ext;
  clear_junk.

Ltac cancel ext := 
  sep_canceler ltac:(ILTacCommon.isConst) ext;
  sep_firstorder;
  clear_junk.

Ltac unf := unfold substH.
Ltac reduce := Programming.reduce unf.
Ltac ho := Programming.ho unf; reduce.

Theorem implyR : forall pc state specs (P Q R : PropX pc state),
  interp specs (P ---> R)
  -> interp specs (P ---> Q ---> R)%PropX.
  intros.
  do 2 apply Imply_I.
  eapply Imply_E.
  eauto.
  constructor; simpl; tauto.
Qed.

Inductive pureConsequences : HProp -> list Prop -> Prop :=
| PurePure : forall P, pureConsequences [| P |]%Sep (P :: nil)
| PureStar : forall P P' Q Q', pureConsequences P P'
  -> pureConsequences Q Q'
  -> pureConsequences (P * Q)%Sep (P' ++ Q')
| PureOther : forall P, pureConsequences P nil.

Theorem pureConsequences_correct : forall P P',
  pureConsequences P P'
  -> forall specs stn st, interp specs (P stn st ---> [| List.Forall (fun p => p) P' |]%PropX).
Proof.
  induction 1; intros.

  unfold injB, inj.
  apply Imply_I.
  eapply Inj_E.
  unfold STK.iinj, STK.iinjX.
  eapply And_E1; apply Env; simpl; eauto. 
  intro; apply Inj_I; repeat constructor; assumption.

  unfold starB, star, STK.istar.
  apply Imply_I.
  eapply Exists_E.
  apply Env; simpl; eauto.
  simpl; intro.
  eapply Exists_E.
  apply Env; simpl; left; eauto.
  simpl; intro.
  eapply Inj_E.
  eapply Imply_E.
  apply interp_weaken; apply IHpureConsequences1.
  eapply And_E1; eapply And_E2; apply Env; simpl; eauto.
  intro.
  eapply Inj_E.
  eapply Imply_E.
  apply interp_weaken; apply IHpureConsequences2.
  do 2 eapply And_E2; apply Env; simpl; eauto.
  intro.
  apply Inj_I.
  apply Forall_app; auto.

  apply Imply_I; apply Inj_I; auto.
Qed.

Theorem extractPure : forall specs P Q Q' R st,
  pureConsequences Q Q'
  -> (List.Forall (fun p => p) Q' -> interp specs (P ---> R))
  -> interp specs (P ---> ![Q] st ---> R)%PropX.
  intros.
  do 2 apply Imply_I.
  eapply Inj_E.
  eapply Imply_E.
  apply interp_weaken.
  apply pureConsequences_correct; eauto.
  rewrite sepFormula_eq.
  unfold sepFormula_def.
  apply Env; simpl; eauto.
  intro.
  eapply Imply_E.
  eauto.
  apply Env; simpl; eauto.
Qed.

Ltac words := 
  repeat match goal with
           | [ H : _ = _ |- _ ] => rewrite H
         end; 
         match goal with
           | |- ?G => has_evar G ; fail 2
           | _ => W_eq
         end.

Definition locals_return ns vs avail p (ns' : list string) (avail' offset : nat) :=
  locals ns vs avail p.

Theorem create_locals_return : forall ns' avail' ns avail offset vs p,
  locals ns vs avail p = locals_return ns vs avail p ns' avail' offset.
  reflexivity.
Qed.

Definition ok_return (ns ns' : list string) (avail avail' offset : nat) :=
  (avail >= avail' + length ns')%nat
  /\ offset = 4 * length ns.

Ltac peelPrefix ls1 ls2 :=
  match ls1 with
    | nil => ls2
    | ?x :: ?ls1' =>
      match ls2 with
        | x :: ?ls2' => peelPrefix ls1' ls2'
      end
  end.

Global Opaque merge.

Theorem use_HProp_extensional : forall p, HProp_extensional p
  -> (fun st sm => p st sm) = p.
  auto.
Qed.

Ltac descend := 
  (*TIME time "descend:descend" *)
  Programming.descend; 
  (*TIME time "descend:reduce" *)
  reduce;
  (*TIME time "descend:unfold_simpl" ( *)
  unfold hvarB; simpl; rereg
  (*TIME ) *);
  (*TIME time "descend:loop" *)
    (repeat match goal with
             | [ |- context[fun stn0 sm => ?f stn0 sm] ] =>
               rewrite (@use_HProp_extensional f) by auto
             | [ |- context[fun stn0 sm => ?f ?a stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b ?c stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b c)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b ?c ?d stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b c d)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b ?c ?d ?e stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b c d e)) by auto
             | [ |- context[fun stn0 sm => ?f ?a ?b ?c ?d ?e ?f stn0 sm] ] =>
               rewrite (@use_HProp_extensional (f a b c d e f)) by auto
           end);
    try match goal with
          | [ p : (settings * state)%type |- _ ] => destruct p; simpl in *
        end.

Definition locals_call ns vs avail p (ns' : list string) (avail' : nat) (offset : nat) :=
  locals ns vs avail p.

Definition ok_call (ns ns' : list string) (avail avail' : nat) (offset : nat) :=
  (length ns' <= avail)%nat
  /\ (avail' <= avail - length ns')%nat
  /\ NoDup ns'
  /\ offset = 4 * length ns.

Definition excessStack (p : W) (ns : list string) (avail : nat) (ns' : list string) (avail' : nat) :=
  reserved (p ^+ natToW (4 * (length ns + length ns' + avail')))
  (avail - length ns' - avail').

Lemma make_call : forall ns ns' vs avail avail' p offset,
  ok_call ns ns' avail avail' offset
  -> locals_call ns vs avail p ns' avail' offset ===>
  locals ns vs 0 p
  * Ex vs', locals ns' vs' avail' (p ^+ natToW offset)
  * excessStack p ns avail ns' avail'.
Proof.
  unfold ok_call; intuition; subst; eapply do_call; eauto.
Qed.

Lemma make_return : forall ns ns' vs avail avail' p offset,
  ok_return ns ns' avail avail' offset
  -> (locals ns vs 0 p
    * Ex vs', locals ns' vs' avail' (p ^+ natToW offset)
    * excessStack p ns avail ns' avail')
  ===> locals_return ns vs avail p ns' avail' offset.
  unfold ok_return; intuition; subst; apply do_return; omega || words.
Qed.

Definition locals_in ns vs avail p (ns' ns'' : list string) (avail' : nat) :=
  locals ns vs avail p.

Open Scope list_scope.

Definition ok_in (ns : list string) (avail : nat) (ns' ns'' : list string) (avail' : nat) :=
  ns ++ ns' = ns'' /\ (length ns' <= avail)%nat /\ NoDup (ns ++ ns')
  /\ avail' = avail - length ns'.

Theorem init_in : forall ns ns' ns'' vs avail p avail',
  ok_in ns avail ns' ns'' avail'
  -> locals_in ns vs avail p ns' ns'' avail' ===>
  Ex vs', locals ns'' (merge vs vs' ns) avail' p.
  unfold ok_in; intuition; subst; apply prelude_in; auto.
Qed.

Definition locals_out ns vs avail p (ns' ns'' : list string) (avail' : nat) :=
  locals ns vs avail p.

Definition ok_out (ns : list string) (avail : nat) (ns' ns'' : list string) (avail' : nat) :=
  ns ++ ns' = ns'' /\ (length ns' <= avail)%nat
  /\ avail' = avail - length ns'.

Theorem init_out : forall ns ns' ns'' vs avail p avail',
  ok_out ns avail ns' ns'' avail'
  -> locals ns'' vs avail' p
  ===> locals_out ns vs avail p ns' ns'' avail'.
  unfold ok_out; intuition; subst; apply prelude_out; auto.
Qed.

Ltac prepare fwd bwd := 
  let the_unfold_tac x := 
    eval unfold empB, injB, injBX, starB, exB, hvarB in x
  in
  ILAlgoTypes.Tactics.Extension.extend the_unfold_tac
    ILTacCommon.isConst auto_ext' tt tt (make_call, init_in, fwd) (make_return, init_out, bwd).

Definition auto_ext : TacPackage.
  prepare tt tt.
Defined.

Theorem create_locals_out : forall ns' ns'' avail' ns avail vs p,
  locals ns vs avail p = locals_out ns vs avail p ns' ns'' avail'.
  reflexivity.
Qed.

Ltac step ext :=
  let considerImp pre post :=
    try match post with
          | context[locals ?ns ?vs ?avail _] =>
            match pre with
              | context[excessStack _ ns avail ?ns' ?avail'] =>
                match avail' with
                  | avail => fail 1
                  | _ =>
                    match pre with
                      | context[locals ns ?vs' 0 ?sp] =>
                        match goal with
                          | [ _ : _ = sp |- _ ] => fail 1
                          | _ => equate vs vs';
                            let offset := eval simpl in (4 * List.length ns) in
                              rewrite (create_locals_return ns' avail' ns avail offset);
                                assert (ok_return ns ns' avail avail' offset)%nat by (split; [
                                  simpl; omega
                                  | reflexivity ] ); autorewrite with sepFormula;
                                generalize dependent vs'; intros
                        end
                    end
                end
              | context[locals ?ns' ?vs' ?avail' _] =>
                match avail' with
                  | avail => fail 1
                  | _ =>
                    match vs' with
                      | vs => fail 1
                      | _ => let ns'' := peelPrefix ns ns' in
                        rewrite (create_locals_out ns'' ns' avail' ns avail);
                          assert (ok_out ns avail ns'' ns' avail')%nat by (split; [
                            reflexivity
                            | split; [
                              simpl; omega
                              | reflexivity ] ] )
                    end
                end
            end
        end;
    progress cancel ext in

  match goal with
    | [ |- _ _ = Some _ ] => solve [ eauto ]
    | [ _ : interp _ (![ ?pre ] _) |- interp _ (![ ?post ] _) ] => considerImp pre post
    | [ |- interp _ (![?pre]%PropX _ ---> ![?post]%PropX _) ] => considerImp pre post
    | [ |- himp ?pre ?post ] => considerImp pre post
    | [ |- interp _ (_ _ _ ?x ---> _ _ _ ?y ---> _ ?x)%PropX ] =>
      match y with
        | x => fail 1
        | _ => eapply extractPure; [ repeat constructor
          | cbv zeta; simpl; intro; repeat match goal with
                                             | [ H : List.Forall _ nil |- _ ] => clear H
                                             | [ H : List.Forall _ (_ :: _) |- _ ] => inversion H; clear H; subst
                                           end; clear_junk ]
        | _ => apply implyR
      end
    | _ => ho; rereg
  end.

Ltac slotVariable E :=
  match E with
    | 4 => constr:"0"
    | 8 => constr:"1"
    | 12 => constr:"2"
    | 16 => constr:"3"
    | 20 => constr:"4"
    | 24 => constr:"5"
    | 28 => constr:"6"
    | 32 => constr:"7"
    | 36 => constr:"8"
    | 40 => constr:"9"
  end.

Ltac slotVariables E :=
  match E with
    | Binop (LvReg Rv) (RvLval (LvReg Sp)) Plus (RvImm (natToW _))
      :: Assign (LvMem (Indir Rv (natToW ?slot))) _
      :: ?E' =>
      let v := slotVariable slot in
        let vs := slotVariables E' in
          constr:(v :: vs)
    | _ :: ?E' => slotVariables E'
    | nil => constr:(@nil string)
  end.

Ltac post := 
  (*TIME time "post:propxFo" *)
  propxFo; 
  (*TIME time "post:autorewrite" ( *)
  autorewrite with sepFormula in *
  (*TIME ) *) ;
  unfold substH in *;
  (*TIME time "post:simpl" ( *)
  simpl in *; rereg; autorewrite with IL;
    try match goal with
          | [ H : context[locals ?ns ?vs ?avail ?p]
              |- context[locals ?ns' _ ?avail' _] ] =>
            match avail' with
              | avail => fail 1
              | _ =>
                (let ns'' := peelPrefix ns ns' in
                 let exposed := eval simpl in (avail - avail') in
                 let new := eval simpl in (List.length ns' - List.length ns) in
                 match new with
                   | exposed =>
                     let avail' := eval simpl in (avail - List.length ns'') in
                     change (locals ns vs avail p) with (locals_in ns vs avail p ns'' ns' avail') in H;
                       assert (ok_in ns avail ns'' ns' avail')%nat
                         by (split; [
                           reflexivity
                           | split; [simpl; omega
                             | split; [ repeat constructor; simpl; intuition congruence
                               | reflexivity ] ] ])                        
                 end)
                || (let offset := eval simpl in (4 * List.length ns) in
                  change (locals ns vs avail p) with (locals_call ns vs avail p ns' avail' offset) in H;
                  assert (ok_call ns ns' avail avail' offset)%nat
                    by (split; [ simpl; omega
                      | split; [ simpl; omega
                        | split; [ repeat constructor; simpl; intuition congruence
                          | reflexivity ] ] ]))
            end
          | [ _ : evalInstrs _ _ ?E = None, H : context[locals ?ns ?vs ?avail ?p] |- _ ] =>
            let ns' := slotVariables E in
            match ns' with
              | nil => fail 1
              | _ =>
                let ns' := constr:("rp" :: ns') in
                  let offset := eval simpl in (4 * List.length ns) in
                    change (locals ns vs avail p) with (locals_call ns vs avail p ns' 0 offset) in H;
                      assert (ok_call ns ns' avail 0 offset)%nat
                        by (split; [ simpl; omega
                          | split; [ simpl; omega
                            | split; [ repeat constructor; simpl; intuition congruence
                              | reflexivity ] ] ])
            end
        end
  (*TIME ) *).

Ltac sep' ext := 
  post; evaluate ext; descend; repeat (step ext; descend).

Ltac sep ext :=
  match goal with
    | [ |- context[Assign (LvMem (Indir Sp (natToW 0))) (RvLval (LvReg Rp)) :: nil] ] =>
      sep' auto_ext (* Easy case; don't bring the hints into it *)
    | _ => sep' ext
  end.

Ltac sepLemma := unfold Himp in *; simpl; intros; cancel auto_ext.

Ltac sepLemmaLhsOnly :=
  let sllo Q := remember Q;
    match goal with
      | [ H : ?X = Q |- _ ] => let H' := fresh in
        assert (H' : bool -> X = Q) by (intro; assumption);
          clear H; rename H' into H;
            sepLemma; rewrite (H true); clear H
    end in
    simpl; intros;
      match goal with
        | [ |- _ ===> ?Q ] => sllo Q
        | [ |- himp _ ?Q ] => sllo Q
      end.

Ltac sep_auto := sep' auto_ext.

Hint Rewrite sel_upd_eq sel_upd_ne using congruence : sepFormula.

Lemma sel_merge : forall vs vs' ns nm,
  In nm ns
  -> sel (merge vs vs' ns) nm = sel vs nm.
  intros.
  generalize (merge_agree vs vs' ns); intro Hl.
  eapply Forall_forall in Hl; eauto.
Qed.

Hint Rewrite sel_merge using (simpl; tauto) : sepFormula.

Theorem lift0 : forall P, lift nil P = P.
  reflexivity.
Qed.

Hint Rewrite lift0 : sepFormula.

(* Within [H], find a conjunct [P] such that [which P] doesn't fail, and reassocate [H]
 * to put [P] in front. *)
Ltac toFront which H :=
  let rec toFront' P k :=
    match P with
      | ST.star ?Q ?R =>
        toFront' Q ltac:(fun it P' => k it (ST.star P' R))
        || toFront' R ltac:(fun it P' => k it (ST.star P' Q))
          || fail 2
      | _ => which P; k P (@ST.emp W (settings * state) nil)
    end in
    match type of H with
      | interp ?specs (![ ?P ] ?st) => toFront' P ltac:(fun it P' =>
        let H' := fresh in
          assert (H' : interp specs (![ ST.star it P' ] st)) by step auto_ext;
            clear H; rename H' into H)
    end.

(* Handle a VC for an indirect function call, given the callee's formal arguments list. *)
Ltac icall formals :=
  match goal with
    | [ H : context[locals ?ns ?vs ?avail ?p] |- exists pre', _ (Regs _ Rv) = Some pre' /\ _ ] =>
      let ns' := constr:("rp" :: formals) in
        let avail' := constr:0 in
          let offset := eval simpl in (4 * List.length ns) in
            change (locals ns vs avail p) with (locals_call ns vs avail p ns' avail' offset) in H;
              assert (ok_call ns ns' avail avail' offset)%nat
                by (split; [ simpl; omega
                  | split; [ simpl; omega
                    | split; [ repeat constructor; simpl; intuition congruence
                      | reflexivity ] ] ])
  end.
