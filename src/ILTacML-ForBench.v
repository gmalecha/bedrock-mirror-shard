Require Import List.
Require Import EquivDec.
Require MirrorShard.ReifySepExpr.
Require Import SepIL.
Require Import TacPackIL.
Require Import IL ILEnv SymIL.
Require Import Word Memory.
Require Import Env.
Require PropX.
Require Import ILTacCommon.
Require Import Timing.

Set Implicit Arguments.
Set Strict Implicit.

Add ML Path "reification".
Declare ML Module "extlib".
Declare ML Module "reif".

Local Notation "a ::: b" := (@Evm_compute.Bcons _ a b) (at level 60, right associativity).

(** Cancellation **)
(******************)
Ltac sep_canceler bf bb isConst ext :=
  (try ILTacCommon.change_to_himp) ;
  let ext' :=
    match ext with
      | tt => eval cbv delta [ TacPackIL.ILAlgoTypes.BedrockPackage.bedrock_package ] in TacPackIL.ILAlgoTypes.BedrockPackage.bedrock_package
      | _ => ext
    end
  in
  start_timer "gather" ;
  match goal with
    | [ |- himp ?L ?R ] =>
      (
      let all_props := ReifyExpr.collect_props ltac:(ILTacCommon.reflectable ILTacCommon.shouldReflect) in
      let pures := all_props in

      let L := eval unfold empB, injB, injBX, starB, exB, hvarB in L in
      let R := eval unfold empB, injB, injBX, starB, exB, hvarB in R in
      stop_timer "gather" ;
      start_timer "seed" ;
      let types := ILTacCommon.reduce_repr ext' tt (TacPackIL.ILAlgoTypes.PACK.applyTypes (TacPackIL.ILAlgoTypes.Env ext') nil) in
      let funcs := ILTacCommon.reduce_repr ext' tt (TacPackIL.ILAlgoTypes.PACK.applyFuncs (TacPackIL.ILAlgoTypes.Env ext') types (Env.repr (ILEnv.bedrock_funcs_r types) nil)) in
      let preds := ILTacCommon.reduce_repr ext' tt (TacPackIL.ILAlgoTypes.PACK.applyPreds (TacPackIL.ILAlgoTypes.Env ext') types nil) in
      stop_timer "seed" ;
      let k := fun typesV funcsV uvars predsV L R pures proofs =>
        let puresV := fresh "pures" in
        pose (puresV := pures) ;
        stop_timer "reify" ;
        start_timer "proof" ;
        let puresPfV := fresh "pures_proof" in
        assert (puresPfV : Expr.AllProvable funcsV uvars nil puresV) by
          (cbv beta iota zeta delta
            [ Expr.AllProvable Expr.AllProvable_gen Expr.Provable puresV
              Expr.exprD nth_error funcsV value error
              Expr.Range Expr.Domain Expr.Denotation
              Expr.EqDec_tvar Expr.applyD equiv_dec
              Expr.tvar_rec Expr.tvar_rect sumbool_rec sumbool_rect
              Peano_dec.eq_nat_dec nat_rec nat_rect eq_rec_r eq_rect eq_rec
              f_equal eq_sym ]; exact proofs ) ;
        change (SEP.himp funcsV predsV uvars nil L R) ;
        apply (@CancelTacIL.ApplyCancelSep_slice bf bb typesV funcsV predsV
          (TacPackIL.ILAlgoTypes.Algos ext' typesV)
          (@TacPackIL.ILAlgoTypes.Algos_correct ext' typesV funcsV predsV)
          uvars L R puresV puresPfV);
        stop_timer "proof" ;
        (start_timer "compute" ;
         let funcs := eval cbv delta [ funcsV ] in funcsV in
         let preds := eval cbv delta [ predsV ] in predsV in
         let bl := constr:(not ::: ex ::: emp ::: star ::: inj ::: himp ::: Evm_compute.Bnil) in
         let bl := ILTacCommon.add_bl ltac:(fun x => eval red in (Expr.Denotation x)) funcs bl in
         let bl := ILTacCommon.add_bl ltac:(fun x => eval red in (SEP.SDenotation x)) preds bl in
         subst funcsV predsV  ;
         evm computed_blacklist [ bl ];
         clear typesV puresV puresPfV ;
         stop_timer "compute")
      in
      start_timer "reify" ;
      first [ sep_canceler_plugin types funcs preds pures L R k
            | fail 10000 "sep_canceler_plugin failed" ]) (** this just prevents backtracking **)
    | [ |- ?G ] =>
      idtac "no match" G
  end
(*TIME ) *).

(** Symbolic Execution **)
(************************)
Ltac sym_eval bf isConst ext :=
  start_timer "sym_eval" ;
  let rec init_from st :=
    match goal with
      | [ H : evalInstrs _ ?st' _ = Some st |- _ ] => init_from st'
      | [ |- _ ] => st
    end
  in
  let cs :=
    match goal with
      | [ H : PropX.codeSpec _ _ |- _ ] => H
    end
  in
  let rec clear_instrs pf :=
    match pf with
      | conj ?X ?pf => clear X ; clear_instrs pf
      | _ => idtac
    end
  in
    let finish H  :=
        first
          [ exact H
          | let rec destruct_exs H :=
              match type of H with
                | Logic.ex _ =>
                  destruct H as [ ? H ] ; destruct_exs H
                | forall x : ?T, _ =>
                  let n := fresh in
                  evar (n : T);
                  let e := eval cbv delta [ n ] in n in
                  specialize (H e)
                | (_ /\ (_ /\ _)) /\ (_ /\ _) =>
                  destruct H as [ [ ? [ ? ? ] ] [ ? ? ] ];
                  repeat match goal with
                           | [ H' : _ /\ _ |- _ ] => destruct H'
                         end
                | ((_ /\ (_ /\ _)) /\ (_ /\ _)) /\ _  =>
                  destruct H as [ [ [ ? [ ? ? ] ] [ ? ? ] ] ? ];
                  repeat match goal with
                           | [ H' : _ /\ _ |- _ ] => destruct H'
                         end
                | False => destruct H
                | ?G =>
                  fail 100000 "bad result goal" G
              end
            in destruct_exs H ]
    in

  let ext' :=
    match ext with
      | tt => eval cbv delta [ TacPackIL.ILAlgoTypes.BedrockPackage.bedrock_package ] in TacPackIL.ILAlgoTypes.BedrockPackage.bedrock_package
      | _ => ext
    end
  in
  let stn_st_SF :=
    match goal with
      | [ H : PropX.interp _ (![ ?SF ] ?X) |- _ ] =>
        let SF := eval unfold empB, injB, injBX, starB, exB, hvarB in SF in
        constr:((X, (SF, H)))
      | [ H : Structured.evalCond _ _ _ ?stn ?st = _ |- _ ] =>
        let st := init_from st in
        constr:(((stn, st), tt))
      | [ H : IL.evalInstrs ?stn ?st _ = _ |- _ ] =>
        let st := init_from st in
        constr:(((stn, st), tt))
      | [ |- _ ] => tt
    end
  in
  let types := ILTacCommon.reduce_repr ext tt (TacPackIL.ILAlgoTypes.PACK.applyTypes (TacPackIL.ILAlgoTypes.Env ext') nil) in
  let funcs := ILTacCommon.reduce_repr ext tt (TacPackIL.ILAlgoTypes.PACK.applyFuncs (TacPackIL.ILAlgoTypes.Env ext') types (repr (bedrock_funcs_r types) nil)) in
  let preds := ILTacCommon.reduce_repr ext tt (TacPackIL.ILAlgoTypes.PACK.applyPreds (TacPackIL.ILAlgoTypes.Env ext') types nil) in
  let all_props := ReifyExpr.collect_props ltac:(ILTacCommon.reflectable shouldReflect) in
  let pures := all_props in
  match stn_st_SF with
    | tt => idtac (* nothing to symbolically evluate *)
    | ((?stn, ?st), tt) =>
      match find_reg st Rp with
        | (?rp_v, ?rp_pf) =>
          match find_reg st Sp with
            | (?sp_v, ?sp_pf) =>
              match find_reg st Rv with
                | (?rv_v, ?rv_pf) =>
                    let k := (fun typesV funcsV uvars predsV rp sp rv is isP fin pures proofs =>
                      first [
                          (let uvarsV := fresh "uvars" in
                           pose (uvarsV := uvars) ;
                           let isV := fresh "path" in
                           pose (isV := is) ;
                           let isD := fresh "pathPf" in
                           assert (isD : @SymIL.istreamD typesV (Env.repr (ILEnv.bedrock_funcs_r typesV) funcsV)
                             uvarsV nil isV stn st fin) by (exact isP) ;
                           let puresV := fresh "pures" in
                           pose (puresV := pures) ;
                           let puresPf := fresh "puresPf" in
                           assert (puresPf : @Expr.AllProvable typesV (Env.repr (ILEnv.bedrock_funcs_r typesV) funcsV) uvars nil puresV) by (exact proofs) ;
                           let new := fresh "after" in
                           evar (new : Prop) ;
                           let g := eval cbv delta [ new ] in new in
                           let result := fresh "result" in
                           assert (result : g) by
                             (generalize (@SymILTac.ApplySymEval_slice_no_heap bf typesV funcsV predsV
                                 (@TacPackIL.ILAlgoTypes.Algos ext' typesV)
                                 (@TacPackIL.ILAlgoTypes.Algos_correct ext' typesV funcsV predsV)
                                 stn uvarsV fin st isV isD cs sp rv rp puresV
                                 sp_pf rv_pf rp_pf puresPf) ;
                                let bl := constr:(evalInstrs ::: Structured.evalCond ::: not ::: Regs ::: ex ::: emp ::: star ::: inj ::: Evm_compute.Bnil) in
                                let funcs := eval cbv delta [ funcsV ] in funcsV in
                                let bl := add_bl ltac:(fun x => eval red in (Expr.Denotation x)) funcs bl in
                                let preds := eval cbv delta [ predsV ] in predsV in
                                let bl := add_bl ltac:(fun x => eval red in (SEP.SDenotation x)) preds bl in
                                subst funcsV predsV ;
                                evm computed_blacklist [ bl ] ;
                                refine (fun x => x)) ;
                             clear new puresPf puresV isD isV uvarsV predsV funcsV typesV ;
                             clear_instrs isP ;
                             finish result) | fail 10000 "symbolic evaluation failed (no heap)" ])
                    in
                    first [ (sym_eval_nosep all types funcs preds pures rp_v sp_v rv_v st k)
                          | fail 10000 "sym_eval_nosep failed" ]
              end
          end
      end
    | ((?stn, ?st), (?SF, ?H_interp)) =>
        match find_reg st Rp with
          | (?rp_v, ?rp_pf) =>
              match find_reg st Sp with
                | (?sp_v, ?sp_pf) =>
                    match find_reg st Rv with
                      | (?rv_v, ?rv_pf) =>
                        let k := (fun typesV funcsV uvars predsV rp sp rv is isP fin pures proofs SF =>
                          first [
                          (  let uvarsV := fresh "uvars" in
                             pose (uvarsV := uvars) ;
                             let isV := fresh "path" in
                             pose (isV := is) ;
                             let isD := fresh "pathPf" in
                             assert (isD : @SymIL.istreamD typesV (Env.repr (ILEnv.bedrock_funcs_r typesV) funcsV)
                              uvarsV nil isV stn st fin) by (exact isP) ;
                             let puresV := fresh "pures" in
                             pose (puresV := pures) ;
                             let puresPf := fresh "puresPf" in
                             assert (puresPf : @Expr.AllProvable typesV (Env.repr (ILEnv.bedrock_funcs_r typesV) funcsV) uvars nil puresV) by (exact proofs) ;
                             let new := fresh "after" in
                             evar (new : Prop) ;
                             let g := eval cbv delta [ new ] in new in
                             let result := fresh "result" in
                             assert (result : g) by
                               (generalize (@SymILTac.ApplySymEval_slice_heap bf typesV funcsV predsV
                                 (@TacPackIL.ILAlgoTypes.Algos ext' typesV)
                                 (@TacPackIL.ILAlgoTypes.Algos_correct ext' typesV funcsV predsV)
                                 stn uvarsV fin st isV isD cs sp rv rp puresV SF
                                 sp_pf rv_pf rp_pf puresPf H_interp) ;
                                let bl := constr:(evalInstrs ::: Structured.evalCond ::: not ::: Regs ::: PropX.interp ::: ex ::: emp ::: star ::: inj ::: Evm_compute.Bnil) in
                                let funcs := eval cbv delta [ funcsV ] in funcsV in
                                let bl := add_bl ltac:(fun x => eval red in (Expr.Denotation x)) funcs bl in
                                let preds := eval cbv delta [ predsV ] in predsV in
                                let bl := add_bl ltac:(fun x => eval red in (SEP.SDenotation x)) preds bl in
                                subst funcsV predsV ;
                                evm computed_blacklist [ bl ] ;
                                refine (fun x => x)) ;
                             clear new H_interp puresPf puresV isD isV uvarsV predsV funcsV typesV ;
                             clear_instrs isP ;
                             finish result) | fail 10000 "symbolic evaluation failed (with heap)" ])
                        in
                        first [ (sym_eval_sep all types funcs preds pures rp_v sp_v rv_v st SF k)
                              | fail 10000  "sym_eval_sep failed" ]
                    end
              end
        end
    | ?X => idtac "Called sym_eval on bad goal" X ; fail 100000 "bad"
  end ;
  stop_timer "sym_eval".

(** 1-shot symbolic evaluation **)
Ltac sym_eval_one bf isConst ext :=
  start_timer "sym_eval_one" ;
  let rec init_from st :=
    match goal with
      | [ H : evalInstrs _ ?st' _ = Some st |- _ ] => init_from st'
      | [ |- _ ] => st
    end
  in
  let cs :=
    match goal with
      | [ H : PropX.codeSpec _ _ |- _ ] => H
    end
  in
  let rec clear_instrs pf :=
    match pf with
      | conj ?X ?pf => clear X ; clear_instrs pf
      | _ => idtac
    end
  in
    let finish H  :=
        first
          [ exact H
          | let rec destruct_exs H :=
              match type of H with
                | Logic.ex _ =>
                  destruct H as [ ? H ] ; destruct_exs H
                | forall x : ?T, _ =>
                  let n := fresh in
                  evar (n : T);
                  let e := eval cbv delta [ n ] in n in
                  specialize (H e)
                | (_ /\ (_ /\ _)) /\ (_ /\ _) =>
                  destruct H as [ [ ? [ ? ? ] ] [ ? ? ] ];
                  repeat match goal with
                           | [ H' : _ /\ _ |- _ ] => destruct H'
                         end
                | ((_ /\ (_ /\ _)) /\ (_ /\ _)) /\ _  =>
                  destruct H as [ [ [ ? [ ? ? ] ] [ ? ? ] ] ? ];
                  repeat match goal with
                           | [ H' : _ /\ _ |- _ ] => destruct H'
                         end
                | False => destruct H
                | ?G =>
                  fail 100000 "bad result goal" G
              end
            in destruct_exs H ]
    in
  let ext' :=
    match ext with
      | tt => eval cbv delta [ TacPackIL.ILAlgoTypes.BedrockPackage.bedrock_package ] in TacPackIL.ILAlgoTypes.BedrockPackage.bedrock_package
      | _ => ext
    end
  in
  let stn_st_SF :=
    match goal with
      | [ H : PropX.interp _ (![ ?SF ] ?X) |- _ ] =>
        let SF := eval unfold empB, injB, injBX, starB, exB, hvarB in SF in
        constr:((X, (SF, H)))
      | [ H : Structured.evalCond _ _ _ ?stn ?st = _ |- _ ] =>
        let st := init_from st in
        constr:(((stn, st), tt))
      | [ H : IL.evalInstrs ?stn ?st _ = _ |- _ ] =>
        let st := init_from st in
        constr:(((stn, st), tt))
      | [ |- _ ] => tt
    end
  in
  let types := ILTacCommon.reduce_repr ext tt (TacPackIL.ILAlgoTypes.PACK.applyTypes (TacPackIL.ILAlgoTypes.Env ext') nil) in
  let funcs := ILTacCommon.reduce_repr ext tt (TacPackIL.ILAlgoTypes.PACK.applyFuncs (TacPackIL.ILAlgoTypes.Env ext') types (repr (bedrock_funcs_r types) nil)) in
  let preds := ILTacCommon.reduce_repr ext tt (TacPackIL.ILAlgoTypes.PACK.applyPreds (TacPackIL.ILAlgoTypes.Env ext') types nil) in
  let all_props := ReifyExpr.collect_props ltac:(ILTacCommon.reflectable shouldReflect) in
  let pures := all_props in
  match stn_st_SF with
    | tt => idtac (* nothing to symbolically evluate *)
    | ((?stn, ?st), tt) =>
      match find_reg st Rp with
        | (?rp_v, ?rp_pf) =>
          match find_reg st Sp with
            | (?sp_v, ?sp_pf) =>
              match find_reg st Rv with
                | (?rv_v, ?rv_pf) =>
                    let k := (fun typesV funcsV uvars predsV rp sp rv is isP fin pures proofs =>
                      first [
                          (let uvarsV := fresh "uvars" in
                           pose (uvarsV := uvars) ;
                           let isV := fresh "path" in
                           pose (isV := is) ;
                           let isD := fresh "pathPf" in
                           assert (isD : @SymIL.istreamD typesV (Env.repr (ILEnv.bedrock_funcs_r typesV) funcsV)
                             uvarsV nil isV stn st fin) by (exact isP) ;
                           let puresV := fresh "pures" in
                           pose (puresV := pures) ;
                           let puresPf := fresh "puresPf" in
                           assert (puresPf : @Expr.AllProvable typesV (Env.repr (ILEnv.bedrock_funcs_r typesV) funcsV) uvars nil puresV) by (exact proofs) ;
                           let new := fresh "after" in
                           evar (new : Prop) ;
                           let g := eval cbv delta [ new ] in new in
                           let result := fresh "result" in
                           assert (result : g) by
                             (generalize (@SymILTac.ApplySymEval_slice_no_heap bf typesV funcsV predsV
                                 (@TacPackIL.ILAlgoTypes.Algos ext' typesV)
                                 (@TacPackIL.ILAlgoTypes.Algos_correct ext' typesV funcsV predsV)
                                 stn uvarsV fin st isV isD cs sp rv rp puresV
                                 sp_pf rv_pf rp_pf puresPf) ;
                                let bl := constr:(evalInstrs ::: Structured.evalCond ::: not ::: Regs ::: ex ::: emp ::: star ::: inj ::: Evm_compute.Bnil) in
                                let funcs := eval cbv delta [ funcsV ] in funcsV in
                                let bl := add_bl ltac:(fun x => eval red in (Expr.Denotation x)) funcs bl in
                                let preds := eval cbv delta [ predsV ] in predsV in
                                let bl := add_bl ltac:(fun x => eval red in (SEP.SDenotation x)) preds bl in
                                subst funcsV predsV ;
                                evm computed_blacklist [ bl ] ;
                                refine (fun x => x)) ;
                             clear new puresPf puresV isD isV uvarsV predsV funcsV typesV ;
                             clear_instrs isP ;
                             finish result) | fail 10000 "symbolic evaluation failed (no heap)" ])
                    in
                    first [ (sym_eval_nosep one types funcs preds pures rp_v sp_v rv_v st k)
                          | fail 10000 "sym_eval_nosep failed" ]
              end
          end
      end
    | ((?stn, ?st), (?SF, ?H_interp)) =>
        match find_reg st Rp with
          | (?rp_v, ?rp_pf) =>
              match find_reg st Sp with
                | (?sp_v, ?sp_pf) =>
                    match find_reg st Rv with
                      | (?rv_v, ?rv_pf) =>
                        let k := (fun typesV funcsV uvars predsV rp sp rv is isP fin pures proofs SF =>
                          first [
                          (  let uvarsV := fresh "uvars" in
                             pose (uvarsV := uvars) ;
                             let isV := fresh "path" in
                             pose (isV := is) ;
                             let isD := fresh "pathPf" in
                             assert (isD : @SymIL.istreamD typesV (Env.repr (ILEnv.bedrock_funcs_r typesV) funcsV)
                              uvarsV nil isV stn st fin) by (exact isP) ;
                             let puresV := fresh "pures" in
                             pose (puresV := pures) ;
                             let puresPf := fresh "puresPf" in
                             assert (puresPf : @Expr.AllProvable typesV (Env.repr (ILEnv.bedrock_funcs_r typesV) funcsV) uvars nil puresV) by (exact proofs) ;
                             let new := fresh "after" in
                             evar (new : Prop) ;
                             let g := eval cbv delta [ new ] in new in
                             let result := fresh "result" in
                             assert (result : g) by
                               (generalize (@SymILTac.ApplySymEval_slice_heap bf typesV funcsV predsV
                                 (@TacPackIL.ILAlgoTypes.Algos ext' typesV)
                                 (@TacPackIL.ILAlgoTypes.Algos_correct ext' typesV funcsV predsV)
                                 stn uvarsV fin st isV isD cs sp rv rp puresV SF
                                 sp_pf rv_pf rp_pf puresPf H_interp) ;
                                let bl := constr:(evalInstrs ::: Structured.evalCond ::: not ::: Regs ::: PropX.interp ::: ex ::: emp ::: star ::: inj ::: Evm_compute.Bnil) in
                                let funcs := eval cbv delta [ funcsV ] in funcsV in
                                let bl := add_bl ltac:(fun x => eval red in (Expr.Denotation x)) funcs bl in
                                let preds := eval cbv delta [ predsV ] in predsV in
                                let bl := add_bl ltac:(fun x => eval red in (SEP.SDenotation x)) preds bl in
                                subst funcsV predsV ;
                                evm computed_blacklist [ bl ] ;
                                refine (fun x => x)) ;
                             clear new H_interp puresPf puresV isD isV uvarsV predsV funcsV typesV ;
                             clear_instrs isP ;
                             finish result) | fail 10000 "symbolic evaluation failed (with heap)" ])
                        in
                        first [ (sym_eval_sep one types funcs preds pures rp_v sp_v rv_v st SF k)
                              | fail 10000  "sym_eval_sep failed" ]
                    end
              end
        end
    | ?X => idtac "Called sym_eval on bad goal" X ; fail 100000 "bad"
  end ;
  stop_timer "sym_eval1".
