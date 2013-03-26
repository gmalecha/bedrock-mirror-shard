Require Import List.

Require ReifySepExpr.
Require Import ILTacCommon.
Require Import SepIL.
Require Import TacPackIL.
Require Import IL ILEnv SymIL.
Require Import Word Memory.
Require Import Env.

Export ILTacCommon.
Require Import Evm_compute.

Set Implicit Arguments.
Set Strict Implicit.

Local Notation "a ::: b" := (@Evm_compute.Bcons _ a b) (at level 60, right associativity).

Module SEP_REIFY := ReifySepExpr.ReifySepExpr ST SEP.

(** Cancellation **)
(******************)
(** The parameters are the following.
 ** - [isConst] is an ltac [* -> bool]
 ** - [ext] is a [TypedPackage .. .. .. .. ..]
 **)
Ltac sep_canceller isConst ext :=
  try change_to_himp;
  (let ext' :=
    (match ext with
       | tt =>
         eval
         cbv delta [TacPackIL.ILAlgoTypes.BedrockPackage.bedrock_package] in
           TacPackIL.ILAlgoTypes.BedrockPackage.bedrock_package
       | _ => eval cbv delta [ext] in ext
       | _ => ext
     end) in
    match goal with
      | |- himp ?L ?R =>
          let pcT := constr:W in
          let stateT := constr:(prod settings state) in
          let all_props :=
           ReifyExpr.collect_props ltac:(reflectable ltac:shouldReflect) in
          let pures := ReifyExpr.props_types all_props in
          let L := eval unfold empB, injB, injBX, starB, exB, hvarB in L in
          let R := eval unfold empB, injB, injBX, starB, exB, hvarB in R in
          let Ts := constr:Reify.Tnil in
          ReifyExpr.collectTypes_exprs isConst pures Ts ltac:(fun Ts =>
            SEP_REIFY.collectTypes_sexpr isConst L Ts ltac:(fun Ts =>
              SEP_REIFY.collectTypes_sexpr isConst R Ts ltac:(fun Ts =>
                match Ts with
                  | context [PropX.PropX] =>
                    fail 1000 "found PropX in types list"
                              "(this causes universe inconsistencies)" Ts
                  | context [PropX.spec] =>
                    fail 1000 "found PropX in types list"
                              "(this causes universe inconsistencies)" Ts
                  | _ => idtac
                end;
                let types_ :=
                  reduce_repr ext tt
                  (TacPackIL.ILAlgoTypes.PACK.applyTypes
                    (TacPackIL.ILAlgoTypes.Env ext)
                    (@nil _)) in
                let types_ := ReifyExpr.extend_all_types Ts types_ in
                let typesV := fresh "types" in
                pose (typesV := types_);
                let uvars := constr:(@nil (sigT (Expr.tvarD typesV))) in
                let gvars := uvars in
                let vars  := constr:(@nil Expr.tvar) in
                let funcs :=
                  reduce_repr ext tt
                  (TacPackIL.ILAlgoTypes.PACK.applyFuncs
                    (TacPackIL.ILAlgoTypes.Env ext)
                    typesV 
                    (@nil _)) in
                let pcT := constr:(Expr.tvType O) in
                let stT := constr:(Expr.tvType (S O)) in
                let preds :=
                  reduce_repr ext tt
                  (TacPackIL.ILAlgoTypes.PACK.applyPreds
                    (TacPackIL.ILAlgoTypes.Env ext)
                    typesV 
                    (@nil _)) in
                ReifyExpr.reify_exprs isConst pures typesV funcs uvars vars ltac:(fun uvars funcs pures =>
                  let proofs := ReifyExpr.props_proof all_props in
                  SEP_REIFY.reify_sexpr isConst L typesV funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds L =>
                    SEP_REIFY.reify_sexpr isConst R typesV funcs pcT stT preds uvars vars ltac:(fun uvars funcs preds R =>
                      let funcsV := fresh "funcs" in
                      pose (funcsV := funcs);
                      let predsV := fresh "preds" in
                      pose (predsV := preds);
                      let puresV := fresh "pures" in
                      pose (puresV := pures) ;
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
                      apply (@ApplyCancelSep_slice typesV funcsV predsV 
                        (TacPackIL.ILAlgoTypes.Algos ext typesV)
                        (@TacPackIL.ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                        uvars L R puresV puresPfV); 
                      (let bl := constr:(ex ::: emp ::: star ::: inj ::: himp ::: Evm_compute.Bnil) in
                       let bl := add_bl ltac:(fun x => eval red in (Expr.Denotation x)) funcs bl in
                       let bl := add_bl ltac:(fun x => eval red in (SEP.SDenotation x)) preds bl in
                       subst funcsV predsV  ;
                       evm computed_blacklist [ bl ];
                       clear typesV puresV puresPfV ;
                       match goal with
                         | |- ?G => let H := fresh in assert (H : G); [ intros | apply H ]
                       end)))))))
      | |- ?G => idtac "no match" G
    end).


(** Symbolic Execution **)
(************************)
(** NOTE:
 ** - [isConst] is an ltac function of type [* -> bool]
 ** - [ext] is the extension. it is a value of type [TypedPackage]
 ** - [simplifier] is an ltac that takes a hypothesis names and simplifies it
 **     (this should be implmented using [cbv beta iota zeta delta [ ... ] in H])
 **     (it is recommended/necessary to call [sym_evaluator] or import its simplification)
 **)
Ltac sym_eval isConst ext simplifier :=
(*TIME  start_timer "sym_eval:init" ; *)
  let rec init_from st :=
    match goal with
      | [ H : evalInstrs _ ?st' _ = Some st |- _ ] => init_from st'
      | [ |- _ ] => st
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
  let cs :=
    match goal with
      | [ H : PropX.codeSpec _ _ |- _ ] => H
    end
  in
  let ext' := 
    match ext with
      | _ => eval cbv delta [ ext ] in ext
      | _ => ext
    end
  in
  match stn_st_SF with
    | tt => idtac (* nothing to symbolically evluate *)
    | ((?stn, ?st), ?SF) =>
      match find_reg st Rp with
        | (?rp_v, ?rp_pf) =>
          match find_reg st Sp with
            | (?sp_v, ?sp_pf) =>
              match find_reg st Rv with
                | (?rv_v, ?rv_pf) =>
(*TIME                  stop_timer "sym_eval:init" ; *)
(*TIME                  start_timer "sym_eval:gather_instrs" ; *)
                  let all_instrs := get_instrs st in
                  let all_props := 
                    ReifyExpr.collect_props ltac:(ILTacCommon.reflectable shouldReflect)
                  in
                  let pures := ReifyExpr.props_types all_props in
                  let regs := constr:((rp_v, (sp_v, (rv_v, tt)))) in
(*TIME                  stop_timer "sym_eval:gather_instrs" ; *)
                  (** collect the raw types **)
(*TIME                  start_timer "sym_eval:reify" ; *)
                  let Ts := constr:(Reify.Tnil) in
                  let Ts k := 
                    match SF with
                      | tt => k Ts
                      | (?SF,_) => (** TODO: a little sketchy since it is in CPS **)
                        SEP_REIFY.collectTypes_sexpr ltac:(isConst) SF Ts k 
                    end
                  in
                    Ts ltac:(fun Ts => 
                  collectAllTypes_instrs all_instrs Ts ltac:(fun Ts => 
                  ReifyExpr.collectTypes_exprs ltac:(isConst) regs Ts ltac:(fun Ts => 
                  ReifyExpr.collectTypes_exprs ltac:(isConst) pures Ts ltac:(fun Ts => 
                  (** check for potential universe problems **)
                  match Ts with
                    | context [ PropX.PropX ] => 
                      fail 1000 "found PropX in types list"
                        "(this causes universe inconsistencies)" Ts
                    | context [ PropX.spec ] => 
                      fail 1000 "found PropX.spec in types list"
                        "(this causes universe inconsistencies)" Ts
                    | _ => idtac
                  end;
                  (** elaborate the types **)
                  let types_ := reduce_repr ext tt (ILAlgoTypes.PACK.applyTypes (TacPackIL.ILAlgoTypes.Env ext) nil) in
                  let types_ := ReifyExpr.extend_all_types Ts types_ in
                  let typesV := fresh "types" in
                  pose (typesV := types_);
                  (** Check the types **)
                  let pcT := constr:(Expr.tvType 0) in
                  let stT := constr:(Expr.tvType 1) in
                  (** build the variables **)
                  let uvars := constr:(@nil (@sigT Expr.tvar (fun t : Expr.tvar => Expr.tvarD typesV t))) in
                  let vars := uvars in
                  (** build the base functions **)
                  let funcs := reduce_repr ext tt (ILAlgoTypes.PACK.applyFuncs (TacPackIL.ILAlgoTypes.Env ext) typesV (repr (bedrock_funcs_r typesV) nil)) in
                   (** build the base sfunctions **)
(*                  let preds := constr:(@nil (@SEP.ssignature typesV pcT stT)) in *)
                  let preds := reduce_repr ext tt (ILAlgoTypes.PACK.applyPreds (TacPackIL.ILAlgoTypes.Env ext) typesV nil) in
                  (** reflect the expressions **)
                  ReifyExpr.reify_exprs ltac:(isConst) pures typesV funcs uvars vars ltac:(fun uvars funcs pures =>
                  let proofs := ReifyExpr.props_proof all_props in
                  
                  ReifyExpr.reify_expr ltac:(isConst) rp_v typesV funcs uvars vars ltac:(fun uvars funcs rp_v  => 
                  ReifyExpr.reify_expr ltac:(isConst) sp_v typesV funcs uvars vars ltac:(fun uvars funcs sp_v =>  

                  ReifyExpr.reify_expr ltac:(isConst) rv_v typesV funcs uvars vars ltac:(fun uvars funcs rv_v => 
                    let finish H  :=
(*TIME                      start_timer "sym_eval:cleanup" ; *)
                      ((try exact H) ||
                       (let rec destruct_exs H :=
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
                           | False => destruct H
                           | ?G =>
                             fail 100000 "bad result goal" G
                         end
                        in let fresh Hcopy := fresh "Hcopy" in
                          let T := type of H in
                            assert (Hcopy : T) by apply H; clear H; destruct_exs Hcopy))
(*TIME                    ;  stop_timer "sym_eval:cleanup" *)
                    in
                    build_path typesV all_instrs st uvars vars funcs ltac:(fun uvars funcs is fin_state is_pf => 
                      match SF with
                        | tt => 
(*TIME                          stop_timer "sym_eval:reify" ; *)
                          let funcsV := fresh "funcs" in
                          pose (funcsV := funcs) ;
                          let predsV := fresh "preds" in
                          pose (predsV := preds) ;
(*                          let ExtC := constr:(@Algos_correct _ _ _ _ _ _ ext typesV funcsV predsV) in *)
                          generalize (@SymILTac.stateD_proof_no_heap typesV funcsV predsV
                            uvars st sp_v rv_v rp_v 
                            sp_pf rv_pf rp_pf pures proofs cs stn) ;
                          let H_stateD := fresh in
                          intro H_stateD ;
                          ((apply (@SymILTac.Apply_sym_eval typesV funcsV predsV
                            (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                            stn uvars fin_state st is is_pf) in H_stateD)
                          || fail 100000 "couldn't apply sym_eval_any! (non-SF case)"); 
                          first [ simplifier typesV funcsV predsV H_stateD | fail 100000 "simplifier failed! (non-SF)" ] ;
                          try clear typesV funcsV predsV ;
                          first [ finish H_stateD (*; clear_instrs all_instrs*) | fail 100000 "finisher failed! (non-SF)" ]
                        | (?SF, ?H_interp) =>
                          SEP_REIFY.reify_sexpr ltac:(isConst) SF typesV funcs pcT stT preds uvars vars 
                          ltac:(fun uvars funcs preds SF =>
(*TIME                            stop_timer "sym_eval:reify" ; *)
(*TIME                            start_timer "sym_eval:pose" ; *)
                            let funcsV := fresh "funcs" in
                            pose (funcsV := funcs) ;
                            let predsV := fresh "preds" in
                            pose (predsV := preds) ;
(*                            let ExtC := constr:(@Algos_correct ext typesV funcsV predsV) in *)
(*TIME                            stop_timer "sym_eval:pose" ; *)
(*TIME                            start_timer "sym_eval:apply_stateD_proof" ; *)
                            apply (@SymILTac.stateD_proof typesV funcsV predsV
                              uvars _ sp_v rv_v rp_v 
                              sp_pf rv_pf rp_pf pures proofs SF _ _ (refl_equal _)) in H_interp ;
(*TIME                            stop_timer "sym_eval:apply_stateD_proof" ; *)
(*TIME                            start_timer "sym_eval:apply_sym_eval" ; *)
                            ((apply (@SymILTac.Apply_sym_eval typesV funcsV predsV
                              (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                              stn uvars fin_state st is is_pf) in H_interp) ||
                             (idtac "couldn't apply sym_eval_any! (SF case)"; 
                               first [ 
                                 generalize (@SymILTac.Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                                   stn uvars fin_state st is is_pf) ; idtac "6" 
                               | generalize (@SymILTac.Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                                   stn uvars fin_state st) ; idtac "5"  
                               | generalize (@SymILTac.Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
                                   stn uvars) ; idtac "4" 
                               | generalize (@SymILTac.Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV) (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV)); idtac "3" 
                               | generalize (@SymILTac.Apply_sym_eval typesV funcsV predsV
                                   (@ILAlgoTypes.Algos ext typesV)) ; generalize (@ILAlgoTypes.Algos_correct ext typesV funcsV predsV) ; idtac "2" 
                               | generalize (@SymILTac.Apply_sym_eval typesV funcsV predsV) ; idtac "1"  
                               ])) ;
(*TIME                             stop_timer "sym_eval:apply_sym_eval" ; *)
(*TIME                             start_timer "sym_eval:simplify" ; *)
                            first [ simplifier typesV funcsV predsV H_interp | fail 100000 "simplifier failed! (SF)" ] ;
(*TIME                             stop_timer "sym_eval:simplify" ; *)
(*TIME                             start_timer "sym_eval:clear" ; *)
                            try clear typesV funcsV predsV ;
(*TIME                             stop_timer "sym_eval:clear" ; *)
                            first [ finish H_interp ; clear_instrs all_instrs | fail 100000 "finisher failed! (SF)" ])
                      end)))))  ))))
              end
          end
      end
  end.