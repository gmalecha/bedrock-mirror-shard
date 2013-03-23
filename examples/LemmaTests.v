Require Import Omega.

Require Import PreAutoSep.


(** Let's put the lemma prover through its paces. *)

Hint Extern 1 => elimtype False; omega : contradiction.

Ltac sep_canceller isConst ext simplifier :=
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
          ReifyExpr.collectTypes_exprs isConst pures Ts
           ltac:(fun Ts =>
                   SEP_REIFY.collectTypes_sexpr isConst L Ts
                    ltac:(fun Ts =>
                            SEP_REIFY.collectTypes_sexpr isConst R Ts
                             ltac:(fun Ts =>
                                     match Ts with
                                     | context [PropX] =>
                                         fail 1000
                                          "found PropX in types list"
                                          "(this causes universe inconsistencies)"
                                          Ts
                                     | context [PropX.spec] =>
                                         fail 1000
                                          "found PropX in types list"
                                          "(this causes universe inconsistencies)"
                                          Ts
                                     | _ => idtac
                                     end;
                                      (let types_ :=
                                        reduce_repr ext tt
                                         (TacPackIL.ILAlgoTypes.PACK.applyTypes
                                            (TacPackIL.ILAlgoTypes.Env ext)
                                            (@nil _)) in
                                       let types_ :=
                                        ReifyExpr.extend_all_types Ts types_ in
                                       let typesV := fresh "types" in
                                       pose (typesV := types_);
                                        (let uvars :=
                                          eval simpl in
                                          (@nil _:Expr.env typesV) in
                                         let gvars := uvars in
                                         let vars :=
                                          eval simpl in (@nil Expr.tvar) in
                                         let funcs :=
                                          reduce_repr ext tt
                                           (TacPackIL.ILAlgoTypes.PACK.applyFuncs
                                              (TacPackIL.ILAlgoTypes.Env ext)
                                              typesV 
                                              (@nil _)) in
                                         let pcT := constr:(Expr.tvType O) in
                                         let stT :=
                                          constr:(Expr.tvType (S O)) in
                                         let preds :=
                                          reduce_repr ext tt
                                           (TacPackIL.ILAlgoTypes.PACK.applyPreds
                                              (TacPackIL.ILAlgoTypes.Env ext)
                                              typesV 
                                              (@nil _)) in
                                         ReifyExpr.reify_exprs isConst pures
                                          typesV funcs uvars vars
                                          ltac:(fun uvars funcs pures =>
                                                  let proofs :=
                                                  ReifyExpr.props_proof
                                                  all_props in
                                                  SEP_REIFY.reify_sexpr
                                                  isConst L typesV funcs pcT
                                                  stT preds uvars vars
                                                  ltac:(
                                                  fun uvars funcs preds L =>
                                                  SEP_REIFY.reify_sexpr
                                                  isConst R typesV funcs pcT
                                                  stT preds uvars vars
                                                  ltac:(
                                                  fun uvars funcs preds R =>
                                                    idtac "HERE" ;
                                                  let funcsV := fresh "funcs" in
                                                  pose (funcsV := funcs);
                                                  (let predsV := fresh
                                                  "preds" in
                                                  pose (predsV := preds);
                                                  (apply
                                                  (@ApplyCancelSep typesV
                                                  funcsV predsV
                                                  (TacPackIL.ILAlgoTypes.Algos
                                                  ext typesV)
                                                  (@TacPackIL.ILAlgoTypes.Algos_correct
                                                  ext typesV funcsV predsV)
                                                  uvars pures L R);
                                                  [ solve
                                                  [ apply proofs ]
                                                  | 
                                                  compute; reflexivity
                                                  | idtac ]) ||
                                                  (idtac
                                                  "failed to apply, generalizing instead!";
                                                  (let algos :=
                                                  constr:
                                                  (TacPackIL.ILAlgoTypes.Algos
                                                  ext typesV) in
                                                  idtac "-";
                                                  (let algosC :=
                                                  constr:
                                                  (@TacPackIL.ILAlgoTypes.Algos_correct
                                                  ext typesV funcsV predsV) in
                                                  idtac "*"; 
                                                    pose algos ;
                                                      pose algosC ;
                                                        pose uvars ; 
                                                          pose L ;
                                                            pose R ; pose pures
                                                            
(* (first
                                                  [ 
                                                  generalize
                                                  (@ApplyCancelSep typesV
                                                  funcsV predsV algos algosC
                                                  uvars pures L R); idtac "p"
                                                  | 
                                                  generalize
                                                  (@ApplyCancelSep typesV
                                                  funcsV predsV algos algosC
                                                  uvars pures L); idtac "o"
                                                  | 
                                                  generalize
                                                  (@ApplyCancelSep typesV
                                                  funcsV predsV algos algosC
                                                  uvars pures); idtac "i"
                                                  | 
                                                  generalize
                                                  (@ApplyCancelSep typesV
                                                  funcsV predsV algos algosC
                                                  uvars); idtac "u"
                                                  | 
                                                  generalize
                                                  (@ApplyCancelSep typesV
                                                  funcsV predsV algos algosC);
                                                  pose uvars; idtac "y"
                                                  | 
                                                  generalize
                                                  (@ApplyCancelSep typesV
                                                  funcsV predsV); 
                                                  pose algosC; idtac "r"
                                                  | 
                                                  generalize
                                                  (@ApplyCancelSep typesV
                                                  funcsV); idtac "q" ])
*)
)));
                                                  (first
                                                  [ 
                                                  simplifier typesV funcsV
                                                  predsV tt
                                                  | 
                                                  fail 100000
                                                  "canceler: simplifier failed" ]);
                                                  try
                                                  clear typesV funcsV predsV)))))))))
    | |- ?G => idtac "no match" G
    end).

Theorem t0 : forall a b, a =*> b ===> a =*> b.
  intros. unfold Himp.
  sep_canceller ltac:isConst auto_ext ltac:(hints_ext_simplifier auto_ext).
  assert (Expr.AllProvable funcs l nil l0). compute. exact I.
  eapply (@ApplyCancelSep_with_eq2 types funcs preds a0 a1 l s s0 l0 H).
  
  Set Printing Implicit.
  compute. reflexivity.
  subst a0 l s s0 l0.
  unfold auto_ext, TacPackIL.ILAlgoTypes.Algos.
  simpl.
  unfold CancelTacIL.CANCEL_LOOP.cancel. unfold SH.hash.
  simpl. unfold CancelTacIL.CANCEL_LOOP.CANCEL_TAC.canceller.
  Print CancelTacIL.CANCEL_LOOP.CANCEL.sepCancel.
  hnf. unfold CancelTacIL.CANCEL_LOOP.cancelLoop.
  hnf. unfold CancelTacIL.CANCEL_LOOP.UNF_TAC.unfold.
  hnf. unfold TacPackIL.UNF.refineForward.
  hnf. unfold TacPackIL.UNF.forward.
  unfold TacPackIL.UNF.unfoldForward.
  unfold TacPackIL.UNF.find. 
  hnf. unfold SH.hash. 


  Require Import Evm_compute.
  compute.
  clear. subst a0 l s s0 l0.
  simpl. unfold CancelTacIL.CANCEL_LOOP.cancel.
  unfold SH.hash. simpl. compute.

  compute.
  evm.
  sepLemma.
Qed.

Theorem t1 : forall a b c d, a =*> b * c =*> d ===> c =*> d * a =*> b.
  sepLemma. 
Qed.

Theorem t2 : forall P : nat -> Prop, (Ex x, [| P x |]) ===> Ex x, [| P x |].
  sepLemma; eauto.
Qed.

Theorem t3 : forall ls : list nat, [| (length ls > 0)%nat |] ===> Ex x, Ex ls', [| ls = x :: ls' |].
  destruct ls; sepLemma.
Qed.

Theorem t4 : forall A (R : A -> A -> Prop),
  (Ex x, Ex y, Ex z, [| R x y /\ R y z |]) ===> (Ex y, ((Ex x, [| R x y |]) * (Ex z, [| R y z |]))).
  sepLemma.
  apply H.
  eassumption.
Qed.

(** Unification **)
Theorem t5 : forall p1 P2 V, exists p2, exists v, 
  (p1 =*> P2 * P2 =*> V) ===> (p1 =*> p2 * p2 =*> v).
  intros. do 2 eexists.
  sepLemma.
Qed.

Theorem t6 : forall p1 P2 V, exists p2, exists v,
  (P2 =*> V * p1 =*> P2) ===> (p1 =*> p2 * p2 =*> v).
  intros. do 2 eexists.
  sepLemma.
Qed.

Theorem t7 : forall p1 P2 V, exists p2, exists v, 
  (p1 =*> P2 * P2 =*> V) ===> (p2 =*> v * p1 =*> p2).
  intros. do 2 eexists.
  sepLemma.
Qed.

Theorem t8 : forall p1 P2 V, exists p2, exists v,
  (P2 =*> V * p1 =*> P2) ===> (p2 =*> v * p1 =*> p2).
  intros. do 2 eexists.
  sepLemma.
Qed.

Theorem t_err : forall a b c d, a =*> c * b =*> d ===> a =*> b * c =*> d.
  intros.
  progress sep_canceller ltac:ILTacCommon.isConst auto_ext ltac:(hints_ext_simplifier auto_ext).
  (progress sep_canceller ltac:ILTacCommon.isConst auto_ext ltac:(hints_ext_simplifier auto_ext); fail 3) || idtac.
Abort.
