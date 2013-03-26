Require Import Omega.

Require Import PreAutoSep.


(** Let's put the lemma prover through its paces. *)

Hint Extern 1 => elimtype False; omega : contradiction.

Theorem t0 : forall a b, a =*> b ===> a =*> b.
(*  intros.  ILTacCommon.change_to_himp. sep_canceller ltac:(fun x => false) auto_ext.  *)
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

(*
Ltac sep_canceller isConst ext :=
  try ILTacCommon.change_to_himp;
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
      | [ |- himp ?L ?R ] =>
          (let types :=
           ILTacCommon.reduce_repr ext tt
            (TacPackIL.ILAlgoTypes.PACK.applyTypes
               (TacPackIL.ILAlgoTypes.Env ext) nil) in
          let funcs :=
           ILTacCommon.reduce_repr ext tt
            (TacPackIL.ILAlgoTypes.PACK.applyFuncs
               (TacPackIL.ILAlgoTypes.Env ext) types
               (Env.repr (ILEnv.bedrock_funcs_r types) nil)) in
          let preds :=
           ILTacCommon.reduce_repr ext tt
            (TacPackIL.ILAlgoTypes.PACK.applyPreds
               (TacPackIL.ILAlgoTypes.Env ext) types nil) in
          let all_props :=
           ReifyExpr.collect_props
            ltac:(ILTacCommon.reflectable ltac:ILTacCommon.shouldReflect) in
          let pures := all_props in
          let L := eval unfold empB, injB, injBX, starB, exB, hvarB in L in
          let R := eval unfold empB, injB, injBX, starB, exB, hvarB in R in
          let k := (fun typesV funcsV uvars predsV L R pures proofs =>
            idtac typesV funcsV uvars predsV pures proofs ;
           (let funcs := eval cbv delta [funcsV] in funcsV in
            let preds := eval cbv delta [predsV] in predsV in
            let puresV := fresh "pures" in
            pose (puresV := pures) ;
              idtac "0" ;
            let puresPfV := fresh "pures_proof" in
            assert (Expr.AllProvable funcsV uvars nil puresV) 
             as puresPfV
             by (cbv beta iota zeta
                  delta [Expr.AllProvable Expr.AllProvable_gen Expr.Provable
                        puresV Expr.exprD nth_error funcsV value error
                        Expr.Range Expr.Domain Expr.Denotation
                        Expr.EqDec_tvar Expr.applyD equiv_dec Expr.tvar_rec
                        Expr.tvar_rect sumbool_rec sumbool_rect eq_nat_dec
                        nat_rec nat_rect eq_rec_r eq_rect eq_rec f_equal
                        eq_sym]; exact proofs);
             idtac "1" ;
             change (SEP.himp funcsV predsV uvars nil L R);
               idtac "2" ;
             apply (@ILTacCommon.ApplyCancelSep_slice typesV funcsV predsV 
          (TacPackIL.ILAlgoTypes.Algos ext typesV)
          (@TacPackIL.ILAlgoTypes.Algos_correct ext typesV funcsV predsV)
          uvars L R puresV puresPfV) ;
              idtac "3" ;
             (let bl :=
               constr:(Evm_compute.Bcons _ ex
                         (Evm_compute.Bcons _ emp
                         (Evm_compute.Bcons _ star
                               (Evm_compute.Bcons _ inj
                                  (Evm_compute.Bcons _ himp Evm_compute.Bnil))))) in
              let bl :=
               ILTacCommon.add_bl
                ltac:(fun x => eval red in (Expr.Denotation x)) funcs bl in
              let bl :=
               ILTacCommon.add_bl
                ltac:(fun x => eval red in (SEP.SDenotation x)) preds bl in
                idtac "4" ;
              subst funcsV predsV; 
                idtac "5" ; evm computed_blacklist [ bl ];
                idtac "6" ;
               clear typesV puresV puresPfV;
                 idtac "7" ;
               match goal with
               | |- ?G => idtac "8" ;
                     let H := fresh in
                       idtac "9" ;
                     (assert G as H; [ intros | idtac "10" ; exact H ]); idtac "11" 
               end))) in
          ((sep_canceler_plugin types funcs preds pures L R k) ||
            fail 10000 "sep_canceler_plugin failed"))
      | [ |- ?G ] => idtac "no match" G
    end).
*)

(*
Theorem t_err : forall a b c d, a =*> c * b =*> d ===> a =*> b * c =*> d.
  intros.
  progress sep_canceller ltac:ILTacCommon.isConst auto_ext.
  sep_canceller ltac:ILTacCommon.isConst auto_ext.
  (progress sep_canceller ltac:ILTacCommon.isConst auto_ext; fail 3) || idtac.
Abort.
*)