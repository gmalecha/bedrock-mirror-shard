Require Import RelationClasses.
Require Import Heaps.
Require Import PropX PropXTac.
Require Import MirrorShard.SepTheory.
Require Import MirrorShard.Heaps.
Require IL.

Set Implicit Arguments.
Set Strict Implicit.

Module Type PcSt.
  Parameter pcType : Type.
  Parameter stateType : Type.
End PcSt.

(** We make this transparent, so that clients can get at 
 ** [ihprop] and it associated lemmas
 **)
Module SepTheoryPropX_Kernel (SM : SeparationMemory) (PC_ST : PcSt) <: 
  SepTheory_Kernel 
  with Definition hprop := 
         IL.settings -> SM.smem -> PropX PC_ST.pcType PC_ST.stateType
  with Definition himp := 
         fun (gl gr : IL.settings -> SM.smem -> PropX PC_ST.pcType PC_ST.stateType) =>
           forall cs stn m, interp cs (gl stn m ---> gr stn m).

  Import PC_ST.

  Definition ihprop (sos : list Type) : Type :=
    IL.settings -> SM.smem -> propX PC_ST.pcType PC_ST.stateType sos.

  Definition hprop : Type := ihprop nil.

  Definition himp : ihprop nil -> ihprop nil -> Prop := 
    fun gl gr =>
      forall cs stn m, interp cs (gl stn m ---> gr stn m).

  Global Instance Refl_himp : Reflexive himp.
  Proof.
    red; unfold himp; intros. 
    eapply Imply_I; eauto.
  Qed.
  Global Instance Trans_himp : Transitive himp.
  Proof.
    red; unfold himp; firstorder.
    eapply Imply_I. eapply Imply_E. eapply valid_weaken. eapply H0. firstorder.
    eapply Imply_E. eapply valid_weaken. eapply H. firstorder. eauto.
  Qed.

  Section with_sos.
    Variable sos : list Type.

    (* Definitions *)
    Definition iinjX (p : propX pcType stateType sos) : ihprop sos :=
      fun _ m => PropX.And p (PropX.Inj (m = SM.smem_emp)).

    Definition iinj (p : Prop) : ihprop sos := iinjX (PropX.Inj p).

    Definition iemp : ihprop sos := iinj True.

    Definition istar (l r : ihprop sos) : ihprop sos :=
      fun s m => PropX.Exists (fun ml : SM.smem => PropX.Exists (fun mr : SM.smem =>
        PropX.And (PropX.Inj (SM.split m ml mr)) (And (l s ml) (r s mr)))).

    Definition iex (T : Type) (p : T -> ihprop sos) : ihprop sos :=
      fun s h => PropX.Exists (fun t => p t s h).

    Definition ihptsto (p : SM.M.addr) (v : SM.M.value) : ihprop sos :=
      fun s h =>
        PropX.Inj (SM.smem_get p h = Some v /\ forall p', p' <> p -> SM.smem_get p' h = None).
  End with_sos.
    

  (* Definitions *)
  Definition injX := @iinjX nil.

  Definition inj := @iinj nil.

  Definition emp := @iemp nil.

  Definition star := @istar nil.

  Definition ex := @iex nil.

  Definition hptsto := @ihptsto nil. 

  Ltac unfold_all := 
    unfold ex, star, emp, inj, injX, iex, istar, iemp, iinj, iinjX, himp, interp.

  Require Import PropXRel.
  
  Hint Immediate SM.split_comm : heaps.
  Hint Resolve SM.split_assoc : heaps.
  
  Lemma himp_star_comm : forall P Q, himp (star P Q) (star Q P).
  Proof.
    unfold_all; intros; propxIntuition.
    do 2 eapply Exists_I. propxIntuition; eauto using SM.split_comm.
  Qed.

  Theorem himp_star_assoc : forall P Q R,
    himp (star (star P Q) R) (star P (star Q R)).
  Proof.      
    unfold_all; intros; propxIntuition.
    destruct (SM.split_assoc _ _ _ _ _ H H0). clear H H0. destruct H1.
    do 2 eapply Exists_I; propxIntuition. eauto. do 2 eapply Exists_I. propxIntuition. eauto.
  Qed.

  Theorem himp_star_emp_p : forall P : hprop, himp (star emp P) P.
  Proof.
    unfold_all; intros; propxIntuition.
    subst. eapply SM.split_emp in H. subst; propxIntuition.
  Qed.

  Theorem himp_star_emp_c : forall P : hprop, himp P (star emp P).
  Proof.
    unfold_all; intros; propxIntuition.
    do 2 eapply Exists_I. instantiate (1 := m). instantiate (1 := SM.smem_emp).
    propxIntuition; auto. eapply SM.split_emp; auto.
  Qed.

  Theorem himp_star_frame : forall P Q R S, 
    himp P Q -> himp R S -> himp (star P R) (star Q S).
  Proof.
    unfold_all; intros; propxIntuition.
    do 2 eapply Exists_I. propxIntuition. eassumption.
    eapply Imply_E. eapply valid_weaken. eapply H. firstorder. propxIntuition.
    eapply Imply_E. eapply valid_weaken. eapply H0. firstorder. propxIntuition.
  Qed.

  Theorem himp_star_pure_p :
    forall (P Q : hprop) (F : Prop),
      himp (star (inj F) P) Q -> F -> himp P Q.
  Proof.
    unfold_all; intros; propxIntuition.
    specialize (H cs stn m). 
    eapply Imply_E. eapply valid_weaken. eapply H. firstorder.
    do 2 eapply Exists_I; propxIntuition. eapply SM.split_emp; auto. auto. reflexivity.
  Qed.

  Theorem himp_star_pure_c :
    forall (P Q : hprop) (F : Prop),
      (F -> himp P Q) -> himp (star (inj F) P) Q.
  Proof.
    unfold_all; intros; propxIntuition.
    propxIntuition. eapply Imply_E.
    eapply valid_weaken. eapply H; auto. firstorder.
    subst. eapply SM.split_emp in H0. subst.
    constructor; firstorder.
  Qed.

  Theorem himp_star_pure_cc :
    forall (P Q : hprop) (p : Prop),
      p -> himp P Q -> himp P (star (inj p) Q).
  Proof.
    unfold_all; intros; propxIntuition.
    do 2 eapply Exists_I; propxIntuition.
    2: eauto. 2: reflexivity. eapply SM.split_emp; reflexivity.
    eapply Imply_E. eapply valid_weaken. eapply H0. firstorder.
    constructor; firstorder.
  Qed.

  Theorem himp_ex_p :
    forall (T : Type) (P : T -> hprop) (Q : hprop),
      (forall v : T, himp (P v) Q) -> himp (ex P) Q.
  Proof.
    unfold_all; intros; propxIntuition.
    eapply Imply_E. eapply valid_weaken. eapply H. firstorder. constructor; firstorder.
  Qed.
  
  Theorem himp_ex_c :
    forall (T : Type) (P : T -> hprop) (Q : hprop),
      (exists v : T, himp Q (P v)) -> himp Q (ex P).
  Proof.
    unfold_all; intros; propxIntuition.
    destruct H. eapply Exists_I.
    instantiate (1 := x). eapply Imply_E.
    eapply valid_weaken; try eapply H. firstorder. constructor; firstorder.
  Qed.

  Theorem himp_ex_star : forall T (P : T -> _) Q,
    himp (star (ex P) Q) (ex (fun x => star (P x) Q)).
  Proof.
    unfold_all; intros; propxIntuition.
    eapply Exists_I with (B := x1). do 2 eapply Exists_I. propxIntuition; auto.
  Qed.

  Theorem himp_star_ex : forall T (P : T -> _) Q,
    himp (ex (fun x => star (P x) Q)) (star (ex P) Q).
  Proof.
    unfold_all; intros; propxIntuition.
    do 2 eapply Exists_I; propxIntuition; eauto.
    eapply Exists_I; propxIntuition.
  Qed.

  (** Interp **)
  Lemma interp_himp : forall cs stn sm P Q,
    interp cs (P stn sm) ->
    himp P Q ->
    interp cs (Q stn sm).
  Proof.
    unfold himp; intros.
    eapply Imply_E. eapply H0. auto.
  Qed.

  Theorem interp_star : forall cs stn sm P Q,
    interp cs ((star P Q) stn sm) ->
    exists sm1 sm2, SM.split sm sm1 sm2 /\
      interp cs (P stn sm1) /\ interp cs (Q stn sm2).
  Proof.
    unfold star. intros; propxFo; eauto.
  Qed.

  Theorem interp_pure : forall cs stn sm P,
    interp cs ((inj P) stn sm) ->
    P /\ sm = SM.smem_emp. 
  Proof.
    unfold inj, iinj, iinjX. intros. propxFo. 
  Qed.

  Theorem interp_ex : forall cs stn sm T (P : T -> _),
    interp cs ((ex P) stn sm) ->
    exists x, interp cs ((P x) stn sm).
  Proof.
    unfold ex. intros. propxFo; eauto.
  Qed.
  
End SepTheoryPropX_Kernel.
