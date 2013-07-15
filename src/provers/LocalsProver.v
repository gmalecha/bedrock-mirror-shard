Require Import List Arith Bool.
Require Import MirrorShard.Expr MirrorShard.Env.
Require Import MirrorShard.Prover.
Require Import MirrorShard.provers.ReflexivityProver.
Require Import Word.
Require Import sep.Locals.

Set Implicit Arguments.
Set Strict Implicit.

(** * The Word Prover **)

Require Import Arith ILEnv Memory.

Section LocalsProver.
  Variable types' : list type.
  Definition types := Locals.types types'.
  Variable funcs' : functions types.
  Definition funcs := Locals.funcs funcs'.

  Definition localsSimplify (e : expr) : expr :=
    match e with
      | Func 18 (vs :: nm :: nil) =>
        match toConst_string nm with
          | Some nm => sym_sel vs nm
          | _ => e
        end
      | _ => e
    end.

  Definition localsProve (_ : unit) (goal : expr) := 
    match goal with
      | Equal _ x y => expr_seq_dec (localsSimplify x) (localsSimplify y)
      | _ => false
    end.

  Lemma localsSimplify_correct : forall uvars vars (e : expr) t v,
    exprD funcs uvars vars e t = Some v
    -> exprD funcs uvars vars (localsSimplify e) t = Some v.
  Proof.
    destruct e; simpl; intuition idtac.
    do 19 (destruct f; try assumption).
    do 3 (destruct l; try assumption).
    generalize (toConst_string_sound funcs e0).
    destruct (toConst_string e0); auto.
    simpl in H.
    destruct (equiv_dec (tvType 0) t); try discriminate.
    hnf in e1; subst.
    change ((forall uvars0 vars0 : env (Locals.types types'),
               exprD funcs uvars0 vars0 e0 (tvType 8) = Some s) ->
            exprD funcs uvars vars (sym_sel e s) (tvType 0) = Some v).
    intro.
    rewrite H0 in *.
    generalize (sym_sel_correct funcs' uvars vars s e).
    change (Locals.funcs funcs') with funcs.
    match type of H with
      | match ?E with Some _ => _ | _ => _ end _ _ = _ => destruct E; try discriminate
    end.
    intro X. rewrite <- H. eapply X. reflexivity.
  Qed.

  Theorem localsProveCorrect : ProverCorrect funcs reflexivityValid localsProve.
  Proof.
    unfold localsProve; hnf; simpl; intros.

    destruct goal; try discriminate.
    destruct H1.
    apply expr_seq_dec_correct in H0.
    hnf.
    simpl in *.
    generalize (localsSimplify_correct uvars vars goal1 t).
    generalize (localsSimplify_correct uvars vars goal2 t).
    destruct (exprD funcs uvars vars goal1 t); try discriminate.
    destruct (exprD funcs uvars vars goal2 t); try discriminate.
    intros.
    specialize (H2 _ (refl_equal _)).
    specialize (H3 _ (refl_equal _)).
    congruence.
  Qed.

  Definition localsProver : ProverT :=
    {| Facts := unit
     ; Summarize := reflexivitySummarize
     ; Learn := reflexivityLearn
     ; Prove := localsProve |}.

  Definition localsProver_correct : ProverT_correct localsProver funcs.
    eapply Build_ProverT_correct with (Valid := reflexivityValid : _ -> _ -> Facts localsProver -> Prop); unfold reflexivityValid; eauto.
    apply localsProveCorrect.
  Qed.

End LocalsProver.

Definition LocalsProver : ProverPackage :=
{| ProverTypes := Locals.types_r
 ; ProverFuncs := Locals.funcs_r
 ; Prover_correct := localsProver_correct
|}.
