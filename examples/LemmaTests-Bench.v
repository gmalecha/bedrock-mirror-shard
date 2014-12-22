(** This file is used to collect profiling information
 ** for cancellation.
 ** You should run each [go] command several times.
 **)
Require Import Timing.
Require Import PreAutoSep.

Fixpoint quant (n : nat) (k : list W -> Prop) :=
  match n with
    | 0 => k nil
    | S n => quant n (fun ls => forall x : W, k (x :: ls))
  end.

Fixpoint chain (ls : list W) : hprop :=
  match ls with
    | nil => emp
    | l :: ls =>
      match ls with
        | nil => emp
        | l' :: ls' =>
          l =*> l' * chain ls
      end
  end%Sep.

Ltac go :=
  simpl; unfold Himp in *; simpl; intros;
  start_timer "cancel" ;
  sep_canceler 10 10 ltac:ILTacCommon.isConst tt ;
  stop_timer "cancel" ;
  reflexivity.

Goal quant 5 (fun ls => chain ls ===> chain ls).
Clear Timing Profile.
go.
Print Timing Profile.
Time Qed.

Goal quant 10 (fun ls => chain ls ===> chain ls).
Clear Timing Profile.
go.
Print Timing Profile.
Time Qed.

Goal quant 25 (fun ls => chain ls ===> chain ls).
Clear Timing Profile.
go.
Print Timing Profile.
Time Qed.

Goal quant 50 (fun ls => chain ls ===> chain ls).
Clear Timing Profile.
go.
Print Timing Profile.
Time Qed.
