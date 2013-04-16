Require Import AutoSep.
Require Import TimeAbstract.

(** Swapping two pointers *)

Definition swapS : spec := SPEC("x", "y") reserving 2
  Al v, Al w,
  PRE[V] V "x" =*> v * V "y" =*> w
  POST[_] V "x" =*> w * V "y" =*> v.

Definition swap := bmodule "swap" {{
  bfunction "swap"("x", "y", "v", "w") [swapS]
    "v" <-* "x";;
    "w" <-* "y";;
    "x" *<- "w";;
    "y" *<- "v";;
    Return 0
  end
}}.

Theorem swapOk : moduleOk swap.
(*TIME Clear Timing Profile. *)
(*TIME  (time "vcgen:all" *) vcgen
(*TIME ) *); time_abstract ltac:(sep_auto).
(*TIME Print Timing Profile. *)
Qed.
