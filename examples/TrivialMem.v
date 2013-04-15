Require Import PreAutoSep.
Require Import TimeAbstract.

(** * A trivial example to make sure the separation logic proof automation isn't completely borked *)

Definition readS : spec := SPEC("x") reserving 1
  Al v,
  PRE[V] V "x" =*> v
  POST[R] [| R = v |] * V "x" =*> v.

Definition read := bmodule "read" {{
  bfunction "read"("x", "y") [readS]
    "y" <-* "x";;
    If ("y" = 0) {
      "x" *<- 0
    } else {
      "x" *<- "y"
    } ;;
    "y" <-* "x";;
    Return "y"
  end
}}.

Theorem readOk : moduleOk read.
(*TIME  Clear Timing Profile. *)
(*TIME  (time "vcgen:all" *) vcgen
(*TIME ) *); time_abstract ltac:(sep_auto).
(*TIME  Print Timing Profile. *)
Qed.
