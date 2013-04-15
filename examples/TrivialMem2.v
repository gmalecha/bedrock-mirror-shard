Require Import AutoSep.
Require Import TimeAbstract.

(** * Like TrivialMem, but tests use of equality prover in symbolic evaluation *)

Definition readS : spec := SPEC("x", "y") reserving 1
  Al v,
  PRE[V] V "x" =*> v
  POST[R] [| R = v |] * V "x" =*> v.

Definition read := bmodule "read" {{
  bfunction "read"("x", "y", "z") [readS]
    If ("x" = "y") {
      "z" <-* "y"
    } else {
      "z" <-* "x"
    };;
    Return "z"
  end
}}.

Theorem readOk : moduleOk read.
(*TIME  Clear Timing Profile. *)
(*TIME  (time "vcgen:all" *) vcgen
(*TIME ) *); time_abstract ltac:(sep_auto).
(*TIME  Print Timing Profile. *)
Qed.
