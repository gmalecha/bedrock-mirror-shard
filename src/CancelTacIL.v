Require MirrorShard.CancelTacBedrock.
Require MirrorShard.ExprUnify.
Require Import SepIL TacPackIL.

Set Implicit Arguments.
Set Strict Implicit.

Module CANCEL_TAC := 
  MirrorShard.CancelTacBedrock.Make SepIL.ST SepIL.SEP SepIL.SH
                                    TacPackIL.SEP_LEMMA 
                                    ExprUnify.UNIFIER
                                    UNF.
