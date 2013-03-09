Require Import AutoSep Malloc Bags ThreadQueues SinglyLinkedList.
Import W_Bag.
Export AutoSep Malloc W_Bag.

Lemma equiv_empty : forall ls, empty %= bagify ls
  -> ls = nil.
  unfold bagify; destruct ls; simpl; intuition.
  eapply equiv_symm in H; eapply equiv_trans in H; [ | eapply equiv_symm; eapply add_something ].
  elimtype False.
  generalize dependent (fold_left add ls empty); intros.
  bags.
  specialize (H a).
  destruct (W_Key.eq_dec a a); congruence.
Qed.

Theorem starB_empty_fwd : forall P, starB P empty ===> Emp.
  unfold starB; intros; intro.
  apply himp_ex_p; intros.
  apply himp_star_pure_c; intro H.
  apply equiv_empty in H; subst.
  reflexivity.
Qed.


Module Type S.
  Parameter globalSched : W.

  Parameter globalInv : bag -> HProp.
  (* Argument is set of available file objects. *)
End S.

Module Make(M : S).
Import M.

Definition allIn (b : bag) := List.Forall (fun p => p %in b).
Definition allInOrZero (b : bag) := List.Forall (fun p => p = $0 \/ p %in b).

Definition files (ts : bag) : bag -> HProp :=
  starB (fun p => Ex fd, Ex inq, Ex outq, (p ==*> fd, inq, outq) * [| inq %in ts |] * [| outq %in ts |])%Sep.

Module M''.
  Definition world := bag.

  Definition evolve : bag -> bag -> Prop := incl.

  Theorem evolve_refl : forall w, evolve w w.
    red; bags.
  Qed.

  Theorem evolve_trans : forall w1 w2 w3, evolve w1 w2 -> evolve w2 w3 -> evolve w1 w3.
    unfold evolve in *; bags.
  Qed.

  Open Scope Sep_scope.

  Definition globalInv (ts : bag) (w : world) : HProp :=
    Ex p, Ex ready, Ex free, Ex wait, Ex waitLen, Ex freeL, Ex waitL,
    
    (* The scheduler entry point *)
    globalSched =*> p * (p ==*> ready, free, wait, waitLen)

    (* The ready queue is a valid thread queue, for threads ready to run immediately. *)
    * [| ready %in ts |]

    (* The free list stores available file pointers. *)
    * sll freeL free * [| allIn w freeL |]

    (* Each available file pointer stores a record of a file descriptor and input/output thread queues. *)
    * files ts w

    (* There is an array correspoinding to outstanding declare() calls, mapping each to a queue that should be poked when its event is enabled. *)
    * array waitL wait * [| allInOrZero ts waitL |]
      * [| length waitL = wordToNat waitLen |]
      * [| wait <> 0 |] * [| freeable wait (length waitL) |]

    (* Finally, the application-specific global invariant holds. *)
    * globalInv w.
End M''.

Module Q' := ThreadQueues.Make(M'').
Import M'' Q'.
Export M'' Q'.


Definition files_pick (_ : W) := files.

Module Type SCHED.
  Parameter sched : bag -> HProp.
  (* Parameter is available file pointers. *)

  Axiom sched_fwd : forall fs, sched fs ===>
    Ex ts, Ex p, globalSched =*> p
    * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)
    * [| ready %in ts |]
    * Ex freeL, sll freeL free * [| allIn fs freeL |]
    * files ts fs
    * Ex waitL, array waitL wait * [| allInOrZero ts waitL |] * [| length waitL = wordToNat waitLen |]
      * [| wait <> 0 |] * [| freeable wait (length waitL) |]
    * tqs ts fs.

  Axiom sched_bwd : forall fs,
    (Ex ts, Ex p, globalSched =*> p
     * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)
     * [| ready %in ts |]
     * Ex freeL, sll freeL free * [| allIn fs freeL |]
     * files ts fs
     * Ex waitL, array waitL wait * [| allInOrZero ts waitL |] * [| length waitL = wordToNat waitLen |]
       * [| wait <> 0 |] * [| freeable wait (length waitL) |]
     * tqs ts fs)
    ===> sched fs.

  Axiom files_empty_fwd : forall ts, files ts empty ===> Emp.
  Axiom files_empty_bwd : forall ts, Emp ===> files ts empty.

  Axiom files_pick_fwd : forall p ts fs, p %in fs
    -> files_pick p ts fs ===> Ex fd, Ex inq, Ex outq, (p ==*> fd, inq, outq)
      * [| inq %in ts |] * [| outq %in ts |] * files ts (fs %- p).
  Axiom files_pick_bwd : forall p ts fs, p %in fs
    -> (Ex fd, Ex inq, Ex outq, (p ==*> fd, inq, outq)
      * [| inq %in ts |] * [| outq %in ts |] * files ts (fs %- p)) ===> files_pick p ts fs.

  Axiom files_add_bwd : forall p ts fs,
    (Ex fd, Ex inq, Ex outq, (p ==*> fd, inq, outq)
      * [| inq %in ts |] * [| outq %in ts |] * files ts fs) ===> files ts (fs %+ p).
End SCHED.

Module Sched : SCHED.
  Open Scope Sep_scope.

  Definition sched fs :=
    Ex ts, Ex p, globalSched =*> p
    * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)
    * [| ready %in ts |]
    * Ex freeL, sll freeL free * [| allIn fs freeL |]
    * files ts fs
    * Ex waitL, array waitL wait * [| allInOrZero ts waitL |] * [| length waitL = wordToNat waitLen |]
      * [| wait <> 0 |] * [| freeable wait (length waitL) |]
    * tqs ts fs.

  Theorem sched_fwd : forall fs, sched fs ===>
    Ex ts, Ex p, globalSched =*> p
    * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)
    * [| ready %in ts |]
    * Ex freeL, sll freeL free * [| allIn fs freeL |]
    * files ts fs
    * Ex waitL, array waitL wait * [| allInOrZero ts waitL |] * [| length waitL = wordToNat waitLen |]
      * [| wait <> 0 |] * [| freeable wait (length waitL) |]
    * tqs ts fs.
    intros; apply Himp_refl.
  Qed.

  Theorem sched_bwd : forall fs,
    (Ex ts, Ex p, globalSched =*> p
     * Ex ready, Ex free, Ex wait, Ex waitLen, (p ==*> ready, free, wait, waitLen)
     * [| ready %in ts |]
     * Ex freeL, sll freeL free * [| allIn fs freeL |]
     * files ts fs
     * Ex waitL, array waitL wait * [| allInOrZero ts waitL |] * [| length waitL = wordToNat waitLen |]
       * [| wait <> 0 |] * [| freeable wait (length waitL) |]
     * tqs ts fs)
     ===> sched fs.
    intros; apply Himp_refl.
  Qed.

  Theorem files_empty_fwd : forall ts, files ts empty ===> Emp.
    intros; apply starB_empty_fwd.
  Qed.

  Theorem files_empty_bwd : forall ts, Emp ===> files ts empty.
    intros; apply starB_empty_bwd.
  Qed.

  Ltac fin ts := match goal with
                   | [ |- context[starB ?X ?Y] ] => change (starB X Y) with (files ts Y)
                 end; sepLemma.

  Theorem files_pick_fwd : forall p ts fs, p %in fs
    -> files_pick p ts fs ===> Ex fd, Ex inq, Ex outq, (p ==*> fd, inq, outq)
      * [| inq %in ts |] * [| outq %in ts |] * files ts (fs %- p).
    intros; eapply Himp_trans; [ apply starB_del_fwd | ]; eauto; fin ts.
  Qed.

  Theorem files_pick_bwd : forall p ts fs, p %in fs
    -> (Ex fd, Ex inq, Ex outq, (p ==*> fd, inq, outq)
      * [| inq %in ts |] * [| outq %in ts |] * files ts (fs %- p)) ===> files_pick p ts fs.
    intros; eapply Himp_trans; [ | apply starB_del_bwd ]; eauto; fin ts.
  Qed.

  Theorem files_add_bwd : forall p ts fs,
    (Ex fd, Ex inq, Ex outq, (p ==*> fd, inq, outq)
      * [| inq %in ts |] * [| outq %in ts |] * files ts fs) ===> files ts (fs %+ p).
    intros; eapply Himp_trans; [ | apply starB_add_bwd ]; fin ts.
  Qed.
End Sched.

Import Sched.
Export Sched.

Lemma allocate_array' : forall p n offset,
  allocated p offset n ===> Ex ls, [| length ls = n |] * array ls (p ^+ $(offset)).
  induction n; simpl.

  sepLemma.
  instantiate (1 := nil); auto.
  sepLemma.

  intros; sepLemmaLhsOnly.
  etransitivity; [ eapply himp_star_frame; [ apply IHn | reflexivity ] | ]; clear IHn.
  sepLemmaLhsOnly.
  apply himp_ex_c; exists (x :: x0).
  sepLemma.
  etransitivity; [ eapply himp_star_frame; [ apply ptsto32m'_in | reflexivity ] | ].
  etransitivity; [ | apply ptsto32m'_out ].
  simpl.
  destruct offset; simpl.
  replace (p ^+ natToW 0) with p by words; sepLemma.
  etransitivity; [ | apply ptsto32m'_shift_base ].
  instantiate (1 := 4); reflexivity.
  auto.
  replace (p ^+ natToW (S offset) ^+ $0) with (p ^+ natToW (S offset)) by words.
  sepLemma.
  etransitivity; [ | apply ptsto32m'_shift_base ].
  instantiate (1 := 4).
  rewrite <- wplus_assoc.
  rewrite <- natToW_plus.
  replace (S offset + 4) with (S (S (S (S (S offset))))) by omega.
  reflexivity.
  auto.
Qed.

Inductive make_array : Prop := MakeArray.

Hint Constructors make_array.

Lemma allocate_array : forall p n,
  p = p
  -> make_array
  -> p =?> n ===> Ex ls, [| length ls = n |] * array ls p.
  intros; eapply Himp_trans; [ apply allocate_array' | ].
  replace (p ^+ $0) with p by words; apply Himp_refl.
Qed.

Lemma free_array' : forall p n offset,
  Ex ls, [| length ls = n |] * array ls (p ^+ $(offset)) ===> allocated p offset n.
  sepLemma.
  etransitivity; [ apply ptsto32m_allocated | ].
  etransitivity; [ apply allocated_shift_base | ].
  3: sepLemma.
  unfold natToW; W_eq.
  auto.
Qed.

Inductive dissolve_array : Prop := DissolveArray.

Hint Constructors dissolve_array.

Lemma free_array : forall p n,
  p = p
  -> dissolve_array
  -> Ex ls, [| length ls = n |] * array ls p ===> p =?> n.
  intros; eapply Himp_trans; [ | apply free_array' ].
  replace (p ^+ $0) with p by words; apply Himp_refl.
Qed.

Theorem tqs_empty_bwd : forall w, Emp ===> tqs empty w.
  intros; rewrite tqs_eq; apply tqs'_empty_bwd.
Qed.

Definition hints : TacPackage.
  prepare (sched_fwd, SinglyLinkedList.nil_fwd, SinglyLinkedList.cons_fwd, allocate_array,
    files_empty_fwd, files_pick_fwd)
  (sched_bwd, SinglyLinkedList.nil_bwd, SinglyLinkedList.cons_bwd, free_array, tqs_empty_bwd,
    files_empty_bwd, files_pick_bwd, files_add_bwd).
Defined.

Definition starting (pc : W) (ss : nat) : HProp := fun s m =>
  (ExX (* pre *) : settings * state, Cptr pc #0
    /\ [| semp m |]
    /\ Al st : settings * state, Al vs, Al fs,
      [| st#Sp <> 0 /\ freeable st#Sp (1 + ss) |]
      /\ ![ ^[locals ("rp" :: nil) vs ss st#Sp * sched fs * M.globalInv fs * mallocHeap 0] ] st
      ---> #0 st)%PropX.

Lemma starting_elim : forall specs pc ss P stn st,
  interp specs (![ starting pc ss * P ] (stn, st))
  -> (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs fs, interp specs ([| stn_st#Sp <> 0 /\ freeable stn_st#Sp (1 + ss) |]
      /\ ![ locals ("rp" :: nil) vs ss stn_st#Sp
      * sched fs * M.globalInv fs * mallocHeap 0 ] stn_st
    ---> pre stn_st)%PropX).
  cptr.
  generalize (split_semp _ _ _ H0 H); intros; subst; auto.
  rewrite <- sepFormula_eq; descend; step auto_ext.
  auto.
  step auto_ext.
Qed.

Local Hint Resolve split_a_semp_a semp_smem_emp.

Lemma starting_intro : forall specs pc ss P stn st,
  (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs fs, interp specs ([| stn_st#Sp <> 0 /\ freeable stn_st#Sp (1 + ss) |]
      /\ ![ locals ("rp" :: nil) vs ss stn_st#Sp
      * sched fs * M.globalInv fs * mallocHeap 0 ] stn_st
    ---> pre stn_st)%PropX)
  -> interp specs (![ starting pc ss * P ] (stn, st)).
  cptr.
Qed.

Lemma other_starting_intro : forall specs ts w pc ss P stn st,
  (exists pre, specs pc = Some (fun x => pre x)
    /\ interp specs (![ P ] (stn, st))
    /\ forall stn_st vs ts' w', interp specs ([| ts %<= ts' |]
      /\ [| M''.evolve w w' |]
      /\ [| stn_st#Sp <> 0 /\ freeable stn_st#Sp (1 + ss) |]
      /\ ![ locals ("rp" :: nil) vs ss stn_st#Sp
      * tqs ts' w' * M''.globalInv ts' w' * mallocHeap 0 ] stn_st
    ---> pre stn_st)%PropX)
  -> interp specs (![ Q'.starting ts w pc ss * P ] (stn, st)).
  cptr.
Qed.


Local Notation "'PREexit' [ vs ] pre" := (Q'.Q.localsInvariantExit (fun vs _ => pre%qspec%Sep))
  (at level 89).

Definition initS : spec := SPEC reserving 18
  PRE[_] globalSched =?> 1 * mallocHeap 0
  POST[R] sched empty * mallocHeap 0.

Definition spawnS : spec := SPEC("pc", "ss") reserving 26
  Al fs,
  PRE[V] [| V "ss" >= $2 |] * sched fs * starting (V "pc") (wordToNat (V "ss") - 1) * mallocHeap 0
  POST[_] sched fs * mallocHeap 0.

Definition exitS : spec := SPEC("sc", "ss") reserving 2
  Al fs,
  PREexit[V] [| V "ss" >= $3 |] * sched fs * M.globalInv fs * mallocHeap 0.

Definition yieldS : spec := SPEC reserving 28
  Al fs,
  PRE[_] sched fs * M.globalInv fs * mallocHeap 0
  POST[_] Ex fs', [| fs %<= fs' |] * sched fs' * M.globalInv fs' * mallocHeap 0.

Definition listenS : spec := SPEC("port") reserving 25
  Al fs,
  PRE[_] sched fs * mallocHeap 0
  POST[R] Ex fs', [| fs %<= fs' |] * sched fs' * mallocHeap 0 * [| R %in fs' |].

Definition closeS : spec := SPEC("fr") reserving 11
  Al fs,
  PRE[V] [| V "fr" %in fs |] * sched fs * mallocHeap 0
  POST[_] sched fs * mallocHeap 0.

Definition readS : spec := SPEC("fr", "buffer", "size") reserving 32
  Al fs,
  PRE[V] [| V "fr" %in fs |] * V "buffer" =?>8 wordToNat (V "size") * sched fs * mallocHeap 0 * M.globalInv fs
  POST[_] Ex fs', [| fs %<= fs' |] * V "buffer" =?>8 wordToNat (V "size") * sched fs' * mallocHeap 0 * M.globalInv fs'.

Definition writeS : spec := SPEC("fr", "buffer", "size") reserving 32
  Al fs,
  PRE[V] [| V "fr" %in fs |] * V "buffer" =?>8 wordToNat (V "size") * sched fs * mallocHeap 0 * M.globalInv fs
  POST[_] Ex fs', [| fs %<= fs' |] * V "buffer" =?>8 wordToNat (V "size") * sched fs' * mallocHeap 0 * M.globalInv fs'.

Definition acceptS : spec := SPEC("fr") reserving 32
  Al fs,
  PRE[V] [| V "fr" %in fs |] * sched fs * mallocHeap 0 * M.globalInv fs
  POST[R] Ex fs', Ex fs'', [| fs %<= fs' |] * [| fs' %<= fs'' |]
    * [| R %in fs'' |] * sched fs'' * mallocHeap 0 * M.globalInv fs'.

(* Specs below this point are for "private" functions. *)

Definition pickNextS : spec := SPEC reserving 13
  Al p, Al ready, Al free, Al wait, Al waitLen, Al ts, Al fs, Al waitL,
  PRE[_] globalSched =*> p * (p ==*> ready, free, wait, waitLen)
    * tqs ts fs * [| ready %in ts |]
    * array waitL wait * [| allInOrZero ts waitL |]
    * [| length waitL = wordToNat waitLen |] * mallocHeap 0
  POST[R] [| R %in ts |]
    * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
    * tqs ts fs * [| ready %in ts |]
    * array waitL wait * [| allInOrZero ts waitL |]
    * [| length waitL = wordToNat waitLen |] * mallocHeap 0.

Definition newS : spec := SPEC("fd") reserving 21
  Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL,
  PRE[V] globalSched =*> p * (p ==*> ready, free, wait, waitLen)
    * sll freeL free * [| allIn fs freeL |]
    * files ts fs * tqs ts fs * mallocHeap 0
  POST[R] Ex ts', Ex fs', Ex free', Ex freeL',
    [| R %in fs' |] * [| ts %<= ts' |] * [| fs %<= fs' |]
    * globalSched =*> p * (p ==*> ready, free', wait, waitLen)
    * sll freeL' free' * [| allIn fs' freeL' |]
    * files ts' fs' * tqs ts' fs' * mallocHeap 0.

Definition declareS : spec := SPEC("tq", "fd", "mode") reserving 16
    Al ts, Al p, Al ready, Al free, Al wait, Al waitLen, Al waitL,
    PRE[V] [| V "tq" %in ts |] * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
      * array waitL wait * [| allInOrZero ts waitL |]
      * [| length waitL = wordToNat waitLen |]
      * [| wait <> 0 |] * [| freeable wait (length waitL) |]
      * mallocHeap 0
    POST[_] Ex wait', Ex waitLen', Ex waitL',
      globalSched =*> p * (p ==*> ready, free, wait', waitLen')
      * array waitL' wait' * [| allInOrZero ts waitL' |]
      * [| length waitL' = wordToNat waitLen' |]
      * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
      * mallocHeap 0.

Definition blockS : spec := SPEC("tq", "fd", "mode") reserving 26
  Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
  PRE[V] [| V "tq" %in ts |]
    * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
    * [| ready %in ts |]
    * sll freeL free * [| allIn fs freeL |]
    * files ts fs * tqs ts fs
    * array waitL wait * [| allInOrZero ts waitL |]
      * [| length waitL = wordToNat waitLen |]
      * [| wait <> 0 |] * [| freeable wait (length waitL) |]
    * M.globalInv fs * mallocHeap 0
  POST[_] Ex p', Ex ts', Ex fs', Ex ready', Ex free', Ex wait', Ex waitLen', Ex freeL', Ex waitL',
    [| ts %<= ts' |] * [| fs %<= fs' |]
    * globalSched =*> p' * (p' ==*> ready', free', wait', waitLen')
    * [| ready' %in ts' |]
    * sll freeL' free' * [| allIn fs' freeL' |]
    * files ts' fs' * tqs ts' fs'
    * array waitL' wait' * [| allInOrZero ts' waitL' |]
      * [| length waitL' = wordToNat waitLen' |]
      * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
    * M.globalInv fs' * mallocHeap 0.

Definition initSize := 2.

Theorem initSize_eq : initSize = 2.
  auto.
Qed.

Opaque initSize.

Inductive add_a_file : Prop := AddAFile.
Inductive reveal_files_pick : Prop := RevealFilesPick.
Local Hint Constructors add_a_file reveal_files_pick.

Definition m := bimport [[ "malloc"!"malloc" @ [mallocS], "malloc"!"free" @ [freeS],
                           "threadqs"!"alloc" @ [Q'.allocS], "threadqs"!"spawn" @ [Q'.spawnS],
                           "threadqs"!"exit" @ [Q'.exitS], "threadqs"!"yield" @ [Q'.yieldS],
                           "threadqs"!"isEmpty" @ [Q'.isEmptyS],

                           "sys"!"abort" @ [abortS], "sys"!"close" @ [Sys.closeS],
                           "sys"!"listen" @ [Sys.listenS], "sys"!"accept" @ [Sys.acceptS],
                           "sys"!"read" @ [Sys.readS], "sys"!"write" @ [Sys.writeS],
                           "sys"!"declare" @ [Sys.declareS], "sys"!"wait" @ [Sys.waitS] ]]
  bmodule "scheduler" {{
    bfunction "init"("root", "ready", "wait") [initS]
      "root" <-- Call "malloc"!"malloc"(0, 4)
      [PRE[_, R] globalSched =?> 1 * R =?> 4 * mallocHeap 0
       POST[_] sched empty * mallocHeap 0];;

      globalSched *<- "root";;

      Assert [PRE[V] globalSched =*> V "root" * V "root" =?> 4 * mallocHeap 0 * tqs empty empty
        POST[_] sched empty * mallocHeap 0];;

      "ready" <-- Call "threadqs"!"alloc"()
      [PRE[V, R] globalSched =*> V "root" * V "root" =?> 4 * tqs (empty %+ R) empty * mallocHeap 0
       POST[_] sched empty * mallocHeap 0];;

      "wait" <-- Call "malloc"!"malloc"(0, initSize)
      [PRE[V, R] R =?> initSize * [| R <> 0 |] * [| freeable R initSize |]
         * globalSched =*> V "root" * V "root" =?> 4
         * tqs (empty %+ V "ready") empty
       POST[_] sched empty];;

      Note [make_array];;

      Assert [Al waitL,
        PRE[V] array waitL (V "wait") * [| length waitL = 2 |] * [| V "wait" <> 0 |] * [| freeable (V "wait") 2 |]
          * [| ($0 < natToW (length waitL))%word |]
          * globalSched =*> V "root" * V "root" =?> 4 * tqs (empty %+ V "ready") empty
        POST[_] sched empty];;

      "wait"+0 *<- 0;;

      Assert [Al waitL,
        PRE[V] array waitL (V "wait") * [| length waitL = 2 |] * [| V "wait" <> 0 |] * [| freeable (V "wait") 2 |]
          * [| ($1 < natToW (length waitL))%word |] * [| Array.selN waitL 0 = $0 |]
          * globalSched =*> V "root" * V "root" =?> 4 * tqs (empty %+ V "ready") empty
        POST[_] sched empty];;

      "wait"+4 *<- 0;;

      "root" *<- "ready";;
      "root"+4 *<- 0;;
      "root"+8 *<- "wait";;
      "root"+12 *<- 2;;
      Return 0
    end with bfunction "spawn"("pc", "ss", "root") [spawnS]
      "root" <-* globalSched;;
      "root" <-* "root";;

      Call "threadqs"!"spawn"("root", "pc", "ss")
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end (*with bfunctionNoRet "exit"("sc", "ss") [exitS]
      "sc" <-* globalSched;;
      Goto "threadqs"!"exit"
    end*) with bfunction "yield"("root", "ready", "q") [yieldS]
      "root" <-* globalSched;;
      "ready" <-* "root";;

      "q" <-- Call "scheduler"!"pickNext"()
      [Al ts, Al fs, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
        PRE[V, R] globalSched =*> V "root" * (V "root" ==*> V "ready", free, wait, waitLen)
          * [| V "ready" %in ts |] * [| R %in ts |]
          * sll freeL free * [| allIn fs freeL |]
          * files ts fs
          * array waitL wait * [| allInOrZero ts waitL |]
          * [| length waitL = wordToNat waitLen |]
          * [| wait <> 0 |] * [| freeable wait (length waitL) |]
          * tqs ts fs * M.globalInv fs * mallocHeap 0
        POST[_] Ex ts', Ex fs', Ex p, Ex ready, Ex free, Ex wait, Ex waitLen, Ex freeL, Ex waitL,
          [| ts %<= ts' |] * [| fs %<= fs' |]
          * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
          * [| ready %in ts' |]
          * sll freeL free * [| allIn fs' freeL |]
          * files ts' fs'
          * array waitL wait * [| allInOrZero ts' waitL |]
          * [| length waitL = wordToNat waitLen |]
          * [| wait <> 0 |] * [| freeable wait (length waitL) |]
          * tqs ts' fs' * M.globalInv fs' * mallocHeap 0 ];;

      Call "threadqs"!"yield"("ready", "q")
      [PRE[_] Emp
       POST[_] Emp];;
      Return 0
    end with bfunction "listen"("port", "fd", "fr") [listenS]
      "fd" <-- Call "sys"!"listen"("port")
      [Al fs,
        PRE[_] sched fs * mallocHeap 0
        POST[R] Ex fs', [| fs %<= fs' |] * sched fs' * mallocHeap 0 * [| R %in fs' |] ];;

      "fr" <-- Call "scheduler"!"new"("fd")
      [PRE[_, R] Emp
       POST[R'] [| R' = R |] ];;
      Return "fr"
    end with bfunction "close"("fr", "root", "free", "fd", "node") [closeS]
      "root" <-* globalSched;;
      "free" <-* "root"+4;;

      Note [reveal_files_pick];;

      Assert [Al ts, Al fs, Al ready, Al wait, Al waitLen, Al freeL,
        PRE[V] globalSched =*> V "root" * (V "root" ==*> ready, V "free", wait, waitLen)
          * sll freeL (V "free") * [| allIn fs freeL |]
          * files_pick (V "fr") ts fs * mallocHeap 0
          * [| V "fr" %in fs |]
        POST[_] Ex free', Ex freeL',
          globalSched =*> V "root" * (V "root" ==*> ready, free', wait, waitLen)
          * sll freeL' free' * [| allIn fs freeL' |]
          * files_pick (V "fr") ts fs * mallocHeap 0];;

      "fd" <-* "fr";;
      Call "sys"!"close"("fd")
      [Al fs, Al ready, Al wait, Al waitLen, Al freeL, Al fd, Al inq, Al outq,
        PRE[V] globalSched =*> V "root" * (V "root" ==*> ready, V "free", wait, waitLen)
          * sll freeL (V "free") * [| allIn fs freeL |]
          * (V "fr" ==*> fd, inq, outq) * mallocHeap 0
          * [| V "fr" %in fs |]
        POST[_] Ex free', Ex freeL',
          globalSched =*> V "root" * (V "root" ==*> ready, free', wait, waitLen)
          * sll freeL' free' * [| allIn fs freeL' |]
          * (V "fr" ==*> fd, inq, outq) * mallocHeap 0];;

      "node" <-- Call "malloc"!"malloc"(0, 2)
      [Al fs, Al ready, Al wait, Al waitLen, Al freeL,
        PRE[V, R] R =?> 2 * [| R <> 0 |] * [| freeable R 2 |]
          * globalSched =*> V "root" * (V "root" ==*> ready, V "free", wait, waitLen)
          * sll freeL (V "free") * [| allIn fs freeL |]
          * [| V "fr" %in fs |]
        POST[_] Ex free', Ex freeL',
          globalSched =*> V "root" * (V "root" ==*> ready, free', wait, waitLen)
          * sll freeL' free' * [| allIn fs freeL' |] ];;

      "node" *<- "fr";;
      "node"+4 *<- "free";;
      "root"+4 *<- "node";;
      Return 0
    end with bfunction "read"("fr", "buffer", "size", "fd", "tq") [readS]
      Note [reveal_files_pick];;

      Assert [Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
        PRE[V] [| V "fr" %in fs |] * V "buffer" =?>8 wordToNat (V "size")
          * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
          * [| ready %in ts |]
          * sll freeL free * [| allIn fs freeL |]
          * files_pick (V "fr") ts fs * tqs ts fs
          * array waitL wait * [| allInOrZero ts waitL |]
            * [| length waitL = wordToNat waitLen |]
            * [| wait <> 0 |] * [| freeable wait (length waitL) |]
          * M.globalInv fs * mallocHeap 0
        POST[_] Ex p', Ex ts', Ex fs', Ex ready', Ex free', Ex wait', Ex waitLen', Ex freeL', Ex waitL',
          [| ts %<= ts' |] * [| fs %<= fs' |] * V "buffer" =?>8 wordToNat (V "size")
          * [| V "fr" %in fs' |]
          * globalSched =*> p' * (p' ==*> ready', free', wait', waitLen')
          * [| ready' %in ts' |]
          * sll freeL' free' * [| allIn fs' freeL' |]
          * files ts' fs' * tqs ts' fs'
          * array waitL' wait' * [| allInOrZero ts' waitL' |]
            * [| length waitL' = wordToNat waitLen' |]
            * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
          * M.globalInv fs' * mallocHeap 0];;

      "fd" <-* "fr";;
      "tq" <-* "fr"+4;;

      Assert [Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
        PRE[V] [| V "tq" %in ts |] * [| V "fr" %in fs |] * V "buffer" =?>8 wordToNat (V "size")
          * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
          * [| ready %in ts |]
          * sll freeL free * [| allIn fs freeL |]
          * files_pick (V "fr") ts fs * tqs ts fs
          * array waitL wait * [| allInOrZero ts waitL |]
            * [| length waitL = wordToNat waitLen |]
            * [| wait <> 0 |] * [| freeable wait (length waitL) |]
          * M.globalInv fs * mallocHeap 0
        POST[_] Ex p', Ex ts', Ex fs', Ex ready', Ex free', Ex wait', Ex waitLen', Ex freeL', Ex waitL',
          [| ts %<= ts' |] * [| fs %<= fs' |] * V "buffer" =?>8 wordToNat (V "size")
          * [| V "fr" %in fs' |]
          * globalSched =*> p' * (p' ==*> ready', free', wait', waitLen')
          * [| ready' %in ts' |]
          * sll freeL' free' * [| allIn fs' freeL' |]
          * files ts' fs' * tqs ts' fs'
          * array waitL' wait' * [| allInOrZero ts' waitL' |]
            * [| length waitL' = wordToNat waitLen' |]
            * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
          * M.globalInv fs' * mallocHeap 0];;

      Note [reveal_files_pick];;

      Call "scheduler"!"block"("tq", "fd", 0)
      [PRE[V] V "buffer" =?>8 wordToNat (V "size")
       POST[_] V "buffer" =?>8 wordToNat (V "size")];;

      "size" <-- Call "sys"!"read"("fd", "buffer", "size")
      [PRE[_] Emp
       POST[_] Emp ];;
      Return "size"
    end with bfunction "write"("fr", "buffer", "size", "fd", "tq") [writeS]
      Note [reveal_files_pick];;

      Assert [Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
        PRE[V] [| V "fr" %in fs |] * V "buffer" =?>8 wordToNat (V "size")
          * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
          * [| ready %in ts |]
          * sll freeL free * [| allIn fs freeL |]
          * files_pick (V "fr") ts fs * tqs ts fs
          * array waitL wait * [| allInOrZero ts waitL |]
            * [| length waitL = wordToNat waitLen |]
            * [| wait <> 0 |] * [| freeable wait (length waitL) |]
          * M.globalInv fs * mallocHeap 0
        POST[_] Ex p', Ex ts', Ex fs', Ex ready', Ex free', Ex wait', Ex waitLen', Ex freeL', Ex waitL',
          [| ts %<= ts' |] * [| fs %<= fs' |] * V "buffer" =?>8 wordToNat (V "size")
          * [| V "fr" %in fs' |]
          * globalSched =*> p' * (p' ==*> ready', free', wait', waitLen')
          * [| ready' %in ts' |]
          * sll freeL' free' * [| allIn fs' freeL' |]
          * files ts' fs' * tqs ts' fs'
          * array waitL' wait' * [| allInOrZero ts' waitL' |]
            * [| length waitL' = wordToNat waitLen' |]
            * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
          * M.globalInv fs' * mallocHeap 0];;

      "fd" <-* "fr";;
      "tq" <-* "fr"+8;;

      Assert [Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
        PRE[V] [| V "tq" %in ts |] * [| V "fr" %in fs |] * V "buffer" =?>8 wordToNat (V "size")
          * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
          * [| ready %in ts |]
          * sll freeL free * [| allIn fs freeL |]
          * files_pick (V "fr") ts fs * tqs ts fs
          * array waitL wait * [| allInOrZero ts waitL |]
            * [| length waitL = wordToNat waitLen |]
            * [| wait <> 0 |] * [| freeable wait (length waitL) |]
          * M.globalInv fs * mallocHeap 0
        POST[_] Ex p', Ex ts', Ex fs', Ex ready', Ex free', Ex wait', Ex waitLen', Ex freeL', Ex waitL',
          [| ts %<= ts' |] * [| fs %<= fs' |] * V "buffer" =?>8 wordToNat (V "size")
          * [| V "fr" %in fs' |]
          * globalSched =*> p' * (p' ==*> ready', free', wait', waitLen')
          * [| ready' %in ts' |]
          * sll freeL' free' * [| allIn fs' freeL' |]
          * files ts' fs' * tqs ts' fs'
          * array waitL' wait' * [| allInOrZero ts' waitL' |]
            * [| length waitL' = wordToNat waitLen' |]
            * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
          * M.globalInv fs' * mallocHeap 0];;

      Note [reveal_files_pick];;

      Call "scheduler"!"block"("tq", "fd", 1)
      [PRE[V] V "buffer" =?>8 wordToNat (V "size")
       POST[_] V "buffer" =?>8 wordToNat (V "size")];;

      "size" <-- Call "sys"!"write"("fd", "buffer", "size")
      [PRE[_] Emp
       POST[_] Emp ];;
      Return "size"
    end with bfunction "accept"("fr", "fd", "tq") [acceptS]
      Note [reveal_files_pick];;

      Assert [Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
        PRE[V] [| V "fr" %in fs |]
          * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
          * [| ready %in ts |]
          * sll freeL free * [| allIn fs freeL |]
          * files_pick (V "fr") ts fs * tqs ts fs
          * array waitL wait * [| allInOrZero ts waitL |]
            * [| length waitL = wordToNat waitLen |]
            * [| wait <> 0 |] * [| freeable wait (length waitL) |]
          * M.globalInv fs * mallocHeap 0
        POST[R] Ex p', Ex ts', Ex fs', Ex fs'', Ex ready', Ex free', Ex wait', Ex waitLen', Ex freeL', Ex waitL',
          [| ts %<= ts' |] * [| fs %<= fs' |] * [| fs' %<= fs'' |]
          * [| V "fr" %in fs'' |] * [| R %in fs'' |]
          * globalSched =*> p' * (p' ==*> ready', free', wait', waitLen')
          * [| ready' %in ts' |]
          * sll freeL' free' * [| allIn fs'' freeL' |]
          * files ts' fs'' * tqs ts' fs''
          * array waitL' wait' * [| allInOrZero ts' waitL' |]
            * [| length waitL' = wordToNat waitLen' |]
            * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
          * M.globalInv fs' * mallocHeap 0];;

      "fd" <-* "fr";;
      "tq" <-* "fr"+4;;

      Assert [Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
        PRE[V] [| V "tq" %in ts |] * [| V "fr" %in fs |]
          * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
          * [| ready %in ts |]
          * sll freeL free * [| allIn fs freeL |]
          * files_pick (V "fr") ts fs * tqs ts fs
          * array waitL wait * [| allInOrZero ts waitL |]
            * [| length waitL = wordToNat waitLen |]
            * [| wait <> 0 |] * [| freeable wait (length waitL) |]
          * M.globalInv fs * mallocHeap 0
        POST[R] Ex p', Ex ts', Ex fs', Ex fs'', Ex ready', Ex free', Ex wait', Ex waitLen', Ex freeL', Ex waitL',
          [| ts %<= ts' |] * [| fs %<= fs' |] * [| fs' %<= fs'' |]
          * [| V "fr" %in fs'' |] * [| R %in fs'' |]
          * globalSched =*> p' * (p' ==*> ready', free', wait', waitLen')
          * [| ready' %in ts' |]
          * sll freeL' free' * [| allIn fs'' freeL' |]
          * files ts' fs'' * tqs ts' fs''
          * array waitL' wait' * [| allInOrZero ts' waitL' |]
            * [| length waitL' = wordToNat waitLen' |]
            * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
          * M.globalInv fs' * mallocHeap 0];;

      Note [reveal_files_pick];;

      Call "scheduler"!"block"("tq", "fd", 0)
      [Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
        PRE[V] [| V "tq" %in ts |] * [| V "fr" %in fs |]
          * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
          * [| ready %in ts |]
          * sll freeL free * [| allIn fs freeL |]
          * files ts fs * tqs ts fs
          * array waitL wait * [| allInOrZero ts waitL |]
            * [| length waitL = wordToNat waitLen |]
            * [| wait <> 0 |] * [| freeable wait (length waitL) |]
          * M.globalInv fs * mallocHeap 0
        POST[R] Ex p', Ex ts', Ex fs', Ex fs'', Ex ready', Ex free', Ex wait', Ex waitLen', Ex freeL', Ex waitL',
          [| ts %<= ts' |] * [| fs %<= fs' |] * [| fs' %<= fs'' |]
          * [| V "fr" %in fs'' |] * [| R %in fs'' |]
          * globalSched =*> p' * (p' ==*> ready', free', wait', waitLen')
          * [| ready' %in ts' |]
          * sll freeL' free' * [| allIn fs'' freeL' |]
          * files ts' fs'' * tqs ts' fs''
          * array waitL' wait' * [| allInOrZero ts' waitL' |]
            * [| length waitL' = wordToNat waitLen' |]
            * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
          * M.globalInv fs' * mallocHeap 0];;

      "fd" <-- Call "sys"!"accept"("fd")
      [Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
        PRE[V] [| V "tq" %in ts |] * [| V "fr" %in fs |]
          * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
          * [| ready %in ts |]
          * sll freeL free * [| allIn fs freeL |]
          * files ts fs * tqs ts fs
          * array waitL wait * [| allInOrZero ts waitL |]
            * [| length waitL = wordToNat waitLen |]
            * [| wait <> 0 |] * [| freeable wait (length waitL) |]
          * M.globalInv fs * mallocHeap 0
        POST[R] Ex p', Ex ts', Ex fs', Ex fs'', Ex ready', Ex free', Ex wait', Ex waitLen', Ex freeL', Ex waitL',
          [| ts %<= ts' |] * [| fs %<= fs' |] * [| fs' %<= fs'' |]
          * [| V "fr" %in fs'' |] * [| R %in fs'' |]
          * globalSched =*> p' * (p' ==*> ready', free', wait', waitLen')
          * [| ready' %in ts' |]
          * sll freeL' free' * [| allIn fs'' freeL' |]
          * files ts' fs'' * tqs ts' fs''
          * array waitL' wait' * [| allInOrZero ts' waitL' |]
            * [| length waitL' = wordToNat waitLen' |]
            * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
          * M.globalInv fs' * mallocHeap 0];;

      "fr" <-- Call "scheduler"!"new"("fd")
      [PRE[_, R] Emp
       POST[R'] [| R' = R |] ];;
      Return "fr"
    end with bfunction "pickNext"("root", "ready", "wait", "waitLen", "blocking", "n") [pickNextS]
      "root" <-* globalSched;;
      "ready" <-* "root";;

      "blocking" <-- Call "threadqs"!"isEmpty"("ready")
      [Al free, Al wait, Al waitLen, Al ts, Al fs, Al waitL,
        PRE[V] globalSched =*> V "root" * (V "root" ==*> V "ready", free, wait, waitLen)
          * tqs ts fs * [| V "ready" %in ts |]
          * array waitL wait * [| allInOrZero ts waitL |]
          * [| length waitL = wordToNat waitLen |]
        POST[R] [| R %in ts |]
          * tqs ts fs * globalSched =*> V "root" * (V "root" ==*> V "ready", free, wait, waitLen)
          * array waitL wait ];;

      "n" <-- Call "sys"!"wait"("blocking")
      [Al free, Al wait, Al waitLen, Al ts, Al waitL,
        PRE[V] globalSched =*> V "root" * (V "root" ==*> V "ready", free, wait, waitLen)
          * [| V "ready" %in ts |]
          * array waitL wait * [| allInOrZero ts waitL |]
          * [| length waitL = wordToNat waitLen |]
        POST[R] [| R %in ts |]
          * globalSched =*> V "root" * (V "root" ==*> V "ready", free, wait, waitLen)
          * array waitL wait ];;

      "wait" <-* "root"+8;;
      "waitLen" <-* "root"+12;;

      If ("n" < "waitLen") {
        Assert [Al free, Al ts, Al waitL,
          PRE[V] globalSched =*> V "root" * (V "root" ==*> V "ready", free, V "wait", V "waitLen")
          * [| V "ready" %in ts |] * [| allInOrZero ts waitL |]
          * array waitL (V "wait") * [| (V "n" < natToW (length waitL))%word |]
        POST[R] [| R %in ts |]
          * globalSched =*> V "root" * (V "root" ==*> V "ready", free, V "wait", V "waitLen")
          * array waitL (V "wait") ];;

        "n" <- 4 * "n";;
        "wait" <-* "wait" + "n";;

        If ("wait" = 0) {
          Call "sys"!"abort"()
          [PREonly[_] [| False |] ]
        } else {
          Return "wait"
        }
      } else {
        Return "ready"
      }
    end with bfunction "new"("fd", "root", "free", "oldFree", "fr", "inq", "outq") [newS]
      "root" <-* globalSched;;
      "free" <-* "root"+4;;

      If ("free" <> 0) {
        "oldFree" <- "free";;
        "fr" <-* "free";;
        "free" <-* "free"+4;;
        "root"+4 *<- "free";;

        Note [reveal_files_pick];;

        Call "malloc"!"free"(0, "oldFree", 2)
        [Al ts, Al fs,
          PRE[V] [| V "fr" %in fs |] * files_pick (V "fr") ts fs
          POST[R] [| R = V "fr" |] * files_pick (V "fr") ts fs];;

        "fr" *<- "fd";;
        Return "fr"
      } else {
        "inq" <-- Call "threadqs"!"alloc"()
        [Al ts, Al fs,
          PRE[V, R] files ts fs * tqs (ts %+ R) fs * mallocHeap 0
          POST[R'] Ex ts', Ex fs', [| R' %in fs' |] * [| ts %+ R %<= ts' |] * [| fs %<= fs' |]
            * files ts' fs' * tqs ts' fs' * mallocHeap 0];;

        "outq" <-- Call "threadqs"!"alloc"()
        [Al ts, Al fs,
          PRE[V, R] files ts fs * tqs (ts %+ V "inq" %+ R) fs * mallocHeap 0
          POST[R'] Ex ts', Ex fs', [| R' %in fs' |] * [| ts %+ V "inq" %+ R %<= ts' |] * [| fs %<= fs' |]
            * files ts' fs' * tqs ts' fs' * mallocHeap 0];;

        "fr" <-- Call "malloc"!"malloc"(0, 3)
        [Al ts, Al fs,
          PRE[V, R] R =?> 3 * files ts fs * tqs (ts %+ V "inq" %+ V "outq") fs
          POST[R'] Ex fs', [| fs %<= fs' |] * [| R' %in fs' |] * files (ts %+ V "inq" %+ V "outq") fs'
            * tqs (ts %+ V "inq" %+ V "outq") fs' ];;

        Note [add_a_file];;

        Assert [Al ts, Al fs,
          PRE[V] V "fr" =?> 3 * files ts fs
          POST[R] [| R = V "fr" |] * files (ts %+ V "inq" %+ V "outq") (fs %+ V "fr") ];;

        "fr" *<- "fd";;
        "fr"+4 *<- "inq";;
        "fr"+8 *<- "outq";;
        Return "fr"
      }
    end with bfunction "declare"("tq", "fd", "mode", "root", "wait", "waitLen", "n", "newWait", "newLen", "i", "j", "v") [declareS]
      "root" <-* globalSched;;
      "wait" <-* "root"+8;;
      "waitLen" <-* "root"+12;;

      "n" <-- Call "sys"!"declare"("fd", "mode")
      [Al ts, Al ready, Al free, Al waitL,
        PRE[V] [| V "tq" %in ts |] * (V "root" ==*> ready, free, V "wait", V "waitLen")
          * array waitL (V "wait") * [| allInOrZero ts waitL |]
          * [| length waitL = wordToNat (V "waitLen") |]
          * [| V "wait" <> 0 |] * [| freeable (V "wait") (length waitL) |]
          * mallocHeap 0
        POST[_] Ex wait', Ex waitLen', Ex waitL',
          (V "root" ==*> ready, free, wait', waitLen')
          * array waitL' wait' * [| allInOrZero ts waitL' |]
          * [| length waitL' = wordToNat waitLen' |]
          * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
          * mallocHeap 0];;

      If ("n" < "waitLen") {
        Assert [Al ts, Al ready, Al free, Al waitL,
          PRE[V] [| V "tq" %in ts |] * (V "root" ==*> ready, free, V "wait", V "waitLen")
            * array waitL (V "wait") * [| allInOrZero ts waitL |]
            * [| length waitL = wordToNat (V "waitLen") |]
            * [| V "wait" <> 0 |] * [| freeable (V "wait") (length waitL) |]
            * [| (V "n" < natToW (length waitL))%word |]
            * mallocHeap 0
          POST[_] Ex wait', Ex waitLen', Ex waitL',
            (V "root" ==*> ready, free, wait', waitLen')
            * array waitL' wait' * [| allInOrZero ts waitL' |]
            * [| length waitL' = wordToNat waitLen' |]
            * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
            * mallocHeap 0];;

        "n" <- 4 * "n";;
        "wait"+"n" *<- "tq";;
        Return 0
      } else {
        "newLen" <- "n" + 1;;

        If ("newLen" < 2) {
          (* This case should be impossible, following the intended API usage. *)
          Call "sys"!"abort"()
          [PREonly[_] [| False |] ]
        } else {
          "newWait" <-- Call "malloc"!"malloc"(0, "newLen")
          [Al ts, Al ready, Al free, Al waitL,
            PRE[V, R] [| V "tq" %in ts |] * (V "root" ==*> ready, free, V "wait", V "waitLen")
              * array waitL (V "wait") * [| allInOrZero ts waitL |]
              * [| length waitL = wordToNat (V "waitLen") |]
              * [| V "wait" <> 0 |] * [| freeable (V "wait") (length waitL) |]
              * R =?> wordToNat (V "newLen") * [| R <> 0 |] * [| freeable R (wordToNat (V "newLen")) |]
              * mallocHeap 0
            POST[_] Ex wait', Ex waitLen', Ex waitL',
              (V "root" ==*> ready, free, wait', waitLen')
              * array waitL' wait' * [| allInOrZero ts waitL' |]
              * [| length waitL' = wordToNat waitLen' |]
              * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
              * mallocHeap 0];;

          Note [make_array];;

          Assert [Al ts, Al ready, Al free, Al waitL, Al newL,
            PRE[V] [| V "tq" %in ts |] * (V "root" ==*> ready, free, V "wait", V "waitLen")
              * array waitL (V "wait") * [| allInOrZero ts waitL |]
              * [| length waitL = wordToNat (V "waitLen") |]
              * [| V "wait" <> 0 |] * [| freeable (V "wait") (length waitL) |]
              * array newL (V "newWait") * [| length newL = wordToNat (V "newLen") |]
              * [| V "newWait" <> 0 |] * [| freeable (V "newWait") (wordToNat (V "newLen")) |]
              * mallocHeap 0
            POST[_] Ex wait', Ex waitLen', Ex waitL',
              (V "root" ==*> ready, free, wait', waitLen')
              * array waitL' wait' * [| allInOrZero ts waitL' |]
              * [| length waitL' = wordToNat waitLen' |]
              * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
              * mallocHeap 0];;

          "i" <- 0;;
          [Al ts, Al ready, Al free, Al waitL, Al waitL',
            PRE[V] [| V "tq" %in ts |] * (V "root" ==*> ready, free, V "wait", V "waitLen")
              * array waitL (V "wait") * [| allInOrZero ts waitL |]
              * [| length waitL = wordToNat (V "waitLen") |]
              * [| V "wait" <> 0 |] * [| freeable (V "wait") (length waitL) |]
              * array waitL' (V "newWait") * [| length waitL' = wordToNat (V "newLen") |]
              * [| V "newWait" <> 0 |] * [| freeable (V "newWait") (wordToNat (V "newLen")) |]
              * [| allInOrZero ts (firstn (wordToNat (V "i")) waitL') |]
              * mallocHeap 0 * [| (V "i" <= V "newLen")%word |]
            POST[_] Ex wait', Ex waitLen', Ex waitL',
              (V "root" ==*> ready, free, wait', waitLen')
              * array waitL' wait' * [| allInOrZero ts waitL' |]
              * [| length waitL' = wordToNat waitLen' |]
              * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
              * mallocHeap 0]
          While ("i" < "newLen") {
            If ("i" = "n") {
              "v" <- "tq"
            } else {
              If ("i" < "waitLen") {
                Assert [Al ts, Al ready, Al free, Al waitL, Al waitL',
                  PRE[V] [| V "tq" %in ts |] * (V "root" ==*> ready, free, V "wait", V "waitLen")
                    * array waitL (V "wait") * [| allInOrZero ts waitL |]
                    * [| length waitL = wordToNat (V "waitLen") |]
                    * [| V "wait" <> 0 |] * [| freeable (V "wait") (length waitL) |]
                    * array waitL' (V "newWait") * [| length waitL' = wordToNat (V "newLen") |]
                    * [| V "newWait" <> 0 |] * [| freeable (V "newWait") (wordToNat (V "newLen")) |]
                    * [| allInOrZero ts (firstn (wordToNat (V "i")) waitL') |]
                    * [| (V "i" < natToW (length waitL'))%word |]
                    * [| (V "i" < natToW (length waitL))%word |]
                    * mallocHeap 0
                  POST[_] Ex wait', Ex waitLen', Ex waitL',
                    (V "root" ==*> ready, free, wait', waitLen')
                    * array waitL' wait' * [| allInOrZero ts waitL' |]
                    * [| length waitL' = wordToNat waitLen' |]
                    * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
                    * mallocHeap 0];;
                "j" <- 4 * "i";;
                "v" <-* "wait" + "j"
              } else {
                "v" <- 0
              }
            };;

            Assert [Al ts, Al ready, Al free, Al waitL, Al waitL',
              PRE[V] [| V "tq" %in ts |] * (V "root" ==*> ready, free, V "wait", V "waitLen")
                * array waitL (V "wait") * [| allInOrZero ts waitL |]
                * [| length waitL = wordToNat (V "waitLen") |]
                * [| V "wait" <> 0 |] * [| freeable (V "wait") (length waitL) |]
                * array waitL' (V "newWait") * [| length waitL' = wordToNat (V "newLen") |]
                * [| V "newWait" <> 0 |] * [| freeable (V "newWait") (wordToNat (V "newLen")) |]
                * [| allInOrZero ts (firstn (wordToNat (V "i")) waitL') |]
                * [| (V "i" < natToW (length waitL'))%word |]
                * [| V "v" = $0 \/ V "v" %in ts |]
                * mallocHeap 0
              POST[_] Ex wait', Ex waitLen', Ex waitL',
                (V "root" ==*> ready, free, wait', waitLen')
                * array waitL' wait' * [| allInOrZero ts waitL' |]
                * [| length waitL' = wordToNat waitLen' |]
                * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
                * mallocHeap 0];;

            "j" <- 4 * "i";;
            "newWait" + "j" *<- "v";;
            "i" <- "i" + 1
          };;

          Note [dissolve_array];;

          Assert [Al ts, Al ready, Al free, Al newL,
            PRE[V] [| V "tq" %in ts |] * (V "root" ==*> ready, free, V "wait", V "waitLen")
              * V "wait" =?> wordToNat (V "waitLen")
              * [| V "wait" <> 0 |] * [| freeable (V "wait") (wordToNat (V "waitLen")) |]
              * array newL (V "newWait") * [| length newL = wordToNat (V "newLen") |]
              * [| V "newWait" <> 0 |] * [| freeable (V "newWait") (wordToNat (V "newLen")) |]
              * [| allInOrZero ts newL |]
              * mallocHeap 0
            POST[_] Ex wait', Ex waitLen', Ex waitL',
              (V "root" ==*> ready, free, wait', waitLen')
              * array waitL' wait' * [| allInOrZero ts waitL' |]
              * [| length waitL' = wordToNat waitLen' |]
              * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
              * mallocHeap 0];;

          Call "malloc"!"free"(0, "wait", "waitLen")
          [Al ready, Al free,
            PRE[V] mallocHeap 0 * (V "root" ==*> ready, free, V "wait", V "waitLen")
            POST[_] mallocHeap 0 * (V "root" ==*> ready, free, V "newWait", V "newLen")];;

          "root"+8 *<- "newWait";;
          "root"+12 *<- "newLen";;
          Return 0
        }
      }
    end with bfunction "block"("tq", "fd", "mode", "tmp") [blockS]
       "tmp" <-- Call "threadqs"!"isEmpty"("tq")
       [Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
         PRE[V] [| V "tq" %in ts |]
           * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
           * [| ready %in ts |]
           * sll freeL free * [| allIn fs freeL |]
           * files ts fs * tqs ts fs
           * array waitL wait * [| allInOrZero ts waitL |]
             * [| length waitL = wordToNat waitLen |]
             * [| wait <> 0 |] * [| freeable wait (length waitL) |]
           * M.globalInv fs * mallocHeap 0
         POST[_] Ex p', Ex ts', Ex fs', Ex ready', Ex free', Ex wait', Ex waitLen', Ex freeL', Ex waitL',
           [| ts %<= ts' |] * [| fs %<= fs' |]
           * globalSched =*> p' * (p' ==*> ready', free', wait', waitLen')
           * [| ready' %in ts' |]
           * sll freeL' free' * [| allIn fs' freeL' |]
           * files ts' fs' * tqs ts' fs'
           * array waitL' wait' * [| allInOrZero ts' waitL' |]
             * [| length waitL' = wordToNat waitLen' |]
             * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
           * M.globalInv fs' * mallocHeap 0];;

       If ("tmp" = 1) {
         Call "scheduler"!"declare"("tq", "fd", "mode")
         [Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
         PRE[V] [| V "tq" %in ts |]
           * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
           * [| ready %in ts |]
           * sll freeL free * [| allIn fs freeL |]
           * files ts fs * tqs ts fs
           * array waitL wait * [| allInOrZero ts waitL |]
             * [| length waitL = wordToNat waitLen |]
             * [| wait <> 0 |] * [| freeable wait (length waitL) |]
           * M.globalInv fs * mallocHeap 0
         POST[_] Ex p', Ex ts', Ex fs', Ex ready', Ex free', Ex wait', Ex waitLen', Ex freeL', Ex waitL',
           [| ts %<= ts' |] * [| fs %<= fs' |]
           * globalSched =*> p' * (p' ==*> ready', free', wait', waitLen')
           * [| ready' %in ts' |]
           * sll freeL' free' * [| allIn fs' freeL' |]
           * files ts' fs' * tqs ts' fs'
           * array waitL' wait' * [| allInOrZero ts' waitL' |]
             * [| length waitL' = wordToNat waitLen' |]
             * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
           * M.globalInv fs' * mallocHeap 0]
       } else {
         Skip
       };;

       "tmp" <-- Call "scheduler"!"pickNext"()
       [Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al freeL, Al waitL,
         PRE[V, R] [| V "tq" %in ts |] * [| R %in ts |]
           * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
           * [| ready %in ts |]
           * sll freeL free * [| allIn fs freeL |]
           * files ts fs * tqs ts fs
           * array waitL wait * [| allInOrZero ts waitL |]
             * [| length waitL = wordToNat waitLen |]
             * [| wait <> 0 |] * [| freeable wait (length waitL) |]
           * M.globalInv fs * mallocHeap 0
         POST[_] Ex p', Ex ts', Ex fs', Ex ready', Ex free', Ex wait', Ex waitLen', Ex freeL', Ex waitL',
           [| ts %<= ts' |] * [| fs %<= fs' |]
           * globalSched =*> p' * (p' ==*> ready', free', wait', waitLen')
           * [| ready' %in ts' |]
           * sll freeL' free' * [| allIn fs' freeL' |]
           * files ts' fs' * tqs ts' fs'
           * array waitL' wait' * [| allInOrZero ts' waitL' |]
             * [| length waitL' = wordToNat waitLen' |]
             * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
           * M.globalInv fs' * mallocHeap 0];;

       Call "threadqs"!"yield"("tq", "tmp")
       [Al ts, Al fs, Al p, Al ready, Al free, Al wait, Al waitLen, Al waitL,
         PRE[V] [| V "tq" %in ts |]
           * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
           * array waitL wait * [| allInOrZero ts waitL |]
             * [| length waitL = wordToNat waitLen |]
             * [| wait <> 0 |] * [| freeable wait (length waitL) |]
           * tqs ts fs * mallocHeap 0
         POST[_] Ex wait', Ex waitLen', Ex waitL',
           globalSched =*> p * (p ==*> ready, free, wait', waitLen')
           * array waitL' wait' * [| allInOrZero ts waitL' |]
             * [| length waitL' = wordToNat waitLen' |]
             * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
           * tqs ts fs * mallocHeap 0];;

       "tmp" <-- Call "threadqs"!"isEmpty"("tq")
       [Al ts, Al p, Al ready, Al free, Al wait, Al waitLen, Al waitL,
         PRE[V] [| V "tq" %in ts |]
           * globalSched =*> p * (p ==*> ready, free, wait, waitLen)
           * array waitL wait * [| allInOrZero ts waitL |]
             * [| length waitL = wordToNat waitLen |]
             * [| wait <> 0 |] * [| freeable wait (length waitL) |]
           * mallocHeap 0
         POST[_] Ex wait', Ex waitLen', Ex waitL',
           globalSched =*> p * (p ==*> ready, free, wait', waitLen')
           * array waitL' wait' * [| allInOrZero ts waitL' |]
             * [| length waitL' = wordToNat waitLen' |]
             * [| wait' <> 0 |] * [| freeable wait' (length waitL') |]
           * mallocHeap 0];;

       If ("tmp" = 0) {
         Call "scheduler"!"declare"("tq", "fd", "mode")
         [PRE[_] Emp POST[_] Emp]
       } else {
         Skip
       };;

       Return 0
    end
  }}.

Ltac finish := auto;
  try solve [ fold (@length W) in *; try rewrite initSize_eq in *;
    repeat match goal with
             | [ H : length _ = _ |- _ ] => rewrite H
           end; reflexivity || eauto 2;
  fold (@firstn W) in *; autorewrite with sepFormula; eauto 2 ].

Lemma selN_updN_eq : forall v a n,
  (n < length a)%nat
  -> Array.selN (Array.updN a n v) n = v.
  induction a; destruct n; simpl; intuition.
Qed.

Lemma selN_upd_eq : forall v a n,
  (n < length a)%nat
  -> goodSize (length a)
  -> Array.selN (Array.upd a (natToW n) v) n = v.
  intros; rewrite upd_updN.
  apply selN_updN_eq; auto.
  eauto using goodSize_weaken.
Qed.

Local Hint Extern 1 (selN _ _ = _) => apply selN_upd_eq; solve [ finish ].

Ltac t' := unfold globalInv; sep hints; finish.

Ltac spawn := post; evaluate hints;
  match goal with
    | [ H : interp _ _ |- _ ] =>
      toFront ltac:(fun P => match P with
                               | starting _ _ => idtac
                             end) H; apply starting_elim in H; post; descend
  end;
  try (toFront_conc ltac:(fun P => match P with
                                     | Q'.starting _ _ _ _ => idtac
                                   end); apply other_starting_intro; descend;
  try match goal with
        | [ |- interp _ (![ _ ] _) ] => step hints
      end);
  (try (repeat (apply andL; apply injL; intro);
    match goal with
      | [ H : forall stn_st : ST.settings * state, _ |- _ ] =>
        eapply Imply_trans; [ | apply H ]; clear H
    end); t').


Lemma breakout : forall A (P : A -> _) Q R x specs,
  (forall v, interp specs (![P v * Q] x ---> R)%PropX)
  -> interp specs (![exB P * Q] x ---> R)%PropX.
  rewrite sepFormula_eq; propxFo.
  unfold sepFormula_def, exB, ex.
  simpl.
  repeat (apply existsL; intros); step auto_ext.
  apply unandL.
  eapply Imply_trans; try apply H; clear H.
  do 2 eapply existsR.
  simpl.
  repeat apply andR.
  apply injR; eauto.
  apply andL; apply implyR.
  apply Imply_refl.
  apply andL; apply swap; apply implyR.
  apply Imply_refl.
Qed.

Ltac exBegone :=
  match goal with
    | [ |- interp ?specs (![ ?P ] ?x ---> ?Q)%PropX ] =>
      toFront' ltac:(fun R => match R with
                                | exB _ => idtac
                              end) P
      ltac:(fun it P' =>
        apply Imply_trans with (![ it * P'] x)%PropX; [ step auto_ext | ])
  end; repeat match goal with
                | [ |- interp _ (![ exB _ * _] _ ---> _)%PropX ] => apply breakout; intro
              end.

Lemma tqs_weaken : forall ts fs fs',
  fs %<= fs'
  -> tqs ts fs ===>* tqs ts fs'.
  rewrite tqs_eq; intros; apply tqs'_weaken; hnf; intuition.
Qed.

Ltac t := solve [
  match goal with
    | [ |- context[starting] ] =>
      match goal with
        | [ |- context[Q'.starting] ] => spawn
      end
    | [ |- context[evolve] ] =>
      unfold globalInv; post; evaluate hints; descend; [ step hints | step hints | ];
        descend; step hints;
        repeat ((apply andL; apply injL) || apply existsL; intro); descend;
          exBegone; t'
    | [ |- context[add_a_file] ] =>
      post; evaluate hints;
      match goal with
        | [ H : context[upd _ "fr" ?V] |- _ ] =>
          match type of H with
            | context[files _ ?B] =>
              toFront ltac:(fun P => match P with
                                       | tqs _ _ => idtac
                                     end) H;
              eapply use_HimpWeak in H; [ | apply (tqs_weaken _ _ (B %+ V)) ]; [ t | finish ]
          end
      end
    | [ |- context[reveal_files_pick] ] => unfold files_pick; t'
    | _ => t'
  end ].

Local Hint Extern 1 (@eq W _ _) => words.
Local Hint Immediate evolve_refl.

Hint Rewrite upd_length : sepFormula.

Local Hint Extern 1 (allInOrZero _ nil) => constructor.
Local Hint Extern 1 (allInOrZero _ (_ :: _)) => constructor.

Local Hint Extern 1 (allIn empty _) => constructor.

Local Hint Extern 1 (allInOrZero _ (Array.upd _ (natToW 1) (natToW 0))) =>
  hnf; rewrite upd_updN by auto;
    repeat match goal with
             | [ ls : list W |- _ ] =>
               match goal with
                 | [ _ : length ?E = _ |- _ ] =>
                   match E with
                     | context[ls] => destruct ls; try discriminate
                   end
               end
           end; simpl in *.

Local Hint Extern 1 (freeable _ _) => congruence.
Local Hint Extern 1 (himp _ _ (sll nil (natToW 0))) => solve [ step hints ].

Lemma length_ok : forall u v n,
  u < v
  -> n = wordToNat v
  -> u < natToW n.
  intros; subst; unfold natToW; rewrite natToWord_wordToNat; auto.
Qed.

Local Hint Immediate length_ok.

Lemma selN_In : forall ls n,
  (n < length ls)%nat
  -> In (Array.selN ls n) ls.
  induction ls; destruct n; simpl; intuition.
Qed.

Lemma sel_In : forall ls n,
  n < natToW (length ls)
  -> goodSize (length ls)
  -> In (Array.sel ls n) ls.
  unfold Array.sel; intros; apply selN_In; nomega.
Qed.    

Lemma found_queue : forall x ls i b,
  x = Array.sel ls i
  -> Array.sel ls i <> 0
  -> allInOrZero b ls
  -> i < natToW (length ls)
  -> goodSize (length ls)
  -> x %in b.
  intros; subst.
  eapply Forall_forall in H1; [ | eauto using sel_In ].
  tauto.
Qed.

Local Hint Extern 1 (_ %in _) =>
  eapply found_queue; [ eassumption | eassumption | eassumption | eassumption | eauto ].

Lemma allIn_monotone : forall b ls b',
  allIn b ls
  -> b %<= b'
  -> allIn b' ls.
  intros; eapply Forall_weaken; eauto.
  bags.
  specialize (H0 x); omega.
Qed.

Local Hint Immediate allIn_monotone.

Lemma allIn_hd : forall b x ls,
  allIn b (x :: ls)
  -> x %in b.
  inversion 1; auto.
Qed.

Lemma allIn_tl : forall b x ls,
  allIn b (x :: ls)
  -> allIn b ls.
  inversion 1; auto.
Qed.

Local Hint Immediate allIn_hd allIn_tl.

Lemma add_incl : forall a b x,
  a %+ x %<= b
  -> a %<= b.
  bags.
  specialize (H x0).
  destruct (W_Key.eq_dec x0 x); auto.
Qed.

Local Hint Immediate add_incl.

Local Hint Extern 1 (himp _ (files _ _) (files _ _)) => apply starB_weaken; solve [ sepLemma ].

Lemma allInOrZero_monotone : forall b ls b',
  allInOrZero b ls
  -> b %<= b'
  -> allInOrZero b' ls.
  intros; eapply Forall_weaken; [ | eauto ].
  bags.
  specialize (H0 x); omega.
Qed.

Local Hint Immediate allInOrZero_monotone.

Lemma allIn_cons : forall b x ls,
  allIn b ls
  -> x %in b
  -> allIn b (x :: ls).
  constructor; auto.
Qed.

Local Hint Immediate allIn_cons.

Lemma allInOrZero_updN : forall b v ls,
  allInOrZero b ls
  -> forall i, v %in b
    -> allInOrZero b (Array.updN ls i v).
  induction 1; destruct i; simpl; intuition;
    constructor; auto; apply IHForall; auto.
Qed.    

Lemma allInOrZero_upd : forall b ls i v,
  allInOrZero b ls
  -> v %in b
  -> allInOrZero b (Array.upd ls i v).
  intros; apply allInOrZero_updN; auto.
Qed.

Local Hint Immediate allInOrZero_upd.

Hint Rewrite roundTrip_0 : N.

Lemma zero_le : forall w : W, natToW 0 <= w.
  intros; nomega.
Qed.

Local Hint Immediate zero_le.

Lemma firstn_advance' : forall v n ls,
  (n < length ls)%nat
  -> firstn (n + 1) (Array.updN ls n v) = firstn n ls ++ v :: nil.
  induction n; destruct ls; simpl; intuition.
  rewrite IHn; auto.
Qed.

Lemma firstn_advance : forall ls w v,
  w < natToW (length ls)
  -> goodSize (length ls)
  -> firstn (wordToNat w + 1) (Array.upd ls w v) = firstn (wordToNat w) ls ++ v :: nil.
  unfold Array.upd; intros; apply firstn_advance'; nomega.
Qed.

Lemma allInOrZero_advance : forall b w ls (v : W),
  allInOrZero b (firstn (wordToNat w) ls)
  -> v = 0 \/ v %in b
  -> w < natToW (length ls)
  -> goodSize (length ls)
  -> allInOrZero b (firstn (wordToNat (w ^+ natToW 1)) (Array.upd ls w v)).
  intros.
  erewrite <- next; eauto.
  rewrite firstn_advance; auto; apply Forall_app; auto.
Qed.

Local Hint Extern 1 (allInOrZero _ (firstn (wordToNat (_ ^+ _)) _)) =>
  solve [ apply allInOrZero_advance; auto; [ eauto 10 ] ].

Lemma inc : forall n (w : W) l,
  n = wordToNat l
  -> w < natToW n
  -> w ^+ natToW 1 <= l.
  intros; subst.
  assert (exists b, w < b) by eauto.
  pre_nomega.
  destruct H.
  erewrite <- next; eauto.
  unfold natToW in *; rewrite natToWord_wordToNat in *.
  auto.
Qed.  

Local Hint Immediate inc.

Theorem natToW_wordToNat : forall w : W,
  natToW (wordToNat w) = w.
  intros; apply natToWord_wordToNat.
Qed.

Hint Rewrite natToW_wordToNat : sepFormula.

Lemma allInOrZero_delivers : forall b ls i,
  allInOrZero b ls
  -> i < natToW (length ls)
  -> goodSize (length ls)
  -> Array.sel ls i = natToW 0 \/ Array.sel ls i %in b.
  intros ? ? ? H ? ?; eapply Forall_forall in H; eauto; apply sel_In; auto.
Qed.

Local Hint Extern 1 (_ \/ _) => solve [ apply allInOrZero_delivers; auto; [ eauto 10 ] ].

Lemma firstn_length : forall A (ls : list A),
  firstn (length ls) ls = ls.
  induction ls; simpl; intuition.
Qed.

Lemma wordToNat_inj : forall sz (u v : word sz),
  wordToNat u = wordToNat v
  -> u = v.
  intros; rewrite <- (natToWord_wordToNat u); rewrite <- (natToWord_wordToNat v); congruence.
Qed.

Lemma allInOrZero_done : forall b (i : W) ls l,
  allInOrZero b (firstn (wordToNat i) ls)
  -> l <= i
  -> i <= l
  -> length ls = wordToNat l
  -> allInOrZero b ls.
  intros; replace i with l in *.
  rewrite <- H2 in *; rewrite firstn_length in *; assumption.
  apply wordToNat_inj; nomega.
Qed.

Local Hint Immediate allInOrZero_done.

Ltac u := abstract t.

Theorem ok : moduleOk m.
  vcgen.

  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u
.  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
  u.
Qed.

Transparent initSize.

End Make.
