Require Import List.
Require Import MirrorShard.DepList.
Require Import MirrorShard.Expr MirrorShard.SepExpr MirrorShard.SepCancel.
Require Import MirrorShard.Prover.
Require Import MirrorShard.Tactics MirrorShard.Reflection.
Require Import MirrorShard.ExprUnify.

Require Import PropX.
Require Import TacPackIL ILEnv.
Require Import IL SepIL.
Require Import Word Memory.
Require Import SymILTac CancelTacIL.

Set Implicit Arguments.
Set Strict Implicit.

(*TIME
Add Rec LoadPath "/usr/local/lib/coq/user-contrib/" as Timing.  
Add ML Path "/usr/local/lib/coq/user-contrib/". 
Declare ML Module "Timing_plugin".
*)

(** isConst **)
(*************)

Ltac isConst_bool e :=
  match e with
    | true => true
    | false => true
    | _ => false
  end.

Ltac isConst e :=
  match e with
    | 0 => true
    | S ?e => isConst e
    | Rp => true
    | Rv => true
    | Sp => true
    | String.EmptyString => true
    | String.String ?e1 ?e2 =>
      match isConst e1 with
        | true => isConst e2
        | _ => false
      end
    | Ascii.Ascii ?a ?b ?c ?d ?e ?f ?g ?h =>
      match isConst_bool a with
        | true =>
          match isConst_bool b with
            | true =>
              match isConst_bool c with
                | true =>
                  match isConst_bool d with
                    | true =>
                      match isConst_bool e with
                        | true =>
                          match isConst_bool f with
                            | true =>
                              match isConst_bool g with
                                | true =>
                                  match isConst_bool h with
                                    | true => true
                                    | _ => false
                                  end
                                | _ => false
                              end
                            | _ => false
                          end
                        | _ => false
                      end
                    | _ => false
                  end
                | _ => false
              end
            | _ => false
          end
        | _ => false
      end
    | _ => false
  end.

(** Should reflect **)
(** TODO: This is probably deprecated **)
Ltac reflectable shouldReflect P :=
  match P with
    | @PropX.interp _ _ _ _ => false
    | @PropX.valid _ _ _ _ _ => false
    | forall x, _ => false
    | context [ PropX.PropX _ _ ] => false
    | context [ PropX.spec _ _ ] => false
    | _ => match type of P with
             | Prop => shouldReflect P
           end
  end.

Ltac shouldReflect P :=
  match P with
    | evalInstrs _ _ _ = _ => false
    | Structured.evalCond _ _ _ _ _ = _ => false
    | @PropX.interp _ _ _ _ => false
    | @PropX.valid _ _ _ _ _ => false
    | @eq ?X _ _ => 
      match X with
        | context [ PropX.PropX ] => false
        | context [ PropX.spec ] => false
      end
    | forall x, _ => false
    | exists x, _ => false
    | _ => true
  end.

(** Reduce Repr **)
Ltac reduce_repr ext sym ls :=
  match sym with
    | tt =>
      eval cbv beta iota zeta delta [ 
        ext
        Env.repr_combine Env.listToRepr Env.listOptToRepr Env.nil_Repr
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
        ILAlgoTypes.PACK.applyTypes
        ILAlgoTypes.PACK.applyFuncs
        ILAlgoTypes.PACK.applyPreds
        List.tl List.hd List.map Env.repr
        ILAlgoTypes.PACK.CE.core
        bedrock_types_r bedrock_funcs_r
        TacPackIL.ILAlgoTypes.Env
        BedrockCoreEnv.core 
      ] in ls
    | tt =>
      eval cbv beta iota zeta delta [ 
        Env.repr_combine Env.listToRepr Env.listOptToRepr Env.nil_Repr
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
        ILAlgoTypes.PACK.applyTypes
        ILAlgoTypes.PACK.applyFuncs
        ILAlgoTypes.PACK.applyPreds
        List.tl List.hd List.map Env.repr
        ILAlgoTypes.PACK.CE.core
        bedrock_types_r bedrock_funcs_r
        TacPackIL.ILAlgoTypes.Env
        BedrockCoreEnv.core 
      ] in ls
    | _ => 
      eval cbv beta iota zeta delta [
        sym ext
        Env.repr_combine Env.listToRepr Env.listOptToRepr Env.nil_Repr
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
        ILAlgoTypes.PACK.applyTypes
        ILAlgoTypes.PACK.applyFuncs
        ILAlgoTypes.PACK.applyPreds
        List.tl List.hd List.map Env.repr
        ILAlgoTypes.PACK.CE.core
        bedrock_types_r bedrock_funcs_r
        TacPackIL.ILAlgoTypes.Env
        BedrockCoreEnv.core 
      ] in ls
    | _ => 
      eval cbv beta iota zeta delta [
        sym
        Env.repr_combine Env.listToRepr Env.listOptToRepr Env.nil_Repr
        ILAlgoTypes.PACK.Types ILAlgoTypes.PACK.Funcs ILAlgoTypes.PACK.Preds
        ILAlgoTypes.PACK.applyTypes
        ILAlgoTypes.PACK.applyFuncs
        ILAlgoTypes.PACK.applyPreds
        List.tl List.hd List.map Env.repr
        ILAlgoTypes.PACK.CE.core
        bedrock_types_r bedrock_funcs_r
        TacPackIL.ILAlgoTypes.Env
        BedrockCoreEnv.core 
      ] in ls
  end.

(** Cancellation **)
(******************)
Section canceller.
  Variable ts : list type.
  Let types := Env.repr BedrockCoreEnv.core ts.

  Require Import MirrorShard.Provers.
  Require Import Bool.

  Parameter checkTypes_funcs : tfunctions -> functions types -> bool.

  Parameter checkTypes_preds : SEP.tpredicates -> SEP.predicates types -> bool.

  Parameter checkTypes_env : tenv -> env types -> bool.

(*
  Definition checkTypes_funcs : tfunctions -> functions types -> bool :=
    Folds.all2 (fun t f => andb (eq_dec (TDomain t) (Domain f)) (eq_dec (TRange t) (Range f))).

  Definition checkTypes_preds : SEP.tpredicates -> SEP.predicates types -> bool :=
    Folds.all2 (fun t f => andb (eq_dec (TDomain t) (Domain f)) (eq_dec (TRange t) (Range f))).
*)

  Require Import Localize.Localize.


  Goal forall ts : list type,
       SEP.tpredicates ->
       ProverT ts ->
       UNF.hintSide ts ->
       UNF.hintSide ts ->
       nat ->
       exprs ts ->
       list tvar ->
       list tvar ->
       SEP.sexpr ts -> SEP.sexpr ts -> CANCEL_LOOP.cancelResult ts * bool.
    refine ((let H := fun elt : Type => SepHeap.FM.Raw.Leaf elt in
 let H0 := NatMap.IntMap.Raw.Proofs.empty_bst in
 let H1 :=
   fun elt : Type =>
   {| Unfolder.FM.this := H elt; Unfolder.FM.is_bst := H0 elt |} in
 let H2 := fun T : Type => H1 (list T) in
 let H3 := fun types : list type => list (expr types) in
 let H4 := word 32 in
 let H5 := H4 in
 let H6 := (settings * state)%type in
 let H7 := fun sos : list Type => settings -> smem -> propX H5 H6 sos in
 let H8 := H7 (@nil Type) in
 let H9 := H8 in
 let H10 :=
   fun types : list type =>
   {|
   SH.impures := H2 (H3 types);
   SH.pures := @nil (expr types);
   SH.other := @nil H9 |} in
 let H11 :=
   fun A : Type =>
   fix length (l : list A) : nat :=
     match l with
     | nil => 0
     | _ :: l' => S (length l')
     end in
 let H12 :=
   fun A : Type =>
   fix app (l m : list A) {struct l} : list A :=
     match l with
     | nil => m
     | a :: l1 => a :: app l1 m
     end in
 let H13 :=
   fun elt : Type =>
   fix fold (A : Type) (f : SepHeap.FM.Raw.key -> elt -> A -> A)
            (m : SepHeap.FM.Raw.tree elt) (a : A) {struct m} : A :=
     match m with
     | SepHeap.FM.Raw.Leaf => a
     | SepHeap.FM.Raw.Node l x d r _ => fold A f r (f x d (fold A f l a))
     end in
 let H14 :=
   fun (elt : Type) (b : SepHeap.FM.bst elt) => let (this, _) := b in this in
 let H15 :=
   fun (elt A : Type) (f : SepHeap.FM.key -> elt -> A -> A)
     (m : SepHeap.FM.t elt) (i : A) => H13 elt A f (H14 elt m) i in
 let H16 := SepHeap.FM.bst in
 let H17 := fun T : Type => H16 (list T) in
 let H18 :=
   fix nat_compare (n m : nat) {struct n} : comparison :=
     match n with
     | 0 => match m with
            | 0 => Datatypes.Eq
            | S _ => Datatypes.Lt
            end
     | S n' =>
         match m with
         | 0 => Datatypes.Gt
         | S m' => nat_compare n' m'
         end
     end in
 let H19 := fun n m : nat => (S n <= m)%nat in
 let H20 := H19 in
 let H21 := @eq nat in
 let H22 :=
   fun x y : NatMap.Ordered_nat.t =>
   match
     H18 x y as r
     return
       (Compare_dec.nat_compare x y = r ->
        @OrderedType.Compare nat NatMap.Ordered_nat.lt NatMap.Ordered_nat.eq
          x y)
   with
   | Datatypes.Eq =>
       fun pf : Compare_dec.nat_compare x y = Datatypes.Eq =>
       @OrderedType.EQ nat H20 H21 x y (Compare_dec.nat_compare_eq x y pf)
   | Datatypes.Lt =>
       fun pf : Compare_dec.nat_compare x y = Datatypes.Lt =>
       @OrderedType.LT nat H20 H21 x y (Compare_dec.nat_compare_Lt_lt x y pf)
   | Datatypes.Gt =>
       fun pf : Compare_dec.nat_compare x y = Datatypes.Gt =>
       @OrderedType.GT nat H20 H21 x y (Compare_dec.nat_compare_Gt_gt x y pf)
   end (@eq_refl comparison (H18 x y)) in
 let H23 :=
   fun elt : Type =>
   fix find (x : nat) (m : SepHeap.FM.Raw.tree elt) {struct m} :
     option elt :=
     match m with
     | SepHeap.FM.Raw.Leaf => @None elt
     | SepHeap.FM.Raw.Node l y d r _ =>
         match H22 x y with
         | OrderedType.LT _ => find x l
         | OrderedType.EQ _ => @Some elt d
         | OrderedType.GT _ => find x r
         end
     end in
 let H24 :=
   fun (elt : Type) (x : SepHeap.FM.key) (m : SepHeap.FM.t elt) =>
   H23 elt x (H14 elt m) in
 let H25 := BinNums.Zpos 1 in
 let H26 := BinNums.Z0 in
 let H27 :=
   fun (elt : Type) (m : SepHeap.FM.Raw.tree elt) =>
   match m with
   | SepHeap.FM.Raw.Leaf => H26
   | SepHeap.FM.Raw.Node _ _ _ _ h => h
   end in
 let H28 :=
   fix compare_cont (x y : BinNums.positive) (r : comparison) {struct y} :
     comparison :=
     match x with
     | BinNums.xI p =>
         match y with
         | BinNums.xI q => compare_cont p q r
         | BinNums.xO q => compare_cont p q Datatypes.Gt
         | BinNums.xH => Datatypes.Gt
         end
     | BinNums.xO p =>
         match y with
         | BinNums.xI q => compare_cont p q Datatypes.Lt
         | BinNums.xO q => compare_cont p q r
         | BinNums.xH => Datatypes.Gt
         end
     | BinNums.xH =>
         match y with
         | BinNums.xI _ => Datatypes.Lt
         | BinNums.xO _ => Datatypes.Lt
         | BinNums.xH => r
         end
     end in
 let H29 := fun x y : BinNums.positive => H28 x y Datatypes.Eq in
 let H30 :=
   fun r : comparison =>
   match r with
   | Datatypes.Eq => Datatypes.Eq
   | Datatypes.Lt => Datatypes.Gt
   | Datatypes.Gt => Datatypes.Lt
   end in
 let H31 :=
   fun x y : BinNums.Z =>
   match x with
   | BinNums.Z0 =>
       match y with
       | BinNums.Z0 => Datatypes.Eq
       | BinNums.Zpos _ => Datatypes.Lt
       | BinNums.Zneg _ => Datatypes.Gt
       end
   | BinNums.Zpos x' =>
       match y with
       | BinNums.Z0 => Datatypes.Gt
       | BinNums.Zpos y' => H29 x' y'
       | BinNums.Zneg _ => Datatypes.Gt
       end
   | BinNums.Zneg x' =>
       match y with
       | BinNums.Z0 => Datatypes.Lt
       | BinNums.Zpos _ => Datatypes.Lt
       | BinNums.Zneg y' => H30 (H29 x' y')
       end
   end in
 let H32 := fun A : Prop => A -> False in
 let H33 := fun (P : Type) (f : False) => match f return P with
                                          end in
 let H34 := fun P : Prop => H33 P in
 let H35 :=
   fun (A : Type) (x : A) (P : A -> Type) (f : P x) (y : A) (e : x = y) =>
   match e in (_ = y0) return (P y0) with
   | eq_refl => f
   end in
 let H36 := fun (A : Type) (x : A) (P : A -> Prop) => H35 A x P in
 let H37 :=
   fun x y : BinNums.Z =>
   match H31 x y as c return ({c = Datatypes.Gt} + {c <> Datatypes.Gt}) with
   | Datatypes.Eq =>
       @right (Datatypes.Eq = Datatypes.Gt)
         (H32 (Datatypes.Eq = Datatypes.Gt))
         (fun H37 : Datatypes.Eq = Datatypes.Gt =>
          (fun H38 : Datatypes.Gt = Datatypes.Gt -> False =>
           H38 (@eq_refl comparison Datatypes.Gt))
            match H37 in (_ = y0) return (y0 = Datatypes.Gt -> False) with
            | eq_refl =>
                fun H38 : Datatypes.Eq = Datatypes.Gt =>
                (fun H39 : Datatypes.Eq = Datatypes.Gt =>
                 (fun H40 : False => (fun H41 : False => H34 False H41) H40)
                   (H36 comparison Datatypes.Eq
                      (fun e : comparison =>
                       match e with
                       | Datatypes.Eq => True
                       | Datatypes.Lt => False
                       | Datatypes.Gt => False
                       end) I Datatypes.Gt H39)) H38
            end)
   | Datatypes.Lt =>
       @right (Datatypes.Lt = Datatypes.Gt)
         (H32 (Datatypes.Lt = Datatypes.Gt))
         (fun H37 : Datatypes.Lt = Datatypes.Gt =>
          (fun H38 : Datatypes.Gt = Datatypes.Gt -> False =>
           H38 (@eq_refl comparison Datatypes.Gt))
            match H37 in (_ = y0) return (y0 = Datatypes.Gt -> False) with
            | eq_refl =>
                fun H38 : Datatypes.Lt = Datatypes.Gt =>
                (fun H39 : Datatypes.Lt = Datatypes.Gt =>
                 (fun H40 : False => (fun H41 : False => H34 False H41) H40)
                   (H36 comparison Datatypes.Lt
                      (fun e : comparison =>
                       match e with
                       | Datatypes.Eq => False
                       | Datatypes.Lt => True
                       | Datatypes.Gt => False
                       end) I Datatypes.Gt H39)) H38
            end)
   | Datatypes.Gt =>
       @left (Datatypes.Gt = Datatypes.Gt)
         (H32 (Datatypes.Gt = Datatypes.Gt))
         (@eq_refl comparison Datatypes.Gt)
   end in
 let H38 := fun x y : BinNums.Z => H37 x y in
 let H39 := H38 in
 let H40 :=
   fix succ (x : BinNums.positive) : BinNums.positive :=
     match x with
     | BinNums.xI p => BinNums.xO (succ p)
     | BinNums.xO p => BinNums.xI p
     | BinNums.xH => BinNums.xO 1
     end in
 let H41 :=
   fix add (x y : BinNums.positive) {struct x} : BinNums.positive :=
     match x with
     | BinNums.xI p =>
         match y with
         | BinNums.xI q => BinNums.xO (add_carry p q)
         | BinNums.xO q => BinNums.xI (add p q)
         | BinNums.xH => BinNums.xO (H40 p)
         end
     | BinNums.xO p =>
         match y with
         | BinNums.xI q => BinNums.xI (add p q)
         | BinNums.xO q => BinNums.xO (add p q)
         | BinNums.xH => BinNums.xI p
         end
     | BinNums.xH =>
         match y with
         | BinNums.xI q => BinNums.xO (H40 q)
         | BinNums.xO q => BinNums.xI q
         | BinNums.xH => BinNums.xO 1
         end
     end
   with add_carry (x y : BinNums.positive) {struct x} : BinNums.positive :=
     match x with
     | BinNums.xI p =>
         match y with
         | BinNums.xI q => BinNums.xI (add_carry p q)
         | BinNums.xO q => BinNums.xO (add_carry p q)
         | BinNums.xH => BinNums.xI (H40 p)
         end
     | BinNums.xO p =>
         match y with
         | BinNums.xI q => BinNums.xO (add_carry p q)
         | BinNums.xO q => BinNums.xI (add p q)
         | BinNums.xH => BinNums.xO (H40 p)
         end
     | BinNums.xH =>
         match y with
         | BinNums.xI q => BinNums.xI (H40 q)
         | BinNums.xO q => BinNums.xO (H40 q)
         | BinNums.xH => BinNums.xI 1
         end
     end
   for add in
 let H42 :=
   fun x : BinNums.Z =>
   match x with
   | BinNums.Z0 => BinNums.Z0
   | BinNums.Zpos p => BinNums.Zpos (BinNums.xO p)
   | BinNums.Zneg p => BinNums.Zneg (BinNums.xO p)
   end in
 let H43 :=
   fix pred_double (x : BinNums.positive) : BinNums.positive :=
     match x with
     | BinNums.xI p => BinNums.xI (BinNums.xO p)
     | BinNums.xO p => BinNums.xI (pred_double p)
     | BinNums.xH => BinNums.xH
     end in
 let H44 :=
   fun x : BinNums.Z =>
   match x with
   | BinNums.Z0 => BinNums.Zpos 1
   | BinNums.Zpos p => BinNums.Zpos (BinNums.xI p)
   | BinNums.Zneg p => BinNums.Zneg (H43 p)
   end in
 let H45 :=
   fun x : BinNums.Z =>
   match x with
   | BinNums.Z0 => BinNums.Zneg 1
   | BinNums.Zpos p => BinNums.Zpos (H43 p)
   | BinNums.Zneg p => BinNums.Zneg (BinNums.xI p)
   end in
 let H46 :=
   fix pos_sub (x y : BinNums.positive) {struct y} : BinNums.Z :=
     match x with
     | BinNums.xI p =>
         match y with
         | BinNums.xI q => H42 (pos_sub p q)
         | BinNums.xO q => H44 (pos_sub p q)
         | BinNums.xH => BinNums.Zpos (BinNums.xO p)
         end
     | BinNums.xO p =>
         match y with
         | BinNums.xI q => H45 (pos_sub p q)
         | BinNums.xO q => H42 (pos_sub p q)
         | BinNums.xH => BinNums.Zpos (H43 p)
         end
     | BinNums.xH =>
         match y with
         | BinNums.xI q => BinNums.Zneg (BinNums.xO q)
         | BinNums.xO q => BinNums.Zneg (H43 q)
         | BinNums.xH => BinNums.Z0
         end
     end in
 let H47 :=
   fun x y : BinNums.Z =>
   match x with
   | BinNums.Z0 => y
   | BinNums.Zpos x' =>
       match y with
       | BinNums.Z0 => x
       | BinNums.Zpos y' => BinNums.Zpos (H41 x' y')
       | BinNums.Zneg y' => H46 x' y'
       end
   | BinNums.Zneg x' =>
       match y with
       | BinNums.Z0 => x
       | BinNums.Zpos y' => H46 y' x'
       | BinNums.Zneg y' => BinNums.Zneg (H41 x' y')
       end
   end in
 let H48 := H47 in
 let H49 := BinNums.Zpos 2 in
 let H50 :=
   fun n m : BinNums.Z =>
   match H31 n m with
   | Datatypes.Eq => n
   | Datatypes.Lt => m
   | Datatypes.Gt => n
   end in
 let H51 := H50 in
 let H52 :=
   fun (elt : Type) (l : SepHeap.FM.Raw.tree elt) (x : SepHeap.FM.Raw.key)
     (e : elt) (r : SepHeap.FM.Raw.tree elt) =>
   @SepHeap.FM.Raw.Node elt l x e r (H48 (H51 (H27 elt l) (H27 elt r)) H25) in
 let H53 := fun elt : Type => H52 elt in
 let H54 :=
   fun (A B : Prop) (P : {A} + {B} -> Type)
     (f : forall a : A, P (@left A B a))
     (f0 : forall b : B, P (@right A B b)) (s : {A} + {B}) =>
   match s as s0 return (P s0) with
   | left x => f x
   | right x => f0 x
   end in
 let H55 := fun (A B : Prop) (P : {A} + {B} -> Set) => H54 A B P in
 let H56 := fun x y : BinNums.Z => H32 (H31 x y = Datatypes.Lt) in
 let H57 := fun x y : BinNums.Z => H31 x y = Datatypes.Lt in
 let H58 :=
   fun (A B : Type) (R : Relation_Definitions.relation A)
     (R' : Relation_Definitions.relation B) (f g : A -> B) =>
   forall x y : A, R x y -> R' (f x) (g y) in
 let H59 := fun A B : Prop => (A -> B) /\ (B -> A) in
 let H60 :=
   fun (A B : Prop) (P : Type) (f : A -> B -> P) (a : A /\ B) =>
   match a with
   | conj x x0 => f x x0
   end in
 let H61 := fun A B P : Prop => H60 A B P in
 let H62 :=
   fun (x y : Prop) (H62 : x <-> y) =>
   H61 (x -> y) (y -> x) (H59 (H32 x) (H32 y))
     (fun (H63 : x -> y) (H64 : y -> x) =>
      @conj (H32 x -> H32 y) (H32 y -> H32 x)
        (fun (H65 : ~ x) (H66 : y) => H34 False (H65 (H64 H66)))
        (fun (H65 : ~ y) (H66 : x) => H34 False (H65 (H63 H66)))) H62 in
 let H63 := H62 in
 let H64 := fun A B : Prop => A -> B in
 let H65 := fun x y : BinNums.Z => H32 (H31 x y = Datatypes.Gt) in
 let H66 :=
   fun x y : BinNums.Z =>
   match
     H31 x y as c return ({c <> Datatypes.Lt} + {~ c <> Datatypes.Lt})
   with
   | Datatypes.Eq =>
       @left (H32 (Datatypes.Eq = Datatypes.Lt))
         (H32 (H32 (Datatypes.Eq = Datatypes.Lt)))
         (fun H66 : Datatypes.Eq = Datatypes.Lt =>
          (fun H67 : Datatypes.Lt = Datatypes.Lt -> False =>
           H67 (@eq_refl comparison Datatypes.Lt))
            match H66 in (_ = y0) return (y0 = Datatypes.Lt -> False) with
            | eq_refl =>
                fun H67 : Datatypes.Eq = Datatypes.Lt =>
                (fun H68 : Datatypes.Eq = Datatypes.Lt =>
                 (fun H69 : False => (fun H70 : False => H34 False H70) H69)
                   (H36 comparison Datatypes.Eq
                      (fun e : comparison =>
                       match e with
                       | Datatypes.Eq => True
                       | Datatypes.Lt => False
                       | Datatypes.Gt => False
                       end) I Datatypes.Lt H68)) H67
            end)
   | Datatypes.Lt =>
       @right (H32 (Datatypes.Lt = Datatypes.Lt))
         (H32 (H32 (Datatypes.Lt = Datatypes.Lt)))
         (fun H66 : Datatypes.Lt <> Datatypes.Lt =>
          (fun H67 : False => (fun H68 : False => H34 False H68) H67)
            ((fun H67 : Datatypes.Lt = Datatypes.Lt => H66 H67)
               (@eq_refl comparison Datatypes.Lt)))
   | Datatypes.Gt =>
       @left (H32 (Datatypes.Gt = Datatypes.Lt))
         (H32 (H32 (Datatypes.Gt = Datatypes.Lt)))
         (fun H66 : Datatypes.Gt = Datatypes.Lt =>
          (fun H67 : Datatypes.Lt = Datatypes.Lt -> False =>
           H67 (@eq_refl comparison Datatypes.Lt))
            match H66 in (_ = y0) return (y0 = Datatypes.Lt -> False) with
            | eq_refl =>
                fun H67 : Datatypes.Gt = Datatypes.Lt =>
                (fun H68 : Datatypes.Gt = Datatypes.Lt =>
                 (fun H69 : False => (fun H70 : False => H34 False H70) H69)
                   (H36 comparison Datatypes.Gt
                      (fun e : comparison =>
                       match e with
                       | Datatypes.Eq => False
                       | Datatypes.Lt => False
                       | Datatypes.Gt => True
                       end) I Datatypes.Lt H68)) H67
            end)
   end in
 let H67 :=
   fun x y : BinNums.Z =>
   H55 (H56 x y) (H32 (H56 x y))
     (fun _ : {BinInt.Z.ge x y} + {~ BinInt.Z.ge x y} =>
      {H56 x y} + {H57 x y})
     (fun a : BinInt.Z.ge x y => @left (H56 x y) (H57 x y) a)
     (fun b : ~ BinInt.Z.ge x y =>
      @right (H56 x y) (H57 x y)
        ((fun b0 : ~ BinInt.Z.le y x =>
          (fun
             H67 : forall n m : BinNums.Z,
                   ~ BinInt.Z.le m n -> BinInt.Z.lt n m => 
           H67 x y b0)
            (fun n m : BinNums.Z =>
             match BinInt.Z.lt_nge n m with
             | conj _ x1 => x1
             end))
           ((fun lemma : BinInt.Z.ge x y <-> BinInt.Z.le y x =>
             @Morphisms.subrelation_proper (Prop -> Prop)
               (H58 Prop Prop H59 H59) H32 H63 (H58 Prop Prop H59 H64) tt
               (@Morphisms.subrelation_respectful Prop H59 H59
                  (Morphisms.subrelation_refl Prop H59) Prop H59 H64
                  Morphisms.iff_impl_subrelation) (H56 x y) 
               (H65 y x) lemma) (BinInt.Z.ge_le_iff x y) b))) 
     (H66 x y) in
 let H68 := H67 in
 let H69 :=
   fun elt : Type =>
   fix bal (l : SepHeap.FM.Raw.tree elt) (x : SepHeap.FM.Raw.key) 
           (d : elt) (r : SepHeap.FM.Raw.tree elt) {struct l} :
     SepHeap.FM.Raw.tree elt :=
     let hl := H27 elt l in
     let hr := H27 elt r in
     if H39 hl (H48 hr H49)
     then
      match l with
      | SepHeap.FM.Raw.Leaf => H53 elt l x d r
      | SepHeap.FM.Raw.Node ll lx ld lr _ =>
          if H68 (H27 elt ll) (H27 elt lr)
          then H52 elt ll lx ld (H52 elt lr x d r)
          else
           match lr with
           | SepHeap.FM.Raw.Leaf => H53 elt l x d r
           | SepHeap.FM.Raw.Node lrl lrx lrd lrr _ =>
               H52 elt (H52 elt ll lx ld lrl) lrx lrd (H52 elt lrr x d r)
           end
      end
     else
      if H39 hr (H48 hl H49)
      then
       match r with
       | SepHeap.FM.Raw.Leaf => H53 elt l x d r
       | SepHeap.FM.Raw.Node rl rx rd rr _ =>
           if H68 (H27 elt rr) (H27 elt rl)
           then H52 elt (H52 elt l x d rl) rx rd rr
           else
            match rl with
            | SepHeap.FM.Raw.Leaf => H53 elt l x d r
            | SepHeap.FM.Raw.Node rll rlx rld rlr _ =>
                H52 elt (H52 elt l x d rll) rlx rld (H52 elt rlr rx rd rr)
            end
       end
      else H52 elt l x d r in
 let H70 :=
   fun elt : Type =>
   fix add (x : SepHeap.FM.Raw.key) (d : elt) (m : SepHeap.FM.Raw.tree elt)
           {struct m} : SepHeap.FM.Raw.tree elt :=
     match m with
     | SepHeap.FM.Raw.Leaf =>
         @SepHeap.FM.Raw.Node elt (SepHeap.FM.Raw.Leaf elt) x d
           (SepHeap.FM.Raw.Leaf elt) H25
     | SepHeap.FM.Raw.Node l y d' r h =>
         match H22 x y with
         | OrderedType.LT _ => H69 elt (add x d l) y d' r
         | OrderedType.EQ _ => @SepHeap.FM.Raw.Node elt l y d r h
         | OrderedType.GT _ => H69 elt l y d' (add x d r)
         end
     end in
 let H71 := NatMap.IntMap.Raw.Proofs.add_bst in
 let H72 :=
   fun (elt : Type) (b : SepHeap.FM.bst elt) =>
   let (this, is_bst) as b0
       return (@SepHeap.FM.Raw.bst elt (@SepHeap.FM.this elt b0)) := b in
   is_bst in
 let H73 :=
   fun (elt : Type) (x : SepHeap.FM.key) (e : elt) (m : SepHeap.FM.t elt) =>
   {|
   Unfolder.FM.this := H70 elt x e (H14 elt m);
   Unfolder.FM.is_bst := H71 elt (H14 elt m) x e (H72 elt m) |} in
 let H74 :=
   fun (T : Type) (k : SepHeap.FM.key) (v : list T) (m : SepHeap.MM.mmap T) =>
   match H24 (list T) k m with
   | Some v' => H73 (list T) k (H12 T v v') m
   | None => H73 (list T) k v m
   end in
 let H75 := fun T : Type => H15 (list T) (H17 T) (H74 T) in
 let H76 :=
   fun (types : list type) (s : SH.SHeap types) =>
   let (impures, _, _) := s in impures in
 let H77 :=
   fun (types : list type) (s : SH.SHeap types) =>
   let (_, pures, _) := s in pures in
 let H78 :=
   fun (types : list type) (s : SH.SHeap types) =>
   let (_, _, other) := s in other in
 let H79 :=
   fun types : list type =>
   fix star_SHeap (l r : SH.SHeap types) {struct l} : 
   SH.SHeap types :=
     {|
     SH.impures := H75 (H3 types) (H76 types l) (H76 types r);
     SH.pures := H12 (expr types) (H77 types l) (H77 types r);
     SH.other := H12 H9 (H78 types l) (H78 types r) |} in
 let H80 :=
   fix map (elt elt' : Type) (f : elt -> elt') (m : SepHeap.FM.Raw.tree elt)
           {struct m} : SepHeap.FM.Raw.tree elt' :=
     match m with
     | SepHeap.FM.Raw.Leaf => SepHeap.FM.Raw.Leaf elt'
     | SepHeap.FM.Raw.Node l x d r h =>
         @SepHeap.FM.Raw.Node elt' (map elt elt' f l) x 
           (f d) (map elt elt' f r) h
     end in
 let H81 := NatMap.IntMap.Raw.Proofs.map_bst in
 let H82 :=
   fun (elt elt' : Type) (f : elt -> elt') (m : SepHeap.FM.t elt) =>
   {|
   Unfolder.FM.this := H80 elt elt' f (H14 elt m);
   Unfolder.FM.is_bst := H81 elt elt' f (H14 elt m) (H72 elt m) |} in
 let H83 :=
   fun (A B : Type) (f : A -> B) =>
   fix map (l : list A) : list B :=
     match l with
     | nil => @nil B
     | a :: t => f a :: map t
     end in
 let H84 :=
   fun (T U : Type) (F : T -> U) => H82 (list T) (list U) (H83 T U F) in
 let H85 :=
   fix leb (n m : nat) {struct n} : bool :=
     match n with
     | 0 => true
     | S n' => match m with
               | 0 => false
               | S m' => leb n' m'
               end
     end in
 let H86 := fun n m : nat => H85 (S n) m in
 let H87 :=
   fix plus (n m : nat) {struct n} : nat :=
     match n with
     | 0 => m
     | S p => S (plus p m)
     end in
 let H88 :=
   fun (types : list type) (ua ub a b : nat) =>
   fix liftExpr (e : expr types) : expr types :=
     match e with
     | Const _ _ => e
     | Var x => @Var types (if H86 x a then x else H87 b x)
     | Func f xs => @Func types f (H83 (expr types) (expr types) liftExpr xs)
     | Equal t e1 e2 => @Equal types t (liftExpr e1) (liftExpr e2)
     | Not e1 => @Not types (liftExpr e1)
     | UVar x => @UVar types (if H86 x ua then x else H87 ub x)
     end in
 let H89 :=
   fun (types : list type) (ua ub a b : nat) (s : SH.SHeap types) =>
   {|
   SH.impures := H84 (list (expr types)) (list (expr types))
                   (H83 (expr types) (expr types) (H88 types ua ub a b))
                   (H76 types s);
   SH.pures := H83 (expr types) (expr types) (H88 types ua ub a b)
                 (H77 types s);
   SH.other := H78 types s |} in
 let H90 :=
   fun (T : Type) (k : SepHeap.FM.key) (v : T) (m : SepHeap.MM.mmap T) =>
   match H24 (list T) k m with
   | Some v' => H73 (list T) k (v :: v') m
   | None => H73 (list T) k (v :: @nil T) m
   end in
 let H91 :=
   fun types : list type =>
   fix hash (s : SEP.sexpr types) : variables * SH.SHeap types :=
     match s with
     | SEP.Emp => (@nil tvar, H10 types)
     | SEP.Inj p =>
         (@nil tvar,
         {|
         SH.impures := H2 (H3 types);
         SH.pures := p :: @nil (expr types);
         SH.other := @nil H9 |})
     | SEP.Star l r =>
         let (vl, hl) := hash l in
         let (vr, hr) := hash r in
         let nr := H11 tvar vr in
         (H12 tvar vl vr,
         H79 types (H89 types 0 0 0 nr hl)
           (H89 types 0 0 nr (H11 tvar vl) hr))
     | SEP.Exists t b => let (v, b0) := hash b in (t :: v, b0)
     | SEP.Func f a =>
         (@nil tvar,
         {|
         SH.impures := H90 (list (expr types)) f a (H2 (list (expr types)));
         SH.pures := @nil (expr types);
         SH.other := @nil H9 |})
     | SEP.Const c =>
         (@nil tvar,
         {|
         SH.impures := H2 (H3 types);
         SH.pures := @nil (expr types);
         SH.other := c :: @nil H9 |})
     end in
 let H92 :=
   fun (types : list type) (F : expr types -> expr types)
     (sh : SH.SHeap types) =>
   {|
   SH.impures := H84 (list (expr types)) (list (expr types))
                   (H83 (expr types) (expr types) F) 
                   (H76 types sh);
   SH.pures := H83 (expr types) (expr types) F (H77 types sh);
   SH.other := H78 types sh |} in
 let H93 :=
   fix minus (n m : nat) {struct n} : nat :=
     match n with
     | 0 => n
     | S k => match m with
              | 0 => n
              | S l => minus k l
              end
     end in
 let H94 :=
   fun types : list type =>
   fix exprSubstU (a b c : nat) (s : expr types) {struct s} : 
   expr types :=
     match s with
     | Const t0 t => @Const types t0 t
     | Var x =>
         if H86 x a
         then @Var types x
         else
          if H86 x b
          then @UVar types (H93 (H87 c x) a)
          else @Var types (H93 (H87 x a) b)
     | Func f args =>
         @Func types f
           (H83 (expr types) (expr types) (exprSubstU a b c) args)
     | Equal t e1 e2 =>
         @Equal types t (exprSubstU a b c e1) (exprSubstU a b c e2)
     | Not e1 => @Not types (exprSubstU a b c e1)
     | UVar x =>
         if H86 x c then @UVar types x else @UVar types (H93 (H87 x b) a)
     end in
 let H95 :=
   fun (types : list type) (a b c : nat) => H92 types (H94 types a b c) in
 let H96 :=
   fun (types : list type) (p : ProverT types) =>
   let (Facts, Summarize, _, _) as p0
       return (exprs types -> @Facts types p0) := p in
   Summarize in
 let H97 :=
   fun (types : list type) (u : UNF.unfoldingState types) =>
   let (_, _, Heap) := u in Heap in
 let H98 :=
   fun (types : list type) (u : UNF.unfoldingState types) =>
   let (_, UVars, _) := u in UVars in
 let H99 :=
   fun (types : list type) (u : UNF.unfoldingState types) =>
   let (Vars, _, _) := u in Vars in
 let H100 :=
   fix find (A B : Type) (f : A -> option B) (ls : list A) {struct ls} :
     option B :=
     match ls with
     | nil => @None B
     | x :: ls' =>
         match f x with
         | Some b => @Some B b
         | None => find A B f ls'
         end
     end in
 let H101 :=
   fun types : list type => (SEP.sexpr types * SEP.sexpr types)%type in
 let H102 := fun (A B : Type) (p : A * B) => let (x, _) := p in x in
 let H103 :=
   fun (types : list type) (concl : Type) (l : SepLemma.lemma types concl) =>
   let (_, _, Concl) := l in Concl in
 let H104 :=
   fun (types : list type)
     (l : SepLemma.lemma types (SEP_LEMMA.sepConcl types)) =>
   H102 (SEP.sexpr types) (SEP.sexpr types) (H103 types (H101 types) l) in
 let H105 :=
   fun elt : Type =>
   fix find (x : nat) (m : Unfolder.FM.Raw.tree elt) {struct m} :
     option elt :=
     match m with
     | Unfolder.FM.Raw.Leaf => @None elt
     | Unfolder.FM.Raw.Node l y d r _ =>
         match H22 x y with
         | OrderedType.LT _ => find x l
         | OrderedType.EQ _ => @Some elt d
         | OrderedType.GT _ => find x r
         end
     end in
 let H106 :=
   fun (elt : Type) (b : Unfolder.FM.bst elt) => let (this, _) := b in this in
 let H107 :=
   fun (elt : Type) (x : Unfolder.FM.key) (m : Unfolder.FM.t elt) =>
   H105 elt x (H106 elt m) in
 let H108 :=
   fun (types : list type) (concl : Type) (l : SepLemma.lemma types concl) =>
   let (Foralls, _, _) := l in Foralls in
 let H109 :=
   fun A : Type =>
   fix rev_append (l l' : list A) {struct l} : list A :=
     match l with
     | nil => l'
     | a :: l0 => rev_append l0 (a :: l')
     end in
 let H110 :=
   fix findWithRest' (A B : Type) (f : A -> list A -> option B)
                     (ls acc : list A) {struct ls} : 
   option B :=
     match ls with
     | nil => @None B
     | x :: ls' =>
         match f x (H109 A acc ls') with
         | Some b => @Some B b
         | None => findWithRest' A B f ls' (x :: acc)
         end
     end in
 let H111 :=
   fun (A B : Type) (f : A -> list A -> option B) (ls : list A) =>
   H110 A B f ls (@nil A) in
 let H112 :=
   fun (T U V : Type) (F : T -> V -> U -> option U) =>
   fix fold_left_2_opt (ls : list T) (ls' : list V) (acc : U) {struct ls} :
     option U :=
     match ls with
     | nil => match ls' with
              | nil => @Some U acc
              | _ :: _ => @None U
              end
     | x :: xs =>
         match ls' with
         | nil => @None U
         | y :: ys =>
             match F x y acc with
             | Some acc0 => fold_left_2_opt xs ys acc0
             | None => @None U
             end
         end
     end in
 let H113 := UNIFIER.FM.bst in
 let H114 :=
   fun (A B : Type) (f : B -> A -> A) (a0 : A) =>
   fix fold_right (l : list B) : A :=
     match l with
     | nil => a0
     | b :: t => f b (fold_right t)
     end in
 let H115 := fun b1 b2 : bool => if b1 then b2 else false in
 let H116 :=
   fun elt : Type =>
   fix find (x : uvar) (m : UNIFIER.FM.Raw.t elt) {struct m} : 
   option elt :=
     match m with
     | UNIFIER.FM.Raw.Leaf => @None elt
     | UNIFIER.FM.Raw.Node l y d r _ =>
         match H22 x y with
         | OrderedType.LT _ => find x l
         | OrderedType.EQ _ => @Some elt d
         | OrderedType.GT _ => find x r
         end
     end in
 let H117 :=
   fun (elt : Type) (b : UNIFIER.FM.bst elt) => let (this, _) := b in this in
 let H118 :=
   fun (elt : Type) (x : UNIFIER.FM.key) (m : UNIFIER.FM.t elt) =>
   H116 elt x (H117 elt m) in
 let H119 :=
   fun (types : list type) (ctx : UNIFIER.FM.t (expr types)) =>
   fix normalized (e : expr types) : bool :=
     match e with
     | Const _ _ => true
     | Var _ => true
     | Func _ l =>
         H114 bool (expr types)
           (fun (x : expr types) (acc : bool) => H115 acc (normalized x))
           true l
     | Equal _ e1 e2 => H115 (normalized e1) (normalized e2)
     | Not e0 => normalized e0
     | UVar x =>
         match H118 (expr types) x ctx with
         | Some _ => false
         | None => true
         end
     end in
 let H120 :=
   fun (types : list type) (this : UNIFIER.FM.t (expr types)) =>
   forall (k : UNIFIER.FM.key) (v : expr types),
   @UNIFIER.FM.MapsTo (expr types) k v this -> H119 types this v = true in
 let H121 :=
   fun types : list type =>
   {this : UNIFIER.FM.t (expr types) & H120 types this} in
 let H122 :=
   fun (A : Type) (R : A -> A -> Prop) (x : A) (H122 : @Acc A R x) =>
   match H122 with
   | Acc_intro H123 => H123
   end in
 let H123 :=
   fun (A : Type) (R : A -> A -> Prop) (P : A -> Type)
     (F : forall x : A, (forall y : A, R y x -> P y) -> P x) =>
   fix Fix_F (x : A) (a : @Acc A R x) {struct a} : 
   P x := F x (fun (y : A) (h : R y x) => Fix_F y (H122 A R x a y h)) in
 let H124 :=
   fun (A : Type) (R : A -> A -> Prop) (Rwf : @well_founded A R)
     (P : A -> Type) (F : forall x : A, (forall y : A, R y x -> P y) -> P x)
     (x : A) => H123 A R P F x (Rwf x) in
 let H125 :=
   fix guard (A : Type) (R : A -> A -> Prop) (n : nat)
             (wfR : @well_founded A R) {struct n} : 
   @well_founded A R :=
     match n with
     | 0 => wfR
     | S n0 =>
         fun x : A =>
         @Acc_intro A R x
           (fun (y : A) (_ : R y x) => guard A R n0 (guard A R n0 wfR) y)
     end in
 let H126 :=
   fun (A : Type) (R : A -> A -> Prop) (P : A -> Type)
     (f : forall x : A,
          (forall y : A, R y x -> @Acc A R y) ->
          (forall y : A, R y x -> P y) -> P x) =>
   fix F (x : A) (a : @Acc A R x) {struct a} : P x :=
     match a with
     | Acc_intro a0 => f x a0 (fun (y : A) (r : R y x) => F y (a0 y r))
     end in
 let H127 :=
   fun (A : Type) (R : A -> A -> Prop) (Rwf : @well_founded A R)
     (P : A -> Type) (X : forall x : A, (forall y : A, R y x -> P y) -> P x)
     (a : A) =>
   H126 A R P
     (fun (x : A) (_ : forall y : A, R y x -> @Acc A R y)
        (X0 : forall y : A, R y x -> P y) => X x X0) a 
     (Rwf a) in
 let H128 :=
   fun (A : Type) (R : A -> A -> Prop) (Rwf : @well_founded A R)
     (P : A -> Prop) => H127 A R Rwf P in
 let H129 :=
   fun (A : Type) (x y : A) (H129 : x = y) =>
   match H129 in (_ = y0) return (y0 = x) with
   | eq_refl => @eq_refl A x
   end in
 let H130 :=
   fun (A : Type) (x : A) (P : A -> Prop) (H130 : P x) (y : A) (H131 : y = x) =>
   H36 A x (fun y0 : A => P y0) H130 y (H129 A y x H131) in
 let H131 :=
   fun (A B : Type) (f : A -> B) (x y : A) (H131 : x = y) =>
   match H131 in (_ = y0) return (f x = f y0) with
   | eq_refl => @eq_refl B (f x)
   end in
 let H132 :=
   fun (T U : Type) (RT : T -> T -> Prop) (RU : U -> U -> Prop)
     (wf_RT : @well_founded T RT) (wf_RU : @well_founded U RU) 
     (x : T * U) =>
   let (t, u) as p return (@Acc (T * U) (@GenRec.R_pair T U RT RU) p) := x in
   H128 T RT wf_RT
     (fun t0 : T =>
      forall u0 : U, @Acc (T * U) (@GenRec.R_pair T U RT RU) (t0, u0))
     (fun (x0 : T)
        (H132 : forall y : T,
                RT y x0 ->
                forall u0 : U,
                @Acc (T * U) (@GenRec.R_pair T U RT RU) (y, u0)) =>
      H128 U RU wf_RU
        (fun u0 : U => @Acc (T * U) (@GenRec.R_pair T U RT RU) (x0, u0))
        (fun (x1 : U)
           (H133 : forall y : U,
                   RU y x1 -> @Acc (T * U) (@GenRec.R_pair T U RT RU) (x0, y)) =>
         @Acc_intro (T * U) (@GenRec.R_pair T U RT RU) 
           (x0, x1)
           (fun y : T * U =>
            let (t0, u0) as p
                return
                  (@GenRec.R_pair T U RT RU p (x0, x1) ->
                   @Acc (T * U) (@GenRec.R_pair T U RT RU) p) := y in
            let p := (t0, u0) in
            let Heqp := @eq_refl (T * U) p in
            let p0 := (x0, x1) in
            let Heqp0 := @eq_refl (T * U) p0 in
            fun H134 : @GenRec.R_pair T U RT RU p p0 =>
            (fun
               H135 : p = p ->
                      p0 = p0 -> @Acc (T * U) (@GenRec.R_pair T U RT RU) p =>
             H135 (@eq_refl (T * U) p) (@eq_refl (T * U) p0))
              match
                H134 in (@GenRec.R_pair _ _ _ _ p1 p2)
                return
                  (p1 = p ->
                   p2 = p0 -> @Acc (T * U) (@GenRec.R_pair T U RT RU) p)
              with
              | GenRec.L l l' r r' H135 =>
                  fun (H136 : (l, r) = p) (H137 : (l', r') = p0) =>
                  (fun H138 : (l, r) = p =>
                   H36 (T * U)%type (l, r)
                     (fun p1 : T * U =>
                      (l', r') = p0 ->
                      RT l l' -> @Acc (T * U) (@GenRec.R_pair T U RT RU) p1)
                     (fun (H139 : (l', r') = p0) (H140 : RT l l') =>
                      H130 (T * U)%type (x0, x1)
                        (fun p1 : T * U =>
                         @GenRec.R_pair T U RT RU p p1 ->
                         (l', r') = p1 ->
                         @Acc (T * U) (@GenRec.R_pair T U RT RU) (l, r))
                        (fun (H141 : @GenRec.R_pair T U RT RU p (x0, x1))
                           (H142 : (l', r') = (x0, x1)) =>
                         H130 (T * U)%type (t0, u0)
                           (fun p1 : T * U =>
                            (l, r) = p1 ->
                            @GenRec.R_pair T U RT RU p1 (x0, x1) ->
                            @Acc (T * U) (@GenRec.R_pair T U RT RU) (l, r))
                           (fun (H143 : (l, r) = (t0, u0))
                              (_ : @GenRec.R_pair T U RT RU (t0, u0) (x0, x1)) =>
                            (fun
                               H145 : (x0, x1) = (x0, x1) ->
                                      @Acc (T * U) 
                                        (@GenRec.R_pair T U RT RU) 
                                        (l, r) =>
                             H145 (@eq_refl (T * U) (x0, x1)))
                              match
                                H142 in (_ = y0)
                                return
                                  (y0 = (x0, x1) ->
                                   @Acc (T * U) (@GenRec.R_pair T U RT RU)
                                     (l, r))
                              with
                              | eq_refl =>
                                  fun H145 : (l', r') = (x0, x1) =>
                                  (fun H146 : (l', r') = (x0, x1) =>
                                   (fun H147 : r' = x1 =>
                                    (fun H148 : l' = x0 =>
                                     (fun (H149 : l' = x0) (_ : r' = x1) =>
                                      (fun
                                         H151 : (t0, u0) = (t0, u0) ->
                                                @Acc 
                                                  (T * U)
                                                  (@GenRec.R_pair T U RT RU)
                                                  (l, r) =>
                                       H151 (@eq_refl (T * U) (t0, u0)))
                                        match
                                          H143 in (_ = y0)
                                          return
                                            (y0 = (t0, u0) ->
                                             @Acc (T * U)
                                               (@GenRec.R_pair T U RT RU)
                                               (l, r))
                                        with
                                        | eq_refl =>
                                            fun H151 : (l, r) = (t0, u0) =>
                                            (fun H152 : (l, r) = (t0, u0) =>
                                             (fun H153 : r = u0 =>
                                              (fun H154 : l = t0 =>
                                               (fun H155 : l = t0 =>
                                                H36 T t0
                                                  (fun t1 : T =>
                                                  r = u0 ->
                                                  @Acc 
                                                  (T * U)
                                                  (@GenRec.R_pair T U RT RU)
                                                  (t1, r))
                                                  (fun H156 : r = u0 =>
                                                  H36 U u0
                                                  (fun u1 : U =>
                                                  @Acc 
                                                  (T * U)
                                                  (@GenRec.R_pair T U RT RU)
                                                  (t0, u1))
                                                  (H130 T t0
                                                  (fun l0 : T =>
                                                  RT l0 l' ->
                                                  @Acc 
                                                  (T * U)
                                                  (@GenRec.R_pair T U RT RU)
                                                  (t0, u0))
                                                  (fun H157 : RT t0 l' =>
                                                  H130 T x0
                                                  (fun l'0 : T =>
                                                  RT t0 l'0 ->
                                                  @Acc 
                                                  (T * U)
                                                  (@GenRec.R_pair T U RT RU)
                                                  (t0, u0))
                                                  (fun H158 : RT t0 x0 =>
                                                  H132 t0 H158 u0) l' H149
                                                  H157) l H155 H140) r
                                                  (H129 U r u0 H156)) l
                                                  (H129 T l t0 H155)) H154)
                                                (H131 
                                                  (T * U)%type T
                                                  (fun e : T * U =>
                                                  let (t1, _) := e in t1)
                                                  (l, r) 
                                                  (t0, u0) H152) H153)
                                               (H131 
                                                  (T * U)%type U
                                                  (fun e : T * U =>
                                                  let (_, u1) := e in u1)
                                                  (l, r) 
                                                  (t0, u0) H152)) H151
                                        end) H148)
                                      (H131 (T * U)%type T
                                         (fun e : T * U =>
                                          let (t1, _) := e in t1) 
                                         (l', r') (x0, x1) H146) H147)
                                     (H131 (T * U)%type U
                                        (fun e : T * U =>
                                         let (_, u1) := e in u1) 
                                        (l', r') (x0, x1) H146)) H145
                              end) p Heqp H138 H141) p0 Heqp0 H134 H139) p
                     H138) H136 H137 H135
              | GenRec.R l r r' H135 =>
                  fun (H136 : (l, r) = p) (H137 : (l, r') = p0) =>
                  (fun H138 : (l, r) = p =>
                   H36 (T * U)%type (l, r)
                     (fun p1 : T * U =>
                      (l, r') = p0 ->
                      RU r r' -> @Acc (T * U) (@GenRec.R_pair T U RT RU) p1)
                     (fun (H139 : (l, r') = p0) (H140 : RU r r') =>
                      H130 (T * U)%type (x0, x1)
                        (fun p1 : T * U =>
                         @GenRec.R_pair T U RT RU p p1 ->
                         (l, r') = p1 ->
                         @Acc (T * U) (@GenRec.R_pair T U RT RU) (l, r))
                        (fun (H141 : @GenRec.R_pair T U RT RU p (x0, x1))
                           (H142 : (l, r') = (x0, x1)) =>
                         H130 (T * U)%type (t0, u0)
                           (fun p1 : T * U =>
                            (l, r) = p1 ->
                            @GenRec.R_pair T U RT RU p1 (x0, x1) ->
                            @Acc (T * U) (@GenRec.R_pair T U RT RU) (l, r))
                           (fun (H143 : (l, r) = (t0, u0))
                              (_ : @GenRec.R_pair T U RT RU (t0, u0) (x0, x1)) =>
                            (fun
                               H145 : (x0, x1) = (x0, x1) ->
                                      @Acc (T * U) 
                                        (@GenRec.R_pair T U RT RU) 
                                        (l, r) =>
                             H145 (@eq_refl (T * U) (x0, x1)))
                              match
                                H142 in (_ = y0)
                                return
                                  (y0 = (x0, x1) ->
                                   @Acc (T * U) (@GenRec.R_pair T U RT RU)
                                     (l, r))
                              with
                              | eq_refl =>
                                  fun H145 : (l, r') = (x0, x1) =>
                                  (fun H146 : (l, r') = (x0, x1) =>
                                   (fun H147 : r' = x1 =>
                                    (fun H148 : l = x0 =>
                                     (fun H149 : l = x0 =>
                                      H36 T x0
                                        (fun t1 : T =>
                                         r' = x1 ->
                                         @Acc (T * U)
                                           (@GenRec.R_pair T U RT RU) 
                                           (t1, r))
                                        (fun H150 : r' = x1 =>
                                         (fun
                                            H151 : 
                                             (t0, u0) = (t0, u0) ->
                                             @Acc (T * U)
                                               (@GenRec.R_pair T U RT RU)
                                               (x0, r) =>
                                          H151 (@eq_refl (T * U) (t0, u0)))
                                           match
                                             H143 in (_ = y0)
                                             return
                                               (y0 = (t0, u0) ->
                                                @Acc 
                                                  (T * U)
                                                  (@GenRec.R_pair T U RT RU)
                                                  (x0, r))
                                           with
                                           | eq_refl =>
                                               fun H151 : (l, r) = (t0, u0) =>
                                               (fun H152 : (l, r) = (t0, u0) =>
                                                (fun H153 : r = u0 =>
                                                 (fun H154 : l = t0 =>
                                                  (fun 
                                                  (H155 : l = t0)
                                                  (H156 : r = u0) =>
                                                  H36 U u0
                                                  (fun u1 : U =>
                                                  @Acc 
                                                  (T * U)
                                                  (@GenRec.R_pair T U RT RU)
                                                  (x0, u1))
                                                  (H130 U u0
                                                  (fun r0 : U =>
                                                  RU r0 r' ->
                                                  @Acc 
                                                  (T * U)
                                                  (@GenRec.R_pair T U RT RU)
                                                  (x0, u0))
                                                  (fun H157 : RU u0 r' =>
                                                  H130 T x0
                                                  (fun l0 : T =>
                                                  l0 = t0 ->
                                                  @Acc 
                                                  (T * U)
                                                  (@GenRec.R_pair T U RT RU)
                                                  (x0, u0))
                                                  (fun _ : x0 = t0 =>
                                                  H130 U x1
                                                  (fun r'0 : U =>
                                                  RU u0 r'0 ->
                                                  @Acc 
                                                  (T * U)
                                                  (@GenRec.R_pair T U RT RU)
                                                  (x0, u0))
                                                  (fun H159 : RU u0 x1 =>
                                                  H133 u0 H159) r' H150 H157)
                                                  l H149 H155) r H156 H140) r
                                                  (H129 U r u0 H156)) H154)
                                                  (H131 
                                                  (T * U)%type T
                                                  (fun e : T * U =>
                                                  let (t1, _) := e in t1)
                                                  (l, r) 
                                                  (t0, u0) H152) H153)
                                                  (H131 
                                                  (T * U)%type U
                                                  (fun e : T * U =>
                                                  let (_, u1) := e in u1)
                                                  (l, r) 
                                                  (t0, u0) H152)) H151
                                           end) l (H129 T l x0 H149)) H148)
                                      (H131 (T * U)%type T
                                         (fun e : T * U =>
                                          let (t1, _) := e in t1) 
                                         (l, r') (x0, x1) H146) H147)
                                     (H131 (T * U)%type U
                                        (fun e : T * U =>
                                         let (_, u1) := e in u1) 
                                        (l, r') (x0, x1) H146)) H145
                              end) p Heqp H138 H141) p0 Heqp0 H134 H139) p
                     H138) H136 H137 H135
              end))) t u in
 let H133 :=
   fun (P : nat -> Type) (f : P 0) (f0 : forall n : nat, P n -> P (S n)) =>
   fix F (n : nat) : P n :=
     match n as n0 return (P n0) with
     | 0 => f
     | S n0 => f0 n0 (F n0)
     end in
 let H134 := fun P : nat -> Prop => H133 P in
 let H135 :=
   fun a : nat =>
   H134 (fun a0 : nat => @Acc nat GenRec.R_nat a0)
     (@Acc_intro nat GenRec.R_nat 0
        (fun (y : nat) (H135 : GenRec.R_nat y 0) =>
         (fun H136 : y = y -> 0 = 0 -> @Acc nat GenRec.R_nat y =>
          H136 (@eq_refl nat y) (@eq_refl nat 0))
           match
             H135 in (GenRec.R_nat n n0)
             return (n = y -> n0 = 0 -> @Acc nat GenRec.R_nat y)
           with
           | GenRec.R_S n =>
               fun (H136 : n = y) (H137 : S n = 0) =>
               (fun H138 : n = y =>
                H36 nat y
                  (fun n0 : nat => S n0 = 0 -> @Acc nat GenRec.R_nat y)
                  (fun H139 : S y = 0 =>
                   (fun H140 : False =>
                    (fun H141 : False => H34 (@Acc nat GenRec.R_nat y) H141)
                      H140)
                     (H36 nat (S y)
                        (fun e : nat =>
                         match e with
                         | 0 => False
                         | S _ => True
                         end) I 0 H139)) n (H129 nat n y H138)) H136 H137
           end))
     (fun (a0 : nat) (IHa : @Acc nat GenRec.R_nat a0) =>
      @Acc_intro nat GenRec.R_nat (S a0)
        (fun (y : nat) (H135 : GenRec.R_nat y (S a0)) =>
         (fun H136 : y = y -> S a0 = S a0 -> @Acc nat GenRec.R_nat y =>
          H136 (@eq_refl nat y) (@eq_refl nat (S a0)))
           match
             H135 in (GenRec.R_nat n n0)
             return (n = y -> n0 = S a0 -> @Acc nat GenRec.R_nat y)
           with
           | GenRec.R_S n =>
               fun (H136 : n = y) (H137 : S n = S a0) =>
               (fun H138 : n = y =>
                H36 nat y
                  (fun n0 : nat => S n0 = S a0 -> @Acc nat GenRec.R_nat y)
                  (fun H139 : S y = S a0 =>
                   (fun H140 : y = a0 =>
                    (fun H141 : y = a0 =>
                     H36 nat a0 (fun n0 : nat => @Acc nat GenRec.R_nat n0)
                       (H36 nat n
                          (fun y0 : nat =>
                           GenRec.R_nat y0 (S a0) ->
                           y0 = a0 -> @Acc nat GenRec.R_nat a0)
                          (fun (H142 : GenRec.R_nat n (S a0)) (H143 : n = a0) =>
                           H130 nat a0
                             (fun n0 : nat =>
                              GenRec.R_nat n0 (S a0) ->
                              @Acc nat GenRec.R_nat a0)
                             (fun _ : GenRec.R_nat a0 (S a0) => IHa) n H143
                             H142) y H138 H135 H141) y 
                       (H129 nat y a0 H141)) H140)
                     (H131 nat nat
                        (fun e : nat =>
                         match e with
                         | 0 => y
                         | S n0 => n0
                         end) (S y) (S a0) H139)) n 
                  (H129 nat n y H138)) H136 H137
           end)) a in
 let H136 :=
   fun (ts : list type) (a : expr ts) =>
   (fix recur (e : expr ts) : @Acc (expr ts) (@R_expr ts) e :=
      match e as e0 return (@Acc (expr ts) (@R_expr ts) e0) with
      | Const t v =>
          @Acc_intro (expr ts) (@R_expr ts) (@Const ts t v)
            (fun (y : expr ts) (H136 : @R_expr ts y (@Const ts t v)) =>
             match
               H136 in (@R_expr _ e0 e1)
               return
                 (e0 = y ->
                  e1 = @Const ts t v -> @Acc (expr ts) (@R_expr ts) y)
             with
             | R_EqualL t1 l r =>
                 fun (H137 : l = y) (H138 : @Equal ts t1 l r = @Const ts t v) =>
                 match
                   match H137 in (_ = y0) return (y0 = l) with
                   | eq_refl => @eq_refl (expr ts) l
                   end in (_ = y0)
                   return
                     (@Equal ts t1 y0 r = @Const ts t v ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Equal ts t1 y r = @Const ts t v =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => True
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_EqualR t1 l r =>
                 fun (H137 : r = y) (H138 : @Equal ts t1 l r = @Const ts t v) =>
                 match
                   match H137 in (_ = y0) return (y0 = r) with
                   | eq_refl => @eq_refl (expr ts) r
                   end in (_ = y0)
                   return
                     (@Equal ts t1 l y0 = @Const ts t v ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Equal ts t1 l y = @Const ts t v =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => True
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_Not e0 =>
                 fun (H137 : e0 = y) (H138 : @Not ts e0 = @Const ts t v) =>
                 match
                   match H137 in (_ = y0) return (y0 = e0) with
                   | eq_refl => @eq_refl (expr ts) e0
                   end in (_ = y0)
                   return
                     (@Not ts y0 = @Const ts t v ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Not ts y = @Const ts t v =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => False
                           | Not _ => True
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_Func f args arg H137 =>
                 fun (H138 : arg = y)
                   (H139 : @Func ts f args = @Const ts t v) =>
                 match
                   match H138 in (_ = y0) return (y0 = arg) with
                   | eq_refl => @eq_refl (expr ts) arg
                   end in (_ = y0)
                   return
                     (@Func ts f args = @Const ts t v ->
                      @In (expr ts) y0 args -> @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H140 : @Func ts f args = @Const ts t v =>
                     H34
                       (@In (expr ts) y args -> @Acc (expr ts) (@R_expr ts) y)
                       match
                         H140 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => True
                           | Equal _ _ _ => False
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H139 H137
             end (@eq_refl (expr ts) y) (@eq_refl (expr ts) (@Const ts t v)))
      | Var x =>
          @Acc_intro (expr ts) (@R_expr ts) (@Var ts x)
            (fun (y : expr ts) (H136 : @R_expr ts y (@Var ts x)) =>
             match
               H136 in (@R_expr _ e0 e1)
               return
                 (e0 = y -> e1 = @Var ts x -> @Acc (expr ts) (@R_expr ts) y)
             with
             | R_EqualL t l r =>
                 fun (H137 : l = y) (H138 : @Equal ts t l r = @Var ts x) =>
                 match
                   match H137 in (_ = y0) return (y0 = l) with
                   | eq_refl => @eq_refl (expr ts) l
                   end in (_ = y0)
                   return
                     (@Equal ts t y0 r = @Var ts x ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Equal ts t y r = @Var ts x =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => True
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_EqualR t l r =>
                 fun (H137 : r = y) (H138 : @Equal ts t l r = @Var ts x) =>
                 match
                   match H137 in (_ = y0) return (y0 = r) with
                   | eq_refl => @eq_refl (expr ts) r
                   end in (_ = y0)
                   return
                     (@Equal ts t l y0 = @Var ts x ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Equal ts t l y = @Var ts x =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => True
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_Not e0 =>
                 fun (H137 : e0 = y) (H138 : @Not ts e0 = @Var ts x) =>
                 match
                   match H137 in (_ = y0) return (y0 = e0) with
                   | eq_refl => @eq_refl (expr ts) e0
                   end in (_ = y0)
                   return
                     (@Not ts y0 = @Var ts x -> @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Not ts y = @Var ts x =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => False
                           | Not _ => True
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_Func f args arg H137 =>
                 fun (H138 : arg = y) (H139 : @Func ts f args = @Var ts x) =>
                 match
                   match H138 in (_ = y0) return (y0 = arg) with
                   | eq_refl => @eq_refl (expr ts) arg
                   end in (_ = y0)
                   return
                     (@Func ts f args = @Var ts x ->
                      @In (expr ts) y0 args -> @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H140 : @Func ts f args = @Var ts x =>
                     H34
                       (@In (expr ts) y args -> @Acc (expr ts) (@R_expr ts) y)
                       match
                         H140 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => True
                           | Equal _ _ _ => False
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H139 H137
             end (@eq_refl (expr ts) y) (@eq_refl (expr ts) (@Var ts x)))
      | Func f xs =>
          @Acc_intro (expr ts) (@R_expr ts) (@Func ts f xs)
            (fun (y : expr ts) (H136 : @R_expr ts y (@Func ts f xs)) =>
             match
               H136 in (@R_expr _ e0 e1)
               return
                 (e0 = y ->
                  e1 = @Func ts f xs -> @Acc (expr ts) (@R_expr ts) y)
             with
             | R_EqualL t l0 r =>
                 fun (H137 : l0 = y)
                   (H138 : @Equal ts t l0 r = @Func ts f xs) =>
                 match
                   match H137 in (_ = y0) return (y0 = l0) with
                   | eq_refl => @eq_refl (expr ts) l0
                   end in (_ = y0)
                   return
                     (@Equal ts t y0 r = @Func ts f xs ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Equal ts t y r = @Func ts f xs =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => True
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_EqualR t l0 r =>
                 fun (H137 : r = y) (H138 : @Equal ts t l0 r = @Func ts f xs) =>
                 match
                   match H137 in (_ = y0) return (y0 = r) with
                   | eq_refl => @eq_refl (expr ts) r
                   end in (_ = y0)
                   return
                     (@Equal ts t l0 y0 = @Func ts f xs ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Equal ts t l0 y = @Func ts f xs =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => True
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_Not e0 =>
                 fun (H137 : e0 = y) (H138 : @Not ts e0 = @Func ts f xs) =>
                 match
                   match H137 in (_ = y0) return (y0 = e0) with
                   | eq_refl => @eq_refl (expr ts) e0
                   end in (_ = y0)
                   return
                     (@Not ts y0 = @Func ts f xs ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Not ts y = @Func ts f xs =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => False
                           | Not _ => True
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_Func f0 args arg H137 =>
                 fun (H138 : arg = y)
                   (H139 : @Func ts f0 args = @Func ts f xs) =>
                 match
                   match H138 in (_ = y0) return (y0 = arg) with
                   | eq_refl => @eq_refl (expr ts) arg
                   end in (_ = y0)
                   return
                     (@Func ts f0 args = @Func ts f xs ->
                      @In (expr ts) y0 args -> @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H140 : @Func ts f0 args = @Func ts f xs =>
                     match
                       match
                         H131 (expr ts) (list (expr ts))
                           (fun e0 : expr ts =>
                            match e0 with
                            | Const _ _ => args
                            | Var _ => args
                            | Func _ l => l
                            | Equal _ _ _ => args
                            | Not _ => args
                            | UVar _ => args
                            end) (@Func ts f0 args) 
                           (@Func ts f xs) H140 in 
                         (_ = y0) return (y0 = args)
                       with
                       | eq_refl => @eq_refl (list (expr ts)) args
                       end in (_ = y0)
                       return
                         (@In (expr ts) y y0 -> @Acc (expr ts) (@R_expr ts) y)
                     with
                     | eq_refl =>
                         fun H141 : @In (expr ts) y xs =>
                         (fix F (l : list (expr ts)) :
                            @List.Forall (expr ts)
                              (fun a0 : expr ts =>
                               @Acc (expr ts) (@R_expr ts) a0) l ->
                            forall y0 : expr ts,
                            @In (expr ts) y0 l ->
                            @Acc (expr ts) (@R_expr ts) y0 :=
                            match
                              l as l0
                              return
                                (@List.Forall (expr ts)
                                   (fun a0 : expr ts =>
                                    @Acc (expr ts) (@R_expr ts) a0) l0 ->
                                 forall y0 : expr ts,
                                 @In (expr ts) y0 l0 ->
                                 @Acc (expr ts) (@R_expr ts) y0)
                            with
                            | nil =>
                                fun
                                  (_ : @List.Forall 
                                         (expr ts)
                                         (fun a0 : expr ts =>
                                          @Acc (expr ts) (@R_expr ts) a0)
                                         (@nil (expr ts))) 
                                  (y0 : expr ts)
                                  (H143 : @In (expr ts) y0 (@nil (expr ts))) =>
                                match
                                  H143
                                  return (@Acc (expr ts) (@R_expr ts) y0)
                                with
                                end
                            | y0 :: l0 =>
                                fun
                                  (H142 : @List.Forall 
                                            (expr ts)
                                            (fun a0 : expr ts =>
                                             @Acc (expr ts) (@R_expr ts) a0)
                                            (y0 :: l0)) 
                                  (y1 : expr ts)
                                  (H143 : @In (expr ts) y1 (y0 :: l0)) =>
                                match H143 with
                                | or_introl H144 =>
                                    match
                                      H142 in (@List.Forall _ _ l1)
                                      return
                                        (l1 = y0 :: l0 ->
                                         @Acc (expr ts) (@R_expr ts) y1)
                                    with
                                    | Forall_nil =>
                                        fun H145 : @nil (expr ts) = y0 :: l0 =>
                                        H34 (@Acc (expr ts) (@R_expr ts) y1)
                                          match
                                            H145 in (_ = y2)
                                            return
                                              match y2 with
                                              | nil => True
                                              | _ :: _ => False
                                              end
                                          with
                                          | eq_refl => I
                                          end
                                    | Forall_cons x l1 H145 H146 =>
                                        fun H147 : x :: l1 = y0 :: l0 =>
                                        match
                                          match
                                            H131 (list (expr ts)) 
                                              (expr ts)
                                              (fun e0 : list (expr ts) =>
                                               match e0 with
                                               | nil => x
                                               | e1 :: _ => e1
                                               end) 
                                              (x :: l1) 
                                              (y0 :: l0) H147 in 
                                            (_ = y2) 
                                            return (y2 = x)
                                          with
                                          | eq_refl => @eq_refl (expr ts) x
                                          end in (_ = y2)
                                          return
                                            (l1 = l0 ->
                                             @Acc (expr ts) (@R_expr ts) y2 ->
                                             @List.Forall 
                                               (expr ts)
                                               (fun a0 : expr ts =>
                                                @Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) a0) l1 ->
                                             @Acc (expr ts) (@R_expr ts) y1)
                                        with
                                        | eq_refl =>
                                            fun H148 : l1 = l0 =>
                                            match
                                              match
                                                H148 in (_ = y2)
                                                return (y2 = l1)
                                              with
                                              | eq_refl =>
                                                  @eq_refl 
                                                  (list (expr ts)) l1
                                              end in 
                                              (_ = y2)
                                              return
                                                (@Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) y0 ->
                                                 @List.Forall 
                                                  (expr ts)
                                                  (fun a0 : expr ts =>
                                                  @Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) a0) y2 ->
                                                 @Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) y1)
                                            with
                                            | eq_refl =>
                                                fun
                                                  (H149 : 
                                                  @Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) y0)
                                                  (_ : 
                                                  @List.Forall 
                                                  (expr ts)
                                                  (fun a0 : expr ts =>
                                                  @Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) a0) l0) =>
                                                match
                                                  H144 in (_ = y2)
                                                  return
                                                  (@Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) y2)
                                                with
                                                | eq_refl => H149
                                                end
                                            end
                                        end
                                          (H131 (list (expr ts))
                                             (list (expr ts))
                                             (fun e0 : list (expr ts) =>
                                              match e0 with
                                              | nil => l1
                                              | _ :: l2 => l2
                                              end) 
                                             (x :: l1) 
                                             (y0 :: l0) H147) H145 H146
                                    end
                                      (@eq_refl (list (expr ts)) (y0 :: l0))
                                | or_intror H144 =>
                                    match
                                      H142 in (@List.Forall _ _ l1)
                                      return
                                        (l1 = y0 :: l0 ->
                                         @Acc (expr ts) (@R_expr ts) y1)
                                    with
                                    | Forall_nil =>
                                        fun H145 : @nil (expr ts) = y0 :: l0 =>
                                        H34 (@Acc (expr ts) (@R_expr ts) y1)
                                          match
                                            H145 in (_ = y2)
                                            return
                                              match y2 with
                                              | nil => True
                                              | _ :: _ => False
                                              end
                                          with
                                          | eq_refl => I
                                          end
                                    | Forall_cons x l1 H145 H146 =>
                                        fun H147 : x :: l1 = y0 :: l0 =>
                                        match
                                          match
                                            H131 (list (expr ts)) 
                                              (expr ts)
                                              (fun e0 : list (expr ts) =>
                                               match e0 with
                                               | nil => x
                                               | e1 :: _ => e1
                                               end) 
                                              (x :: l1) 
                                              (y0 :: l0) H147 in 
                                            (_ = y2) 
                                            return (y2 = x)
                                          with
                                          | eq_refl => @eq_refl (expr ts) x
                                          end in (_ = y2)
                                          return
                                            (l1 = l0 ->
                                             @Acc (expr ts) (@R_expr ts) y2 ->
                                             @List.Forall 
                                               (expr ts)
                                               (fun a0 : expr ts =>
                                                @Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) a0) l1 ->
                                             @Acc (expr ts) (@R_expr ts) y1)
                                        with
                                        | eq_refl =>
                                            fun H148 : l1 = l0 =>
                                            match
                                              match
                                                H148 in (_ = y2)
                                                return (y2 = l1)
                                              with
                                              | eq_refl =>
                                                  @eq_refl 
                                                  (list (expr ts)) l1
                                              end in 
                                              (_ = y2)
                                              return
                                                (@Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) y0 ->
                                                 @List.Forall 
                                                  (expr ts)
                                                  (fun a0 : expr ts =>
                                                  @Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) a0) y2 ->
                                                 @Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) y1)
                                            with
                                            | eq_refl =>
                                                fun
                                                  (_ : 
                                                  @Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) y0)
                                                  (H150 : 
                                                  @List.Forall 
                                                  (expr ts)
                                                  (fun a0 : expr ts =>
                                                  @Acc 
                                                  (expr ts) 
                                                  (@R_expr ts) a0) l0) =>
                                                F l0 H150 y1 H144
                                            end
                                        end
                                          (H131 (list (expr ts))
                                             (list (expr ts))
                                             (fun e0 : list (expr ts) =>
                                              match e0 with
                                              | nil => l1
                                              | _ :: l2 => l2
                                              end) 
                                             (x :: l1) 
                                             (y0 :: l0) H147) H145 H146
                                    end
                                      (@eq_refl (list (expr ts)) (y0 :: l0))
                                end
                            end) xs
                           ((fix prove (ls : list (expr ts)) :
                               @List.Forall (expr ts)
                                 (fun a0 : expr ts =>
                                  @Acc (expr ts) (@R_expr ts) a0) ls :=
                               match
                                 ls as ls0
                                 return
                                   (@List.Forall (expr ts)
                                      (fun a0 : expr ts =>
                                       @Acc (expr ts) (@R_expr ts) a0) ls0)
                               with
                               | nil =>
                                   @Forall_nil (expr ts)
                                     (fun a0 : expr ts =>
                                      @Acc (expr ts) (@R_expr ts) a0)
                               | l :: ls0 =>
                                   @Forall_cons (expr ts)
                                     (fun a0 : expr ts =>
                                      @Acc (expr ts) (@R_expr ts) a0) l ls0
                                     (recur l) (prove ls0)
                               end) xs) y H141
                     end
                 end H139 H137
             end (@eq_refl (expr ts) y) (@eq_refl (expr ts) (@Func ts f xs)))
      | Equal tv e1 e2 =>
          @Acc_intro (expr ts) (@R_expr ts) (@Equal ts tv e1 e2)
            (fun (y : expr ts) (H136 : @R_expr ts y (@Equal ts tv e1 e2)) =>
             match
               H136 in (@R_expr _ e0 e3)
               return
                 (e0 = y ->
                  e3 = @Equal ts tv e1 e2 -> @Acc (expr ts) (@R_expr ts) y)
             with
             | R_EqualL t0 l r =>
                 fun (H137 : l = y)
                   (H138 : @Equal ts t0 l r = @Equal ts tv e1 e2) =>
                 match
                   match H137 in (_ = y0) return (y0 = l) with
                   | eq_refl => @eq_refl (expr ts) l
                   end in (_ = y0)
                   return
                     (@Equal ts t0 y0 r = @Equal ts tv e1 e2 ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Equal ts t0 y r = @Equal ts tv e1 e2 =>
                     match
                       match
                         H131 (expr ts) (expr ts)
                           (fun e0 : expr ts =>
                            match e0 with
                            | Const _ _ => y
                            | Var _ => y
                            | Func _ _ => y
                            | Equal _ e3 _ => e3
                            | Not _ => y
                            | UVar _ => y
                            end) (@Equal ts t0 y r) 
                           (@Equal ts tv e1 e2) H139 in 
                         (_ = y0) return (y0 = y)
                       with
                       | eq_refl => @eq_refl (expr ts) y
                       end in (_ = y0)
                       return (r = e2 -> @Acc (expr ts) (@R_expr ts) y0)
                     with
                     | eq_refl => fun _ : r = e2 => recur e1
                     end
                       (H131 (expr ts) (expr ts)
                          (fun e0 : expr ts =>
                           match e0 with
                           | Const _ _ => r
                           | Var _ => r
                           | Func _ _ => r
                           | Equal _ _ e4 => e4
                           | Not _ => r
                           | UVar _ => r
                           end) (@Equal ts t0 y r) 
                          (@Equal ts tv e1 e2) H139)
                 end H138
             | R_EqualR t0 l r =>
                 fun (H137 : r = y)
                   (H138 : @Equal ts t0 l r = @Equal ts tv e1 e2) =>
                 match
                   match H137 in (_ = y0) return (y0 = r) with
                   | eq_refl => @eq_refl (expr ts) r
                   end in (_ = y0)
                   return
                     (@Equal ts t0 l y0 = @Equal ts tv e1 e2 ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Equal ts t0 l y = @Equal ts tv e1 e2 =>
                     match
                       match
                         H131 (expr ts) (expr ts)
                           (fun e0 : expr ts =>
                            match e0 with
                            | Const _ _ => y
                            | Var _ => y
                            | Func _ _ => y
                            | Equal _ _ e4 => e4
                            | Not _ => y
                            | UVar _ => y
                            end) (@Equal ts t0 l y) 
                           (@Equal ts tv e1 e2) H139 in 
                         (_ = y0) return (y0 = y)
                       with
                       | eq_refl => @eq_refl (expr ts) y
                       end in (_ = y0)
                       return (@Acc (expr ts) (@R_expr ts) y0)
                     with
                     | eq_refl => recur e2
                     end
                 end H138
             | R_Not e0 =>
                 fun (H137 : e0 = y) (H138 : @Not ts e0 = @Equal ts tv e1 e2) =>
                 match
                   match H137 in (_ = y0) return (y0 = e0) with
                   | eq_refl => @eq_refl (expr ts) e0
                   end in (_ = y0)
                   return
                     (@Not ts y0 = @Equal ts tv e1 e2 ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Not ts y = @Equal ts tv e1 e2 =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => False
                           | Not _ => True
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_Func f args arg H137 =>
                 fun (H138 : arg = y)
                   (H139 : @Func ts f args = @Equal ts tv e1 e2) =>
                 match
                   match H138 in (_ = y0) return (y0 = arg) with
                   | eq_refl => @eq_refl (expr ts) arg
                   end in (_ = y0)
                   return
                     (@Func ts f args = @Equal ts tv e1 e2 ->
                      @In (expr ts) y0 args -> @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H140 : @Func ts f args = @Equal ts tv e1 e2 =>
                     H34
                       (@In (expr ts) y args -> @Acc (expr ts) (@R_expr ts) y)
                       match
                         H140 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => True
                           | Equal _ _ _ => False
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H139 H137
             end (@eq_refl (expr ts) y)
               (@eq_refl (expr ts) (@Equal ts tv e1 e2)))
      | Not e0 =>
          @Acc_intro (expr ts) (@R_expr ts) (@Not ts e0)
            (fun (y : expr ts) (H136 : @R_expr ts y (@Not ts e0)) =>
             match
               H136 in (@R_expr _ e1 e2)
               return
                 (e1 = y -> e2 = @Not ts e0 -> @Acc (expr ts) (@R_expr ts) y)
             with
             | R_EqualL t l r =>
                 fun (H137 : l = y) (H138 : @Equal ts t l r = @Not ts e0) =>
                 match
                   match H137 in (_ = y0) return (y0 = l) with
                   | eq_refl => @eq_refl (expr ts) l
                   end in (_ = y0)
                   return
                     (@Equal ts t y0 r = @Not ts e0 ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Equal ts t y r = @Not ts e0 =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => True
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_EqualR t l r =>
                 fun (H137 : r = y) (H138 : @Equal ts t l r = @Not ts e0) =>
                 match
                   match H137 in (_ = y0) return (y0 = r) with
                   | eq_refl => @eq_refl (expr ts) r
                   end in (_ = y0)
                   return
                     (@Equal ts t l y0 = @Not ts e0 ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Equal ts t l y = @Not ts e0 =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => True
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_Not e1 =>
                 fun (H137 : e1 = y) (H138 : @Not ts e1 = @Not ts e0) =>
                 match
                   match H137 in (_ = y0) return (y0 = e1) with
                   | eq_refl => @eq_refl (expr ts) e1
                   end in (_ = y0)
                   return
                     (@Not ts y0 = @Not ts e0 ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Not ts y = @Not ts e0 =>
                     match
                       match
                         H131 (expr ts) (expr ts)
                           (fun e2 : expr ts =>
                            match e2 with
                            | Const _ _ => y
                            | Var _ => y
                            | Func _ _ => y
                            | Equal _ _ _ => y
                            | Not e3 => e3
                            | UVar _ => y
                            end) (@Not ts y) (@Not ts e0) H139 in 
                         (_ = y0) return (y0 = y)
                       with
                       | eq_refl => @eq_refl (expr ts) y
                       end in (_ = y0)
                       return (@Acc (expr ts) (@R_expr ts) y0)
                     with
                     | eq_refl => recur e0
                     end
                 end H138
             | R_Func f args arg H137 =>
                 fun (H138 : arg = y) (H139 : @Func ts f args = @Not ts e0) =>
                 match
                   match H138 in (_ = y0) return (y0 = arg) with
                   | eq_refl => @eq_refl (expr ts) arg
                   end in (_ = y0)
                   return
                     (@Func ts f args = @Not ts e0 ->
                      @In (expr ts) y0 args -> @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H140 : @Func ts f args = @Not ts e0 =>
                     H34
                       (@In (expr ts) y args -> @Acc (expr ts) (@R_expr ts) y)
                       match
                         H140 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => True
                           | Equal _ _ _ => False
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H139 H137
             end (@eq_refl (expr ts) y) (@eq_refl (expr ts) (@Not ts e0)))
      | UVar x =>
          @Acc_intro (expr ts) (@R_expr ts) (@UVar ts x)
            (fun (y : expr ts) (H136 : @R_expr ts y (@UVar ts x)) =>
             match
               H136 in (@R_expr _ e0 e1)
               return
                 (e0 = y -> e1 = @UVar ts x -> @Acc (expr ts) (@R_expr ts) y)
             with
             | R_EqualL t l r =>
                 fun (H137 : l = y) (H138 : @Equal ts t l r = @UVar ts x) =>
                 match
                   match H137 in (_ = y0) return (y0 = l) with
                   | eq_refl => @eq_refl (expr ts) l
                   end in (_ = y0)
                   return
                     (@Equal ts t y0 r = @UVar ts x ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Equal ts t y r = @UVar ts x =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => True
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_EqualR t l r =>
                 fun (H137 : r = y) (H138 : @Equal ts t l r = @UVar ts x) =>
                 match
                   match H137 in (_ = y0) return (y0 = r) with
                   | eq_refl => @eq_refl (expr ts) r
                   end in (_ = y0)
                   return
                     (@Equal ts t l y0 = @UVar ts x ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Equal ts t l y = @UVar ts x =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => True
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_Not e0 =>
                 fun (H137 : e0 = y) (H138 : @Not ts e0 = @UVar ts x) =>
                 match
                   match H137 in (_ = y0) return (y0 = e0) with
                   | eq_refl => @eq_refl (expr ts) e0
                   end in (_ = y0)
                   return
                     (@Not ts y0 = @UVar ts x ->
                      @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H139 : @Not ts y = @UVar ts x =>
                     H34 (@Acc (expr ts) (@R_expr ts) y)
                       match
                         H139 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => False
                           | Equal _ _ _ => False
                           | Not _ => True
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H138
             | R_Func f args arg H137 =>
                 fun (H138 : arg = y) (H139 : @Func ts f args = @UVar ts x) =>
                 match
                   match H138 in (_ = y0) return (y0 = arg) with
                   | eq_refl => @eq_refl (expr ts) arg
                   end in (_ = y0)
                   return
                     (@Func ts f args = @UVar ts x ->
                      @In (expr ts) y0 args -> @Acc (expr ts) (@R_expr ts) y)
                 with
                 | eq_refl =>
                     fun H140 : @Func ts f args = @UVar ts x =>
                     H34
                       (@In (expr ts) y args -> @Acc (expr ts) (@R_expr ts) y)
                       match
                         H140 in (_ = y0)
                         return
                           match y0 with
                           | Const _ _ => False
                           | Var _ => False
                           | Func _ _ => True
                           | Equal _ _ _ => False
                           | Not _ => False
                           | UVar _ => False
                           end
                       with
                       | eq_refl => I
                       end
                 end H139 H137
             end (@eq_refl (expr ts) y) (@eq_refl (expr ts) (@UVar ts x)))
      end) a in
 let H137 :=
   fun (A : Type) (R : Relation_Definitions.relation A)
     (equiv : @Equivalence A R) (EqDec : @EqDec A R equiv) => EqDec in
 let H138 := fun A : Type => @eq_refl A in
 let H139 := fun A : Type => H129 A in
 let H140 :=
   fun (A : Type) (x y z : A) (H140 : x = y) (H141 : y = z) =>
   match H141 in (_ = y0) return (x = y0) with
   | eq_refl => H140
   end in
 let H141 := fun A : Type => H140 A in
 let H142 :=
   fun A : Type =>
   {|
   Equivalence_Reflexive := H138 A;
   Equivalence_Symmetric := H139 A;
   Equivalence_Transitive := H141 A |} in
 let H143 :=
   fun (P : tvar -> Type) (f : P tvProp) (f0 : forall n : nat, P (tvType n))
     (t : tvar) =>
   match t as t0 return (P t0) with
   | tvProp => f
   | tvType x => f0 x
   end in
 let H144 := fun P : tvar -> Set => H143 P in
 let H145 := fun (A : Type) (x : A) (P : A -> Set) => H35 A x P in
 let H146 :=
   fun (A : Type) (x : A) (P : A -> Set) (H146 : P x) (y : A) (H147 : y = x) =>
   H145 A x (fun y0 : A => P y0) H146 y (H129 A y x H147) in
 let H147 := fun P : nat -> Set => H133 P in
 let H148 :=
   fun n : nat =>
   H147 (fun n0 : nat => forall m : nat, {n0 = m} + {H32 (n0 = m)})
     (fun m : nat =>
      match m as n0 return ({0 = n0} + {0 <> n0}) with
      | 0 => @left (0 = 0) (H32 (0 = 0)) (@eq_refl nat 0)
      | S m0 => @right (0 = S m0) (H32 (0 = S m0)) (O_S m0)
      end)
     (fun (n0 : nat) (IHn : forall m : nat, {n0 = m} + {n0 <> m}) (m : nat) =>
      match m as n1 return ({S n0 = n1} + {S n0 <> n1}) with
      | 0 =>
          @right (S n0 = 0) (H32 (S n0 = 0))
            (@not_eq_sym nat 0 (S n0) (O_S n0))
      | S m0 =>
          H55 (n0 = m0) (H32 (n0 = m0))
            (fun _ : {n0 = m0} + {n0 <> m0} =>
             {S n0 = S m0} + {H32 (S n0 = S m0)})
            (fun a : n0 = m0 =>
             @left (S n0 = S m0) (H32 (S n0 = S m0)) (H131 nat nat S n0 m0 a))
            (fun b : n0 <> m0 =>
             @right (S n0 = S m0) (H32 (S n0 = S m0)) (not_eq_S n0 m0 b))
            (IHn m0)
      end) n in
 let H149 :=
   fun x y : tvar =>
   H144 (fun x0 : tvar => forall y0 : tvar, {x0 = y0} + {H32 (x0 = y0)})
     (fun y0 : tvar =>
      match y0 as t return ({tvProp = t} + {tvProp <> t}) with
      | tvProp =>
          @left (tvProp = tvProp) (H32 (tvProp = tvProp))
            (@eq_refl tvar tvProp)
      | tvType n =>
          @right (tvProp = tvType n) (H32 (tvProp = tvType n))
            (fun H149 : tvProp = tvType n =>
             (fun H150 : False => (fun H151 : False => H34 False H151) H150)
               (H36 tvar tvProp
                  (fun e : tvar =>
                   match e with
                   | tvProp => True
                   | tvType _ => False
                   end) I (tvType n) H149))
      end)
     (fun (n : nat) (y0 : tvar) =>
      match y0 as t return ({tvType n = t} + {tvType n <> t}) with
      | tvProp =>
          @right (tvType n = tvProp) (H32 (tvType n = tvProp))
            (fun H149 : tvType n = tvProp =>
             (fun H150 : False => (fun H151 : False => H34 False H151) H150)
               (H36 tvar (tvType n)
                  (fun e : tvar =>
                   match e with
                   | tvProp => False
                   | tvType _ => True
                   end) I tvProp H149))
      | tvType n0 =>
          H55 (n = n0) (H32 (n = n0))
            (fun _ : {n = n0} + {n <> n0} =>
             {tvType n = tvType n0} + {H32 (tvType n = tvType n0)})
            (fun a : n = n0 =>
             H146 nat n0
               (fun n1 : nat =>
                {tvType n1 = tvType n0} + {H32 (tvType n1 = tvType n0)})
               (@left (tvType n0 = tvType n0) (H32 (tvType n0 = tvType n0))
                  (@eq_refl tvar (tvType n0))) n a)
            (fun diseq : n <> n0 =>
             @right (tvType n = tvType n0) (H32 (tvType n = tvType n0))
               (fun absurd : tvType n = tvType n0 =>
                diseq
                  ((fun H149 : n = n0 => (fun H150 : n = n0 => H150) H149)
                     (H131 tvar nat
                        (fun e : tvar =>
                         match e with
                         | tvProp => n
                         | tvType n1 => n1
                         end) (tvType n) (tvType n0) absurd)))) 
            (H148 n n0)
      end) x y in
 let H150 := @None in
 let H151 := Some in
 let H152 :=
   fun A : Type =>
   fix nth_error (l : list A) (n : nat) {struct n} : 
   Exc A :=
     match n with
     | 0 => match l with
            | nil => H150 A
            | x :: _ => H151 A x
            end
     | S n0 => match l with
               | nil => H150 A
               | _ :: l0 => nth_error l0 n0
               end
     end in
 let H153 :=
   fun t : type =>
   let (Impl, Eqb, _) as t0 return (Impl t0 -> Impl t0 -> bool) := t in Eqb in
 let H154 :=
   fun (types : list type) (t : tvar) =>
   match t as t0 return (tvarD types t0 -> tvarD types t0 -> bool) with
   | tvProp => fun _ _ : tvarD types tvProp => false
   | tvType t0 =>
       match
         H152 type types t0 as k
         return
           (match k with
            | Some t1 => Impl t1
            | None => Empty_set
            end ->
            match k with
            | Some t1 => Impl t1
            | None => Empty_set
            end -> bool)
       with
       | Some t1 => H153 t1
       | None =>
           fun
             x
              _ : match @None type with
                  | Some t1 => Impl t1
                  | None => Empty_set
                  end => match x return bool with
                         end
       end
   end in
 let H155 :=
   fun (types : list type) (k : nat) (s : UNIFIER.FM.t (expr types)) =>
   H118 (expr types) k s in
 let H156 :=
   fun (A : Type) (P : A -> Type) (x : @sigT A P) => let (a, _) := x in a in
 let H157 :=
   fun (types : list type) (k : nat) (s : UNIFIER.Subst types) =>
   H155 types k
     (H156 (H113 (expr types))
        (fun this : UNIFIER.FM.t (expr types) => H120 types this) s) in
 let H158 :=
   fun (types : list type) (sub : UNIFIER.FM.t (expr types)) =>
   fix subst_exprInstantiate (e : expr types) : expr types :=
     match e with
     | Const _ _ => e
     | Var _ => e
     | Func f args =>
         @Func types f
           (H83 (expr types) (expr types) subst_exprInstantiate args)
     | Equal t l r =>
         @Equal types t (subst_exprInstantiate l) (subst_exprInstantiate r)
     | Not e0 => @Not types (subst_exprInstantiate e0)
     | UVar n => match H155 types n sub with
                 | Some v => v
                 | None => e
                 end
     end in
 let H159 := fun b1 b2 : bool => if b1 then true else b2 in
 let H160 :=
   fix beq_nat (n m : nat) {struct n} : bool :=
     match n with
     | 0 => match m with
            | 0 => true
            | S _ => false
            end
     | S n1 => match m with
               | 0 => false
               | S m1 => beq_nat n1 m1
               end
     end in
 let H161 :=
   fun (types : list type) (uv : uvar) =>
   fix mentionsU (e : expr types) : bool :=
     match e with
     | Const _ _ => false
     | Var _ => false
     | Func _ args =>
         (fix anyb (ls : list (expr types)) : bool :=
            match ls with
            | nil => false
            | l :: ls0 => H159 (mentionsU l) (anyb ls0)
            end) args
     | Equal _ l r => H159 (mentionsU l) (mentionsU r)
     | Not e0 => mentionsU e0
     | UVar n => if H160 uv n then true else false
     end in
 let H162 :=
   fun (elt : Type) (m : UNIFIER.FM.Raw.t elt) =>
   match m with
   | UNIFIER.FM.Raw.Leaf => H26
   | UNIFIER.FM.Raw.Node _ _ _ _ h => h
   end in
 let H163 :=
   fun (elt : Type) (l : UNIFIER.FM.Raw.t elt) (x : UNIFIER.FM.Raw.key)
     (e : elt) (r : UNIFIER.FM.Raw.t elt) =>
   @UNIFIER.FM.Raw.Node elt l x e r (H48 (H51 (H162 elt l) (H162 elt r)) H25) in
 let H164 := fun elt : Type => H163 elt in
 let H165 :=
   fun elt : Type =>
   fix bal (l : UNIFIER.FM.Raw.t elt) (x : UNIFIER.FM.Raw.key) 
           (d : elt) (r : UNIFIER.FM.Raw.t elt) {struct l} :
     UNIFIER.FM.Raw.t elt :=
     let hl := H162 elt l in
     let hr := H162 elt r in
     if H39 hl (H48 hr H49)
     then
      match l with
      | UNIFIER.FM.Raw.Leaf => H164 elt l x d r
      | UNIFIER.FM.Raw.Node ll lx ld lr _ =>
          if H68 (H162 elt ll) (H162 elt lr)
          then H163 elt ll lx ld (H163 elt lr x d r)
          else
           match lr with
           | UNIFIER.FM.Raw.Leaf => H164 elt l x d r
           | UNIFIER.FM.Raw.Node lrl lrx lrd lrr _ =>
               H163 elt (H163 elt ll lx ld lrl) lrx lrd (H163 elt lrr x d r)
           end
      end
     else
      if H39 hr (H48 hl H49)
      then
       match r with
       | UNIFIER.FM.Raw.Leaf => H164 elt l x d r
       | UNIFIER.FM.Raw.Node rl rx rd rr _ =>
           if H68 (H162 elt rr) (H162 elt rl)
           then H163 elt (H163 elt l x d rl) rx rd rr
           else
            match rl with
            | UNIFIER.FM.Raw.Leaf => H164 elt l x d r
            | UNIFIER.FM.Raw.Node rll rlx rld rlr _ =>
                H163 elt (H163 elt l x d rll) rlx rld (H163 elt rlr rx rd rr)
            end
       end
      else H163 elt l x d r in
 let H166 :=
   fun elt : Type =>
   fix add (x : UNIFIER.FM.Raw.key) (d : elt) (m : UNIFIER.FM.Raw.t elt)
           {struct m} : UNIFIER.FM.Raw.t elt :=
     match m with
     | UNIFIER.FM.Raw.Leaf =>
         @UNIFIER.FM.Raw.Node elt (UNIFIER.FM.Raw.Leaf elt) x d
           (UNIFIER.FM.Raw.Leaf elt) H25
     | UNIFIER.FM.Raw.Node l y d' r h =>
         match H22 x y with
         | OrderedType.LT _ => H165 elt (add x d l) y d' r
         | OrderedType.EQ _ => @UNIFIER.FM.Raw.Node elt l y d r h
         | OrderedType.GT _ => H165 elt l y d' (add x d r)
         end
     end in
 let H167 :=
   fun (elt : Type) (b : UNIFIER.FM.bst elt) =>
   let (this, is_bst) as b0
       return (@UNIFIER.FM.Raw.bst elt (@UNIFIER.FM.this elt b0)) := b in
   is_bst in
 let H168 :=
   fun (elt : Type) (x : UNIFIER.FM.key) (e : elt) (m : UNIFIER.FM.t elt) =>
   {|
   UNIFIER.FM.this := H166 elt x e (H117 elt m);
   UNIFIER.FM.is_bst := @UNIFIER.FM.Raw.Proofs.add_bst elt 
                          (H117 elt m) x e (H167 elt m) |} in
 let H169 :=
   fix map (elt elt' : Type) (f : elt -> elt') (m : UNIFIER.FM.Raw.t elt)
           {struct m} : UNIFIER.FM.Raw.t elt' :=
     match m with
     | UNIFIER.FM.Raw.Leaf => UNIFIER.FM.Raw.Leaf elt'
     | UNIFIER.FM.Raw.Node l x d r h =>
         @UNIFIER.FM.Raw.Node elt' (map elt elt' f l) x 
           (f d) (map elt elt' f r) h
     end in
 let H170 :=
   fun (elt elt' : Type) (f : elt -> elt') (m : UNIFIER.FM.t elt) =>
   {|
   UNIFIER.FM.this := H169 elt elt' f (H117 elt m);
   UNIFIER.FM.is_bst := @UNIFIER.FM.Raw.Proofs.map_bst elt elt' f
                          (H117 elt m) (H167 elt m) |} in
 let H171 :=
   fun (types : list type) (k : nat) (v : expr types)
     (s : UNIFIER.FM.t (expr types)) =>
   let v' := H158 types s v in
   if H161 types k v'
   then @None (H113 (expr types))
   else
    let s0 := H168 (expr types) k v' s in
    let s1 := H170 (expr types) (expr types) (H158 types s0) s0 in
    @Some (H113 (expr types)) s1 in
 let H172 :=
   fun (A : Type) (P : A -> Type) (x : @sigT A P) =>
   let (x0, h) as x0 return (P (@projT1 A P x0)) := x in h in
 let H173 :=
   fun (types : list type) (k : nat) (v : expr types)
     (s : UNIFIER.Subst types) =>
   match
     H171 types k v
       (H156 (H113 (expr types))
          (fun this : UNIFIER.FM.t (expr types) => H120 types this) s) as t
     return
       (@UNIFIER.subst_set types k v
          (@projT1 (UNIFIER.FM.t (expr types))
             (fun this : UNIFIER.FM.t (expr types) =>
              @UNIFIER.WellFormed types this) s) = t ->
        option
          (@sigT (UNIFIER.FM.t (expr types)) (@UNIFIER.WellFormed types)))
   with
   | Some s' =>
       fun
         pf : @UNIFIER.subst_set types k v
                (@projT1 (UNIFIER.FM.t (expr types))
                   (fun this : UNIFIER.FM.t (expr types) =>
                    @UNIFIER.WellFormed types this) s) =
              @Some (UNIFIER.FM.t (expr types)) s' =>
       @Some (@sigT (H113 (expr types)) (H120 types))
         (@existT (H113 (expr types)) (H120 types) s'
            (@UNIFIER.subst_set_wf types k v
               (H156 (H113 (expr types))
                  (fun this : UNIFIER.FM.t (expr types) => H120 types this) s)
               s'
               (H172 (H113 (expr types))
                  (fun this : UNIFIER.FM.t (expr types) => H120 types this) s)
               pf))
   | None =>
       fun
         _ : @UNIFIER.subst_set types k v
               (@projT1 (UNIFIER.FM.t (expr types))
                  (fun this : UNIFIER.FM.t (expr types) =>
                   @UNIFIER.WellFormed types this) s) =
             @None (UNIFIER.FM.t (expr types)) =>
       @None (@sigT (H113 (expr types)) (H120 types))
   end
     (@eq_refl (option (H113 (expr types)))
        (H171 types k v
           (H156 (H113 (expr types))
              (fun this : UNIFIER.FM.t (expr types) => H120 types this) s))) in
 let H174 :=
   fun A : Type =>
   fix In (a : A) (l : list A) {struct l} : Prop :=
     match l with
     | nil => False
     | b :: m => b = a \/ In a m
     end in
 let H175 :=
   fun (types : list type) (LS : list (expr types))
     (F : forall l : expr types,
          expr types ->
          UNIFIER.Subst types ->
          @In (expr types) l LS -> option (UNIFIER.Subst types)) =>
   fix dep_in (ls rs : list (expr types)) (sub : UNIFIER.Subst types)
              {struct ls} :
     (forall l : expr types, H173 (expr types) l ls -> H173 (expr types) l LS) ->
     option (H120 types) :=
     match
       ls as ls0
       return
         ((forall l : expr types,
           @In (expr types) l ls0 -> @In (expr types) l LS) ->
          option (UNIFIER.Subst types))
     with
     | nil =>
         match rs with
         | nil =>
             fun
               _ : forall l : expr types,
                   @In (expr types) l (@nil (expr types)) ->
                   @In (expr types) l LS => @Some (H121 types) sub
         | _ :: _ =>
             fun
               _ : forall l0 : expr types,
                   @In (expr types) l0 (@nil (expr types)) ->
                   @In (expr types) l0 LS => @None (H121 types)
         end
     | l :: ls0 =>
         match rs with
         | nil =>
             fun
               _ : forall l0 : expr types,
                   @In (expr types) l0 (l :: ls0) -> @In (expr types) l0 LS =>
             @None (H121 types)
         | r :: rs0 =>
             fun
               pf_trans : forall l0 : expr types,
                          @In (expr types) l0 (l :: ls0) ->
                          @In (expr types) l0 LS =>
             match
               F l r sub
                 (pf_trans l
                    (@or_introl (l = l)
                       ((fix In (a : expr types) (l0 : list (expr types))
                                {struct l0} : Prop :=
                           match l0 with
                           | nil => False
                           | b :: m => b = a \/ In a m
                           end) l ls0) (@eq_refl (expr types) l)))
             with
             | Some sub0 =>
                 dep_in ls0 rs0 sub0
                   (fun (ls1 : expr types) (pf : @In (expr types) ls1 ls0) =>
                    pf_trans ls1
                      (@or_intror (l = ls1) (H174 (expr types) ls1 ls0) pf))
             | None => @None (H121 types)
             end
         end
     end in
 let H176 :=
   fun (types : list type) (bound_l : nat * expr types)
     (recur : forall a_b : nat * expr types,
              @GenRec.R_pair nat (expr types) GenRec.R_nat 
                (@R_expr types) a_b bound_l ->
              expr types ->
              UNIFIER.Subst types -> option (UNIFIER.Subst types))
     (r : expr types) (sub : UNIFIER.Subst types) =>
   (let (bound, l) as bound_l0
        return
          ((forall a_b : nat * expr types,
            @GenRec.R_pair nat (expr types) GenRec.R_nat 
              (@R_expr types) a_b bound_l0 ->
            expr types -> UNIFIER.Subst types -> option (UNIFIER.Subst types)) ->
           option (UNIFIER.Subst types)) := bound_l in
    match
      l as l0
      return
        ((forall a_b : nat * expr types,
          @GenRec.R_pair nat (expr types) GenRec.R_nat 
            (@R_expr types) a_b (bound, l0) ->
          expr types -> UNIFIER.Subst types -> option (UNIFIER.Subst types)) ->
         option (UNIFIER.Subst types))
    with
    | Const t v =>
        let l0 := @Const types t v in
        match r with
        | Const t' v' =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Const types t v) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            match H137 tvar (@eq tvar) (H142 tvar) H149 t t' with
            | left pf =>
                match
                  pf in (_ = k)
                  return (tvarD types k -> option (UNIFIER.Subst types))
                with
                | eq_refl =>
                    fun v'0 : tvarD types t =>
                    if H154 types t v v'0
                    then @Some (H121 types) sub
                    else @None (H121 types)
                end v'
            | right _ => @None (H121 types)
            end
        | Var _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Const types t v) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Func _ _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Const types t v) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Equal _ _ _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Const types t v) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Not _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Const types t v) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | UVar u =>
            match H157 types u sub with
            | Some r' =>
                match
                  bound as bound0
                  return
                    ((forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound0, l0) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types)) ->
                     option (UNIFIER.Subst types))
                with
                | 0 =>
                    fun
                      _ : forall a_b : nat * expr types,
                          @GenRec.R_pair nat (expr types) GenRec.R_nat
                            (@R_expr types) a_b (0, l0) ->
                          expr types ->
                          UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                    @None (H121 types)
                | S bound0 =>
                    fun
                      recur0 : forall a_b : nat * expr types,
                               @GenRec.R_pair nat (expr types) GenRec.R_nat
                                 (@R_expr types) a_b 
                                 (S bound0, l0) ->
                               expr types ->
                               UNIFIER.Subst types ->
                               option (UNIFIER.Subst types) =>
                    recur0 (bound0, l0)
                      (@GenRec.L nat (expr types) GenRec.R_nat
                         (@R_expr types) bound0 (S bound0) l0 l0
                         (GenRec.R_S bound0)) r' sub
                end
            | None =>
                fun
                  _ : forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound, @Const types t v) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                H173 types u l0 sub
            end
        end
    | Var v =>
        let l0 := @Var types v in
        match r with
        | Const _ _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Var types v) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Var v' =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Var types v) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            if H148 v v' then @Some (H121 types) sub else @None (H121 types)
        | Func _ _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Var types v) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Equal _ _ _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Var types v) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Not _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Var types v) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | UVar u =>
            match H157 types u sub with
            | Some r' =>
                match
                  bound as bound0
                  return
                    ((forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound0, l0) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types)) ->
                     option (UNIFIER.Subst types))
                with
                | 0 =>
                    fun
                      _ : forall a_b : nat * expr types,
                          @GenRec.R_pair nat (expr types) GenRec.R_nat
                            (@R_expr types) a_b (0, l0) ->
                          expr types ->
                          UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                    @None (H121 types)
                | S bound0 =>
                    fun
                      recur0 : forall a_b : nat * expr types,
                               @GenRec.R_pair nat (expr types) GenRec.R_nat
                                 (@R_expr types) a_b 
                                 (S bound0, l0) ->
                               expr types ->
                               UNIFIER.Subst types ->
                               option (UNIFIER.Subst types) =>
                    recur0 (bound0, l0)
                      (@GenRec.L nat (expr types) GenRec.R_nat
                         (@R_expr types) bound0 (S bound0) l0 l0
                         (GenRec.R_S bound0)) r' sub
                end
            | None =>
                fun
                  _ : forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound, @Var types v) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                H173 types u l0 sub
            end
        end
    | Func f1 args1 =>
        let l0 := @Func types f1 args1 in
        match r with
        | Const _ _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Func types f1 args1) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Var _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Func types f1 args1) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Func f2 args2 =>
            fun
              recur0 : forall a_b : nat * expr types,
                       @GenRec.R_pair nat (expr types) GenRec.R_nat
                         (@R_expr types) a_b (bound, @Func types f1 args1) ->
                       expr types ->
                       UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            if H160 f1 f2
            then
             H175 types args1
               (fun (l1 r0 : expr types) (s : UNIFIER.Subst types)
                  (pf : @In (expr types) l1 args1) =>
                recur0 (bound, l1)
                  (@GenRec.R nat (expr types) GenRec.R_nat 
                     (@R_expr types) bound l1 (@Func types f1 args1)
                     (@R_Func types f1 args1 l1 pf)) r0 s) args1 args2 sub
               (fun (l1 : expr types) (pf : @In (expr types) l1 args1) => pf)
            else @None (H121 types)
        | Equal _ _ _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Func types f1 args1) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Not _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Func types f1 args1) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | UVar u =>
            match H157 types u sub with
            | Some r' =>
                match
                  bound as bound0
                  return
                    ((forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound0, l0) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types)) ->
                     option (UNIFIER.Subst types))
                with
                | 0 =>
                    fun
                      _ : forall a_b : nat * expr types,
                          @GenRec.R_pair nat (expr types) GenRec.R_nat
                            (@R_expr types) a_b (0, l0) ->
                          expr types ->
                          UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                    @None (H121 types)
                | S bound0 =>
                    fun
                      recur0 : forall a_b : nat * expr types,
                               @GenRec.R_pair nat (expr types) GenRec.R_nat
                                 (@R_expr types) a_b 
                                 (S bound0, l0) ->
                               expr types ->
                               UNIFIER.Subst types ->
                               option (UNIFIER.Subst types) =>
                    recur0 (bound0, l0)
                      (@GenRec.L nat (expr types) GenRec.R_nat
                         (@R_expr types) bound0 (S bound0) l0 l0
                         (GenRec.R_S bound0)) r' sub
                end
            | None =>
                fun
                  _ : forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound, @Func types f1 args1) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                H173 types u l0 sub
            end
        end
    | Equal t1 e1 f1 =>
        let l0 := @Equal types t1 e1 f1 in
        match r with
        | Const _ _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Equal types t1 e1 f1) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Var _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Equal types t1 e1 f1) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Func _ _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Equal types t1 e1 f1) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Equal t2 e2 f2 =>
            fun
              recur0 : forall a_b : nat * expr types,
                       @GenRec.R_pair nat (expr types) GenRec.R_nat
                         (@R_expr types) a_b (bound, @Equal types t1 e1 f1) ->
                       expr types ->
                       UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            if H137 tvar (@eq tvar) (H142 tvar) H149 t1 t2
            then
             match
               recur0 (bound, e1)
                 (@GenRec.R nat (expr types) GenRec.R_nat 
                    (@R_expr types) bound e1 (@Equal types t1 e1 f1)
                    (@R_EqualL types t1 e1 f1)) e2 sub
             with
             | Some sub0 =>
                 recur0 (bound, f1)
                   (@GenRec.R nat (expr types) GenRec.R_nat 
                      (@R_expr types) bound f1 (@Equal types t1 e1 f1)
                      (@R_EqualR types t1 e1 f1)) f2 sub0
             | None => @None (H121 types)
             end
            else @None (H121 types)
        | Not _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Equal types t1 e1 f1) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | UVar u =>
            match H157 types u sub with
            | Some r' =>
                match
                  bound as bound0
                  return
                    ((forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound0, l0) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types)) ->
                     option (UNIFIER.Subst types))
                with
                | 0 =>
                    fun
                      _ : forall a_b : nat * expr types,
                          @GenRec.R_pair nat (expr types) GenRec.R_nat
                            (@R_expr types) a_b (0, l0) ->
                          expr types ->
                          UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                    @None (H121 types)
                | S bound0 =>
                    fun
                      recur0 : forall a_b : nat * expr types,
                               @GenRec.R_pair nat (expr types) GenRec.R_nat
                                 (@R_expr types) a_b 
                                 (S bound0, l0) ->
                               expr types ->
                               UNIFIER.Subst types ->
                               option (UNIFIER.Subst types) =>
                    recur0 (bound0, l0)
                      (@GenRec.L nat (expr types) GenRec.R_nat
                         (@R_expr types) bound0 (S bound0) l0 l0
                         (GenRec.R_S bound0)) r' sub
                end
            | None =>
                fun
                  _ : forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound, @Equal types t1 e1 f1) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                H173 types u l0 sub
            end
        end
    | Not e1 =>
        let l0 := @Not types e1 in
        match r with
        | Const _ _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Not types e1) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Var _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Not types e1) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Func _ _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Not types e1) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Equal _ _ _ =>
            fun
              _ : forall a_b : nat * expr types,
                  @GenRec.R_pair nat (expr types) GenRec.R_nat
                    (@R_expr types) a_b (bound, @Not types e1) ->
                  expr types ->
                  UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            @None (H121 types)
        | Not e2 =>
            fun
              recur0 : forall a_b : nat * expr types,
                       @GenRec.R_pair nat (expr types) GenRec.R_nat
                         (@R_expr types) a_b (bound, @Not types e1) ->
                       expr types ->
                       UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
            recur0 (bound, e1)
              (@GenRec.R nat (expr types) GenRec.R_nat 
                 (@R_expr types) bound e1 (@Not types e1) 
                 (@R_Not types e1)) e2 sub
        | UVar u =>
            match H157 types u sub with
            | Some r' =>
                match
                  bound as bound0
                  return
                    ((forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound0, l0) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types)) ->
                     option (UNIFIER.Subst types))
                with
                | 0 =>
                    fun
                      _ : forall a_b : nat * expr types,
                          @GenRec.R_pair nat (expr types) GenRec.R_nat
                            (@R_expr types) a_b (0, l0) ->
                          expr types ->
                          UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                    @None (H121 types)
                | S bound0 =>
                    fun
                      recur0 : forall a_b : nat * expr types,
                               @GenRec.R_pair nat (expr types) GenRec.R_nat
                                 (@R_expr types) a_b 
                                 (S bound0, l0) ->
                               expr types ->
                               UNIFIER.Subst types ->
                               option (UNIFIER.Subst types) =>
                    recur0 (bound0, l0)
                      (@GenRec.L nat (expr types) GenRec.R_nat
                         (@R_expr types) bound0 (S bound0) l0 l0
                         (GenRec.R_S bound0)) r' sub
                end
            | None =>
                fun
                  _ : forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound, @Not types e1) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                H173 types u l0 sub
            end
        end
    | UVar u =>
        match r with
        | Const _ _ =>
            match H157 types u sub with
            | Some l' =>
                match
                  bound as bound0
                  return
                    ((forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound0, @UVar types u) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types)) ->
                     option (UNIFIER.Subst types))
                with
                | 0 =>
                    fun
                      _ : forall a_b : nat * expr types,
                          @GenRec.R_pair nat (expr types) GenRec.R_nat
                            (@R_expr types) a_b (0, @UVar types u) ->
                          expr types ->
                          UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                    @None (H121 types)
                | S bound0 =>
                    fun
                      recur0 : forall a_b : nat * expr types,
                               @GenRec.R_pair nat (expr types) GenRec.R_nat
                                 (@R_expr types) a_b
                                 (S bound0, @UVar types u) ->
                               expr types ->
                               UNIFIER.Subst types ->
                               option (UNIFIER.Subst types) =>
                    recur0 (bound0, l')
                      (@GenRec.L nat (expr types) GenRec.R_nat
                         (@R_expr types) bound0 (S bound0) l' 
                         (@UVar types u) (GenRec.R_S bound0)) r sub
                end
            | None =>
                fun
                  _ : forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound, @UVar types u) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                H173 types u r sub
            end
        | Var _ =>
            match H157 types u sub with
            | Some l' =>
                match
                  bound as bound0
                  return
                    ((forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound0, @UVar types u) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types)) ->
                     option (UNIFIER.Subst types))
                with
                | 0 =>
                    fun
                      _ : forall a_b : nat * expr types,
                          @GenRec.R_pair nat (expr types) GenRec.R_nat
                            (@R_expr types) a_b (0, @UVar types u) ->
                          expr types ->
                          UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                    @None (H121 types)
                | S bound0 =>
                    fun
                      recur0 : forall a_b : nat * expr types,
                               @GenRec.R_pair nat (expr types) GenRec.R_nat
                                 (@R_expr types) a_b
                                 (S bound0, @UVar types u) ->
                               expr types ->
                               UNIFIER.Subst types ->
                               option (UNIFIER.Subst types) =>
                    recur0 (bound0, l')
                      (@GenRec.L nat (expr types) GenRec.R_nat
                         (@R_expr types) bound0 (S bound0) l' 
                         (@UVar types u) (GenRec.R_S bound0)) r sub
                end
            | None =>
                fun
                  _ : forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound, @UVar types u) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                H173 types u r sub
            end
        | Func _ _ =>
            match H157 types u sub with
            | Some l' =>
                match
                  bound as bound0
                  return
                    ((forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound0, @UVar types u) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types)) ->
                     option (UNIFIER.Subst types))
                with
                | 0 =>
                    fun
                      _ : forall a_b : nat * expr types,
                          @GenRec.R_pair nat (expr types) GenRec.R_nat
                            (@R_expr types) a_b (0, @UVar types u) ->
                          expr types ->
                          UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                    @None (H121 types)
                | S bound0 =>
                    fun
                      recur0 : forall a_b : nat * expr types,
                               @GenRec.R_pair nat (expr types) GenRec.R_nat
                                 (@R_expr types) a_b
                                 (S bound0, @UVar types u) ->
                               expr types ->
                               UNIFIER.Subst types ->
                               option (UNIFIER.Subst types) =>
                    recur0 (bound0, l')
                      (@GenRec.L nat (expr types) GenRec.R_nat
                         (@R_expr types) bound0 (S bound0) l' 
                         (@UVar types u) (GenRec.R_S bound0)) r sub
                end
            | None =>
                fun
                  _ : forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound, @UVar types u) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                H173 types u r sub
            end
        | Equal _ _ _ =>
            match H157 types u sub with
            | Some l' =>
                match
                  bound as bound0
                  return
                    ((forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound0, @UVar types u) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types)) ->
                     option (UNIFIER.Subst types))
                with
                | 0 =>
                    fun
                      _ : forall a_b : nat * expr types,
                          @GenRec.R_pair nat (expr types) GenRec.R_nat
                            (@R_expr types) a_b (0, @UVar types u) ->
                          expr types ->
                          UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                    @None (H121 types)
                | S bound0 =>
                    fun
                      recur0 : forall a_b : nat * expr types,
                               @GenRec.R_pair nat (expr types) GenRec.R_nat
                                 (@R_expr types) a_b
                                 (S bound0, @UVar types u) ->
                               expr types ->
                               UNIFIER.Subst types ->
                               option (UNIFIER.Subst types) =>
                    recur0 (bound0, l')
                      (@GenRec.L nat (expr types) GenRec.R_nat
                         (@R_expr types) bound0 (S bound0) l' 
                         (@UVar types u) (GenRec.R_S bound0)) r sub
                end
            | None =>
                fun
                  _ : forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound, @UVar types u) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                H173 types u r sub
            end
        | Not _ =>
            match H157 types u sub with
            | Some l' =>
                match
                  bound as bound0
                  return
                    ((forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound0, @UVar types u) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types)) ->
                     option (UNIFIER.Subst types))
                with
                | 0 =>
                    fun
                      _ : forall a_b : nat * expr types,
                          @GenRec.R_pair nat (expr types) GenRec.R_nat
                            (@R_expr types) a_b (0, @UVar types u) ->
                          expr types ->
                          UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                    @None (H121 types)
                | S bound0 =>
                    fun
                      recur0 : forall a_b : nat * expr types,
                               @GenRec.R_pair nat (expr types) GenRec.R_nat
                                 (@R_expr types) a_b
                                 (S bound0, @UVar types u) ->
                               expr types ->
                               UNIFIER.Subst types ->
                               option (UNIFIER.Subst types) =>
                    recur0 (bound0, l')
                      (@GenRec.L nat (expr types) GenRec.R_nat
                         (@R_expr types) bound0 (S bound0) l' 
                         (@UVar types u) (GenRec.R_S bound0)) r sub
                end
            | None =>
                fun
                  _ : forall a_b : nat * expr types,
                      @GenRec.R_pair nat (expr types) GenRec.R_nat
                        (@R_expr types) a_b (bound, @UVar types u) ->
                      expr types ->
                      UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                H173 types u r sub
            end
        | UVar u0 =>
            if H160 u u0
            then
             fun
               _ : forall a_b : nat * expr types,
                   @GenRec.R_pair nat (expr types) GenRec.R_nat
                     (@R_expr types) a_b (bound, @UVar types u) ->
                   expr types ->
                   UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
             @Some (H121 types) sub
            else
             match H157 types u sub with
             | Some l' =>
                 match H157 types u0 sub with
                 | Some r' =>
                     match
                       bound as bound0
                       return
                         ((forall a_b : nat * expr types,
                           @GenRec.R_pair nat (expr types) GenRec.R_nat
                             (@R_expr types) a_b (bound0, @UVar types u) ->
                           expr types ->
                           UNIFIER.Subst types ->
                           option (UNIFIER.Subst types)) ->
                          option (UNIFIER.Subst types))
                     with
                     | 0 =>
                         fun
                           _ : forall a_b : nat * expr types,
                               @GenRec.R_pair nat (expr types) GenRec.R_nat
                                 (@R_expr types) a_b 
                                 (0, @UVar types u) ->
                               expr types ->
                               UNIFIER.Subst types ->
                               option (UNIFIER.Subst types) =>
                         @None (H121 types)
                     | S bound0 =>
                         fun
                           recur0 : forall a_b : nat * expr types,
                                    @GenRec.R_pair nat 
                                      (expr types) GenRec.R_nat
                                      (@R_expr types) a_b
                                      (S bound0, @UVar types u) ->
                                    expr types ->
                                    UNIFIER.Subst types ->
                                    option (UNIFIER.Subst types) =>
                         recur0 (bound0, l')
                           (@GenRec.L nat (expr types) GenRec.R_nat
                              (@R_expr types) bound0 
                              (S bound0) l' (@UVar types u)
                              (GenRec.R_S bound0)) r' sub
                     end
                 | None =>
                     fun
                       _ : forall a_b : nat * expr types,
                           @GenRec.R_pair nat (expr types) GenRec.R_nat
                             (@R_expr types) a_b (bound, @UVar types u) ->
                           expr types ->
                           UNIFIER.Subst types ->
                           option (UNIFIER.Subst types) =>
                     H173 types u0 l' sub
                 end
             | None =>
                 fun
                   _ : forall a_b : nat * expr types,
                       @GenRec.R_pair nat (expr types) GenRec.R_nat
                         (@R_expr types) a_b (bound, @UVar types u) ->
                       expr types ->
                       UNIFIER.Subst types -> option (UNIFIER.Subst types) =>
                 H173 types u (@UVar types u0) sub
             end
        end
    end) recur in
 let H177 :=
   fun (types : list type) (bound : nat) (l : expr types) =>
   H124 (nat * expr types)%type
     (@GenRec.R_pair nat (expr types) GenRec.R_nat (@R_expr types))
     (H125 (nat * expr types)%type
        (@GenRec.R_pair nat (expr types) GenRec.R_nat (@R_expr types)) 4
        (H132 nat (expr types) GenRec.R_nat (@R_expr types) H135 (H136 types)))
     (fun _ : nat * expr types =>
      expr types -> H121 types -> option (H121 types)) 
     (H176 types) (bound, l) in
 let H178 :=
   fun (types : list type) (U : nat) =>
   fix openForUnification (e : expr types) : expr types :=
     match e with
     | Const _ _ => e
     | Var v => @UVar types (H87 U v)
     | Func f es =>
         @Func types f (H83 (expr types) (expr types) openForUnification es)
     | Equal t l r =>
         @Equal types t (openForUnification l) (openForUnification r)
     | Not e0 => @Not types (openForUnification e0)
     | UVar _ => e
     end in
 let H179 := fun elt : Type => UNIFIER.FM.Raw.Leaf elt in
 let H180 :=
   fun elt : Type =>
   {|
   UNIFIER.FM.this := H179 elt;
   UNIFIER.FM.is_bst := UNIFIER.FM.Raw.Proofs.empty_bst elt |} in
 let H181 := fun types : list type => H180 (expr types) in
 let H182 :=
   fun (types : list type) (k : UNIFIER.FM.key) (v : expr types)
     (H182 : @UNIFIER.FM.MapsTo (expr types) k v
               (UNIFIER.FM.empty (expr types))) =>
   (fun
      H183 : forall (elt : Type) (x : UNIFIER.FM.key) (e : elt),
             @UNIFIER.FM.MapsTo elt x e (UNIFIER.FM.empty elt) -> False =>
    (fun H184 : False => H34 (H119 types (H180 (expr types)) v = true) H184)
      (H183 (expr types) k v H182))
     (fun (elt : Type) (x : UNIFIER.FM.key) (e : elt) =>
      match @UNIFIER.FACTS.empty_mapsto_iff elt x e with
      | conj x0 _ => x0
      end) in
 let H183 :=
   fun types : list type =>
   @existT (H113 (expr types)) (H120 types) (H181 types) (H182 types) in
 let H184 :=
   fun elt : Type =>
   fix cardinal (m : UNIFIER.FM.Raw.t elt) : nat :=
     match m with
     | UNIFIER.FM.Raw.Leaf => 0
     | UNIFIER.FM.Raw.Node l _ _ r _ => S (H87 (cardinal l) (cardinal r))
     end in
 let H185 :=
   fun (elt : Type) (m : UNIFIER.FM.t elt) => H184 elt (H117 elt m) in
 let H186 :=
   fun (types : list type) (s : UNIFIER.Subst types) =>
   H185 (expr types)
     (H156 (H113 (expr types))
        (fun this : UNIFIER.FM.t (expr types) => H120 types this) s) in
 let H187 :=
   fun types : list type =>
   fix checkAllInstantiated (from : nat) (ts : variables)
                            (sub : UNIFIER.Subst types) {struct ts} : bool :=
     match ts with
     | nil => true
     | _ :: ts0 =>
         if H157 types from sub
         then checkAllInstantiated (S from) ts0 sub
         else false
     end in
 let H188 :=
   fun (A : Type) (P : A -> bool) =>
   fix allb (ls : list A) : bool :=
     match ls with
     | nil => true
     | x :: ls' => if P x then allb ls' else false
     end in
 let H189 :=
   fun (types : list type) (p : ProverT types) =>
   let (Facts, _, _, Prove) as p0
       return (@Facts types p0 -> expr types -> bool) := p in
   Prove in
 let H190 :=
   fun (types : list type) (U_or_G : bool) (U G G' : nat)
     (sub : UNIFIER.Subst types) =>
   fix liftInstantiate (e : expr types) : expr types :=
     match e with
     | Const _ _ => e
     | Var v =>
         if H86 v G'
         then if U_or_G then @UVar types (H87 v U) else @Var types (H87 v G)
         else
          let idx := H93 (H87 U v) G' in
          match H157 types idx sub with
          | Some e0 => e0
          | None => @UVar types idx
          end
     | Func f es =>
         @Func types f (H83 (expr types) (expr types) liftInstantiate es)
     | Equal t l r => @Equal types t (liftInstantiate l) (liftInstantiate r)
     | Not e0 => @Not types (liftInstantiate e0)
     | UVar v =>
         match H157 types v sub with
         | Some e0 => e0
         | None => @UVar types v
         end
     end in
 let H191 :=
   fun (types : list type) (concl : Type) (l : SepLemma.lemma types concl) =>
   let (_, Hyps, _) := l in Hyps in
 let H192 :=
   fun (types : list type) (unify_bound : nat) (prover : ProverT types)
     (facts : @Facts types prover) (U_or_G : bool) 
     (firstUvar firstVar : nat) (lem : SEP_LEMMA.sepLemma types)
     (args key : exprs types) =>
   let numForalls := H11 tvar (H108 types (H101 types) lem) in
   match
     H112 (expr types) (H121 types) (expr types) (H177 types unify_bound)
       (H83 (expr types) (expr types) (H178 types firstUvar) key) args
       (H183 types)
   with
   | Some subst =>
       if H115 (H160 (H186 types subst) numForalls)
            (H187 types firstUvar (H108 types (H101 types) lem) subst)
       then
        if H188 (expr types) (H189 types prover facts)
             (H83 (expr types) (expr types)
                (H190 types U_or_G firstUvar firstVar 0 subst)
                (H191 types (H101 types) lem))
        then @Some (H121 types) subst
        else @None (H121 types)
       else @None (H121 types)
   | None => @None (H121 types)
   end in
 let H193 :=
   fun (elt : Type) (m : Unfolder.FM.Raw.tree elt) =>
   match m with
   | Unfolder.FM.Raw.Leaf => H26
   | Unfolder.FM.Raw.Node _ _ _ _ h => h
   end in
 let H194 :=
   fun (elt : Type) (l : Unfolder.FM.Raw.tree elt) 
     (x : Unfolder.FM.Raw.key) (e : elt) (r : Unfolder.FM.Raw.tree elt) =>
   @Unfolder.FM.Raw.Node elt l x e r
     (H48 (H51 (H193 elt l) (H193 elt r)) H25) in
 let H195 := fun elt : Type => H194 elt in
 let H196 :=
   fun elt : Type =>
   fix bal (l : Unfolder.FM.Raw.tree elt) (x : Unfolder.FM.Raw.key) 
           (d : elt) (r : Unfolder.FM.Raw.tree elt) {struct l} :
     Unfolder.FM.Raw.tree elt :=
     let hl := H193 elt l in
     let hr := H193 elt r in
     if H39 hl (H48 hr H49)
     then
      match l with
      | Unfolder.FM.Raw.Leaf => H195 elt l x d r
      | Unfolder.FM.Raw.Node ll lx ld lr _ =>
          if H68 (H193 elt ll) (H193 elt lr)
          then H194 elt ll lx ld (H194 elt lr x d r)
          else
           match lr with
           | Unfolder.FM.Raw.Leaf => H195 elt l x d r
           | Unfolder.FM.Raw.Node lrl lrx lrd lrr _ =>
               H194 elt (H194 elt ll lx ld lrl) lrx lrd (H194 elt lrr x d r)
           end
      end
     else
      if H39 hr (H48 hl H49)
      then
       match r with
       | Unfolder.FM.Raw.Leaf => H195 elt l x d r
       | Unfolder.FM.Raw.Node rl rx rd rr _ =>
           if H68 (H193 elt rr) (H193 elt rl)
           then H194 elt (H194 elt l x d rl) rx rd rr
           else
            match rl with
            | Unfolder.FM.Raw.Leaf => H195 elt l x d r
            | Unfolder.FM.Raw.Node rll rlx rld rlr _ =>
                H194 elt (H194 elt l x d rll) rlx rld (H194 elt rlr rx rd rr)
            end
       end
      else H194 elt l x d r in
 let H197 :=
   fun elt : Type =>
   fix add (x : Unfolder.FM.Raw.key) (d : elt) (m : Unfolder.FM.Raw.tree elt)
           {struct m} : Unfolder.FM.Raw.tree elt :=
     match m with
     | Unfolder.FM.Raw.Leaf =>
         @Unfolder.FM.Raw.Node elt (Unfolder.FM.Raw.Leaf elt) x d
           (Unfolder.FM.Raw.Leaf elt) H25
     | Unfolder.FM.Raw.Node l y d' r h =>
         match H22 x y with
         | OrderedType.LT _ => H196 elt (add x d l) y d' r
         | OrderedType.EQ _ => @Unfolder.FM.Raw.Node elt l y d r h
         | OrderedType.GT _ => H196 elt l y d' (add x d r)
         end
     end in
 let H198 := NatMap.IntMap.Raw.Proofs.add_bst in
 let H199 :=
   fun (elt : Type) (b : Unfolder.FM.bst elt) =>
   let (this, is_bst) as b0
       return (@Unfolder.FM.Raw.bst elt (@Unfolder.FM.this elt b0)) := b in
   is_bst in
 let H200 :=
   fun (elt : Type) (x : Unfolder.FM.key) (e : elt) (m : Unfolder.FM.t elt) =>
   {|
   Unfolder.FM.this := H197 elt x e (H106 elt m);
   Unfolder.FM.is_bst := H198 elt (H106 elt m) x e (H199 elt m) |} in
 let H201 := fun (A B : Type) (p : A * B) => let (_, y) := p in y in
 let H202 :=
   fun (types : list type)
     (l : SepLemma.lemma types (SEP_LEMMA.sepConcl types)) =>
   H201 (SEP.sexpr types) (SEP.sexpr types) (H103 types (H101 types) l) in
 let H203 :=
   fun A : Type =>
   fix rev (l : list A) : list A :=
     match l with
     | nil => @nil A
     | x :: l' => H12 A (rev l') (x :: @nil A)
     end in
 let H204 :=
   fun (types : list type) (unify_bound : nat) (prover : ProverT types)
     (facts : @Facts types prover) (hs : UNF.hintSide types)
     (s : UNF.unfoldingState types) =>
   let imps := H76 types (H97 types s) in
   let firstUvar := H11 tvar (H98 types s) in
   let firstVar := H11 tvar (H99 types s) in
   H100 (SepLemma.lemma types (H101 types)) (UNF.unfoldingState types)
     (fun h : SepLemma.lemma types (SEP_LEMMA.sepConcl types) =>
      match H104 types h with
      | SEP.Emp => @None (UNF.unfoldingState types)
      | SEP.Inj _ => @None (UNF.unfoldingState types)
      | SEP.Star _ _ => @None (UNF.unfoldingState types)
      | SEP.Exists _ _ => @None (UNF.unfoldingState types)
      | SEP.Func f args' =>
          match H107 (list (H3 types)) f imps with
          | Some argss =>
              let numForalls := H11 tvar (H108 types (H101 types) h) in
              H111 (H3 types) (UNF.unfoldingState types)
                (fun (args : exprs types) (argss0 : list (exprs types)) =>
                 match
                   H192 types unify_bound prover facts false firstUvar
                     firstVar h args args'
                 with
                 | Some subs =>
                     let impures' :=
                       H200 (list (H3 types)) f argss0
                         (H76 types (H97 types s)) in
                     let sh :=
                       {|
                       SH.impures := impures';
                       SH.pures := H77 types (H97 types s);
                       SH.other := H78 types (H97 types s) |} in
                     let (exs, sh') := H91 types (H202 types h) in
                     let sh'0 :=
                       H92 types
                         (H190 types false firstUvar firstVar 
                            (H11 tvar exs) subs) sh' in
                     @Some (UNF.unfoldingState types)
                       {|
                       UNF.Vars := H12 tvar (H99 types s) (H203 tvar exs);
                       UNF.UVars := H98 types s;
                       UNF.Heap := H79 types sh sh'0 |}
                 | None => @None (UNF.unfoldingState types)
                 end) argss
          | None => @None (UNF.unfoldingState types)
          end
      | SEP.Const _ => @None (UNF.unfoldingState types)
      end) hs in
 let H205 := 5 in
 let H206 :=
   fun (types : list type) (hs : UNF.hintSide types) (prover : ProverT types) =>
   fix forward (bound : nat) (facts : @Facts types prover)
               (s : UNF.unfoldingState types) {struct bound} :
     UNF.unfoldingState types * nat :=
     match bound with
     | 0 => (s, bound)
     | S bound' =>
         match H204 types H205 prover facts hs s with
         | Some s' => forward bound' facts s'
         | None => (s, bound)
         end
     end in
 let H207 :=
   fun (types : list type) (prover : ProverT types) 
     (hs : UNF.hintSide types) (bound : nat) (facts : @Facts types prover)
     (us : UNF.unfoldingState types) =>
   let '(res, n) := H206 types hs prover bound facts us in
        (res, H160 n bound) in
 let H208 :=
   fun (types : list type) (p : ProverT types) =>
   let (Facts, _, Learn, _) as p0
       return (@Facts types p0 -> exprs types -> @Facts types p0) := p in
   Learn in
 let H209 :=
   fun (types : list type) (unify_bound : nat) (prover : ProverT types)
     (facts : @Facts types prover) (hs : UNF.hintSide types)
     (s : UNF.unfoldingState types) =>
   let imps := H76 types (H97 types s) in
   let firstUvar := H11 tvar (H98 types s) in
   let firstVar := H11 tvar (H99 types s) in
   H100 (SepLemma.lemma types (H101 types)) (UNF.unfoldingState types)
     (fun h : SepLemma.lemma types (SEP_LEMMA.sepConcl types) =>
      match H202 types h with
      | SEP.Emp => @None (UNF.unfoldingState types)
      | SEP.Inj _ => @None (UNF.unfoldingState types)
      | SEP.Star _ _ => @None (UNF.unfoldingState types)
      | SEP.Exists _ _ => @None (UNF.unfoldingState types)
      | SEP.Func f args' =>
          match H107 (list (H3 types)) f imps with
          | Some argss =>
              H111 (H3 types) (UNF.unfoldingState types)
                (fun (args : exprs types) (argss0 : list (exprs types)) =>
                 match
                   H192 types unify_bound prover facts true firstUvar
                     firstVar h args args'
                 with
                 | Some subs =>
                     let impures' :=
                       H200 (list (H3 types)) f argss0
                         (H76 types (H97 types s)) in
                     let sh :=
                       {|
                       SH.impures := impures';
                       SH.pures := H77 types (H97 types s);
                       SH.other := H78 types (H97 types s) |} in
                     let (exs, sh') := H91 types (H104 types h) in
                     let sh'0 :=
                       H92 types
                         (H190 types true firstUvar firstVar 
                            (H11 tvar exs) subs) sh' in
                     @Some (UNF.unfoldingState types)
                       {|
                       UNF.Vars := H99 types s;
                       UNF.UVars := H12 tvar (H98 types s) (H203 tvar exs);
                       UNF.Heap := H79 types sh sh'0 |}
                 | None => @None (UNF.unfoldingState types)
                 end) argss
          | None => @None (UNF.unfoldingState types)
          end
      | SEP.Const _ => @None (UNF.unfoldingState types)
      end) hs in
 let H210 :=
   fun (types : list type) (hs : UNF.hintSide types) (prover : ProverT types) =>
   fix backward (bound : nat) (facts : @Facts types prover)
                (s : UNF.unfoldingState types) {struct bound} :
     UNF.unfoldingState types * nat :=
     match bound with
     | 0 => (s, bound)
     | S bound' =>
         match H209 types H205 prover facts hs s with
         | Some s' => backward bound' facts s'
         | None => (s, bound)
         end
     end in
 let H211 :=
   fun (types : list type) (prover : ProverT types) 
     (hs : UNF.hintSide types) (bound : nat) (facts : @Facts types prover)
     (us : UNF.unfoldingState types) =>
   let '(res, n) := H210 types hs prover bound facts us in
        (res, H160 n bound) in
 let H212 :=
   fun A : Type =>
   fix skipn (n : nat) (l : list A) {struct n} : list A :=
     match n with
     | 0 => l
     | S n0 => match l with
               | nil => @nil A
               | _ :: l0 => skipn n0 l0
               end
     end in
 let H213 :=
   fun (types : list type) (prover : ProverT types)
     (facts : @Facts types prover) (hintsFwd hintsBwd : UNF.hintSide types)
     (uvars ql : list tvar) (lhs rhs : SH.SHeap types) =>
   let pre := {| UNF.Vars := ql; UNF.UVars := uvars; UNF.Heap := lhs |} in
   let (u, fprog) := H207 types prover hintsFwd 10 facts pre in
   match u with
   | {| UNF.Vars := vars'; UNF.UVars := uvars'; UNF.Heap := lhs0 |} =>
       let post :=
         {| UNF.Vars := vars'; UNF.UVars := uvars'; UNF.Heap := rhs |} in
       let facts' := H208 types prover facts (H77 types lhs0) in
       let (u0, bprog) := H211 types prover hintsBwd 10 facts' post in
       match u0 with
       | {| UNF.Vars := vars'0; UNF.UVars := uvars'0; UNF.Heap := rhs0 |} =>
           let new_vars := H212 tvar (H11 tvar ql) vars'0 in
           let new_uvars := H212 tvar (H11 tvar uvars) uvars'0 in
           let bound := H11 tvar uvars'0 in
           ({|
            CANCEL_LOOP.UNF_TAC.Alls := new_vars;
            CANCEL_LOOP.UNF_TAC.Exs := new_uvars;
            CANCEL_LOOP.UNF_TAC.Lhs := lhs0;
            CANCEL_LOOP.UNF_TAC.Rhs := rhs0;
            CANCEL_LOOP.UNF_TAC.Know := facts' |}, 
           H159 fprog bprog)
       end
   end in
 let H214 :=
   fun (types : list type) (prover : ProverT types)
     (P : @CANCEL_LOOP.UNF_TAC.unfolderResult types prover -> Type)
     (f : forall (Alls Exs : list tvar) (Lhs Rhs : SH.SHeap types)
            (Know : @Facts types prover),
          P
            {|
            CANCEL_LOOP.UNF_TAC.Alls := Alls;
            CANCEL_LOOP.UNF_TAC.Exs := Exs;
            CANCEL_LOOP.UNF_TAC.Lhs := Lhs;
            CANCEL_LOOP.UNF_TAC.Rhs := Rhs;
            CANCEL_LOOP.UNF_TAC.Know := Know |})
     (u : @CANCEL_LOOP.UNF_TAC.unfolderResult types prover) =>
   match u as u0 return (P u0) with
   | {| CANCEL_LOOP.UNF_TAC.Alls := x; CANCEL_LOOP.UNF_TAC.Exs := x0;
     CANCEL_LOOP.UNF_TAC.Lhs := x1; CANCEL_LOOP.UNF_TAC.Rhs := x2;
     CANCEL_LOOP.UNF_TAC.Know := x3 |} => f x x0 x1 x2 x3
   end in
 let H215 := fun types : list type => list (H3 types * nat) in
 let H216 :=
   fun (A B : Type) (f : A -> B -> A) =>
   fix fold_left (l : list B) (a0 : A) {struct l} : A :=
     match l with
     | nil => a0
     | b :: t => fold_left t (f a0 b)
     end in
 let H217 :=
   fun (T : Type) (cmp : T -> T -> comparison) (val : T) =>
   fix insert_in_order (ls : list T) : list T :=
     match ls with
     | nil => val :: @nil T
     | l :: ls' =>
         match cmp val l with
         | Datatypes.Eq => val :: ls
         | Datatypes.Lt => val :: ls
         | Datatypes.Gt => l :: insert_in_order ls'
         end
     end in
 let H218 := nat in
 let H219 :=
   fun types : list type =>
   fix expr_count_meta (e : expr types) : nat :=
     match e with
     | Const _ _ => 0
     | Var _ => 0
     | Func _ args =>
         H216 nat nat H87 (H83 (expr types) nat expr_count_meta args) 0
     | Equal _ l r => H87 (expr_count_meta l) (expr_count_meta r)
     | Not l => expr_count_meta l
     | UVar _ => 1
     end in
 let H220 :=
   fun types : list type =>
   fix exprs_count_meta (es : exprs types) : nat :=
     match es with
     | nil => 0
     | e :: es' => H87 (H219 types e) (exprs_count_meta es')
     end in
 let H221 :=
   fun (T : Type) (cmp : T -> T -> comparison) =>
   fix list_lex_cmp (ls rs : list T) {struct ls} : comparison :=
     match ls with
     | nil =>
         match rs with
         | nil => Datatypes.Eq
         | _ :: _ => Datatypes.Lt
         end
     | l :: ls0 =>
         match rs with
         | nil => Datatypes.Gt
         | r :: rs0 =>
             match cmp l r with
             | Datatypes.Eq => list_lex_cmp ls0 rs0
             | Datatypes.Lt => Datatypes.Lt
             | Datatypes.Gt => Datatypes.Gt
             end
         end
     end in
 let H222 :=
   fun types : list type =>
   fix expr_size (e : expr types) : nat :=
     match e with
     | Const _ _ => 0
     | Var _ => 0
     | Func _ args =>
         H216 nat nat H87 (H83 (expr types) nat expr_size args) 1
     | Equal _ l r => S (H87 (expr_size l) (expr_size r))
     | Not l => S (expr_size l)
     | UVar _ => 0
     end in
 let H223 :=
   fun (types : list type) (l r : exprs types) =>
   match H18 (H220 types l) (H220 types r) with
   | Datatypes.Eq =>
       H221 (expr types)
         (fun l0 r0 : expr types => H18 (H222 types l0) (H222 types r0)) l r
   | Datatypes.Lt => Datatypes.Lt
   | Datatypes.Gt => Datatypes.Gt
   end in
 let H224 :=
   fun (types : list type) (l r : exprs types * func) =>
   match H201 (H3 types) H218 l with
   | 0 =>
       match
         H223 types (H102 (H3 types) H218 l) (H102 (H3 types) H218 r)
       with
       | Datatypes.Eq =>
           H18 (H201 (H3 types) H218 l) (H201 (H3 types) H218 r)
       | Datatypes.Lt => Datatypes.Lt
       | Datatypes.Gt => Datatypes.Gt
       end
   | 1 =>
       match
         H223 types (H102 (H3 types) H218 l) (H102 (H3 types) H218 r)
       with
       | Datatypes.Eq =>
           H18 (H201 (H3 types) H218 l) (H201 (H3 types) H218 r)
       | Datatypes.Lt => Datatypes.Lt
       | Datatypes.Gt => Datatypes.Gt
       end
   | 2 =>
       match H201 (H3 types) H218 r with
       | 0 => Datatypes.Lt
       | 1 => Datatypes.Lt
       | 2 =>
           match
             H223 types (H102 (H3 types) H218 l) (H102 (H3 types) H218 r)
           with
           | Datatypes.Eq =>
               H18 (H201 (H3 types) H218 l) (H201 (H3 types) H218 r)
           | Datatypes.Lt => Datatypes.Lt
           | Datatypes.Gt => Datatypes.Gt
           end
       | S (S (S _)) => Datatypes.Lt
       end
   | S (S (S _)) =>
       match
         H223 types (H102 (H3 types) H218 l) (H102 (H3 types) H218 r)
       with
       | Datatypes.Eq =>
           H18 (H201 (H3 types) H218 l) (H201 (H3 types) H218 r)
       | Datatypes.Lt => Datatypes.Lt
       | Datatypes.Gt => Datatypes.Gt
       end
   end in
 let H225 := nat in
 let H226 :=
   fun (types : list type) (imps : SepHeap.MM.mmap (exprs types)) =>
   H15 (list (H3 types)) (H215 types)
     (fun k : SepHeap.FM.key =>
      H216 (H215 types) (H3 types)
        (fun (acc : CANCEL_LOOP.CANCEL.cancel_list types)
           (args : exprs types) =>
         H217 (H3 types * H218)%type (H224 types) (args, k) acc)) imps
     (@nil (H3 types * nat)) in
 let H227 :=
   fun (T : Type) (cmp : T -> T -> comparison) =>
   fix sort (ls : list T) : list T :=
     match ls with
     | nil => @nil T
     | l :: ls0 => H217 T cmp l (sort ls0)
     end in
 let H228 := list tvar in
 let H229 :=
   fun (T U V A : Type) (F : T -> U -> V -> A -> option A) =>
   fix fold_left_3_opt (ls : list T) (ls' : list U) 
                       (ls'' : list V) (acc : A) {struct ls} : 
   option A :=
     match ls with
     | nil =>
         match ls' with
         | nil =>
             match ls'' with
             | nil => @Some A acc
             | _ :: _ => @None A
             end
         | _ :: _ => @None A
         end
     | x :: xs =>
         match ls' with
         | nil => @None A
         | y :: ys =>
             match ls'' with
             | nil => @None A
             | z :: zs =>
                 match F x y z acc with
                 | Some acc0 => fold_left_3_opt xs ys zs acc0
                 | None => @None A
                 end
             end
         end
     end in
 let H230 :=
   fun (types : list type) (sub : UNIFIER.Subst types) =>
   H158 types
     (H156 (H113 (expr types))
        (fun this : UNIFIER.FM.t (expr types) => H120 types this) sub) in
 let H231 :=
   fun (types : list type) (Prover : ProverT types) 
     (bound : nat) (summ : @Facts types Prover) (l r : list (expr types))
     (ts : list tvar) (sub : UNIFIER.Subst types) =>
   H229 (expr types) (expr types) tvar (H121 types)
     (fun (l0 r0 : expr types) (t : tvar) (acc : UNIFIER.Subst types) =>
      if H189 types Prover summ
           (@Equal types t (H230 types acc l0) (H230 types acc r0))
      then @Some (H121 types) acc
      else H177 types bound l0 r0 acc) l r ts sub in
 let H232 :=
   fun (types : list type) (Prover : ProverT types) =>
   fix unify_remove (bound : nat) (summ : @Facts types Prover)
                    (l : exprs types) (ts : list tvar)
                    (r : list (exprs types)) (sub : UNIFIER.Subst types)
                    {struct r} :
     option (list (list (expr types)) * H120 types) :=
     match r with
     | nil => @None (list (list (expr types)) * H121 types)
     | a :: b =>
         match H231 types Prover bound summ l a ts sub with
         | Some sub0 => @Some (list (H3 types) * H121 types) (b, sub0)
         | None =>
             match unify_remove bound summ l ts b sub with
             | Some (x, sub0) =>
                 @Some (list (H3 types) * H121 types) (a :: x, sub0)
             | None => @None (list (list (expr types)) * H121 types)
             end
         end
     end in
 let H233 :=
   fun (types : list type) (Prover : ProverT types) =>
   fix cancel_in_order (bound : nat) (summ : @Facts types Prover)
                       (tpreds : SEP.tpredicates)
                       (ls : CANCEL_LOOP.CANCEL.cancel_list types)
                       (acc rem : SepHeap.MM.mmap (exprs types))
                       (sub : UNIFIER.Subst types) 
                       (progress : bool) {struct ls} :
     option (H16 (H2 types) * H16 (H2 types) * H120 types) :=
     match ls with
     | nil =>
         if progress
         then
          @Some (H17 (H3 types) * H17 (H3 types) * H121 types)
            (acc, rem, sub)
         else @None (H17 (H3 types) * H17 (H3 types) * H121 types)
     | (args, f) :: ls0 =>
         match H24 (list (H3 types)) f rem with
         | Some argss =>
             match H152 H228 tpreds f with
             | Some ts =>
                 match H232 types Prover bound summ args ts argss sub with
                 | Some (rem', sub0) =>
                     cancel_in_order bound summ tpreds ls0 acc
                       (H73 (list (list (expr types))) f rem' rem) sub0 true
                 | None =>
                     cancel_in_order bound summ tpreds ls0
                       (H90 (H3 types) f args acc) rem sub progress
                 end
             | None =>
                 cancel_in_order bound summ tpreds ls0
                   (H90 (H3 types) f args acc) rem sub progress
             end
         | None =>
             cancel_in_order bound summ tpreds ls0
               (H90 (H3 types) f args acc) rem sub progress
         end
     end in
 let H234 :=
   fun (types : list type) (Prover : ProverT types) 
     (bound : nat) (tpreds : SEP.tpredicates) (summ : @Facts types Prover)
     (l r : SH.SHeap types) (s : UNIFIER.Subst types) =>
   let ordered_r := H226 types (H76 types r) in
   let sorted_l :=
     H82 (list (H3 types)) (list (H3 types))
       (fun v : list (exprs types) => H227 (H3 types) (H223 types) v)
       (H76 types l) in
   match
     H233 types Prover bound summ tpreds ordered_r 
       (H2 (H3 types)) sorted_l s false
   with
   | Some (rf, lf, sub) =>
       @Some (SH.SHeap types * SH.SHeap types * H121 types)
         ({|
          SH.impures := lf;
          SH.pures := H77 types l;
          SH.other := H78 types l |},
         {|
         SH.impures := rf;
         SH.pures := H77 types r;
         SH.other := H78 types r |}, sub)
   | None => @None (SH.SHeap types * SH.SHeap types * H121 types)
   end in
 let H235 :=
   fun (types : list type) (prover : ProverT types) =>
   let bound := 10 in
   fun (tpreds : SEP.tpredicates) (facts : @Facts types prover)
     (lhs rhs : SH.SHeap types) (sub : CANCEL_LOOP.CANCEL.U.Subst types) =>
   match H234 types prover bound tpreds facts lhs rhs sub with
   | Some (l, r, s) =>
       ({|
        CANCEL_LOOP.CANCEL_TAC.Lhs := l;
        CANCEL_LOOP.CANCEL_TAC.Rhs := r;
        CANCEL_LOOP.CANCEL_TAC.Subst := s |}, true)
   | None =>
       ({|
        CANCEL_LOOP.CANCEL_TAC.Lhs := lhs;
        CANCEL_LOOP.CANCEL_TAC.Rhs := rhs;
        CANCEL_LOOP.CANCEL_TAC.Subst := sub |}, false)
   end in
 let H236 :=
   fun (ts : list type) (tpreds : SEP.tpredicates) 
     (prover : ProverT ts) (hintsFwd hintsBwd : UNF.hintSide ts) =>
   fix cancelLoop (n : nat) (facts : @Facts ts prover)
                  (uvars vars : list tvar) (l r : SH.SHeap ts)
                  (sub : UNIFIER.Subst ts) (prog : bool) {struct n} :
     CANCEL_LOOP.cancelResult ts * bool :=
     match n with
     | 0 =>
         let Lhs' :=
           {|
           SH.impures := H76 ts l;
           SH.pures := @nil (expr ts);
           SH.other := H78 ts l |} in
         (@CANCEL_LOOP.Quant ts (@nil tvar) (H77 ts l) 
            (@nil tvar) sub (@CANCEL_LOOP.Done ts Lhs' r), true)
     | S n0 =>
         let '(unf, prog') :=
              H213 ts prover facts hintsFwd hintsBwd uvars vars l r in
              H214 ts prover
                (fun _ : @CANCEL_LOOP.UNF_TAC.unfolderResult ts prover =>
                 (CANCEL_LOOP.cancelResult ts * bool)%type)
                (fun (alls exs : list tvar) (lhs rhs : SH.SHeap ts)
                   (know : @Facts ts prover) =>
                 let '(cncl, prog'') :=
                      H235 ts prover tpreds know lhs rhs sub in
                      if H159 prog' prog''
                      then
                       match cncl with
                       | {| CANCEL_LOOP.CANCEL_TAC.Lhs := Lhs;
                         CANCEL_LOOP.CANCEL_TAC.Rhs := Rhs;
                         CANCEL_LOOP.CANCEL_TAC.Subst := Subst |} =>
                           let Lhs' :=
                             {|
                             SH.impures := H76 ts Lhs;
                             SH.pures := @nil (expr ts);
                             SH.other := H78 ts Lhs |} in
                           let '(res, p) :=
                                cancelLoop n0 know 
                                  (H12 tvar uvars exs) 
                                  (H12 tvar vars alls) Lhs' Rhs Subst true in
                                (@CANCEL_LOOP.Quant ts alls 
                                   (H77 ts Lhs) exs Subst res, p)
                       end
                      else (@CANCEL_LOOP.Done ts l r, prog)) unf
     end in
 let H237 :=
   fun (ts : list type) (tpreds : SEP.tpredicates) 
     (prover : ProverT ts) (hintsFwd hintsBwd : UNF.hintSide ts) 
     (n : nat) (hyps : exprs ts) (tuvars _ : list tvar) 
     (l r : SEP.sexpr ts) =>
   let '(ql, lhs) := H91 ts l in
        let '(qr, rhs) := H91 ts r in
             let rhs0 := H95 ts 0 (H11 tvar qr) (H11 tvar tuvars) rhs in
             let facts := H96 ts prover (H12 (expr ts) hyps (H77 ts lhs)) in
             let lhs' :=
               {|
               SH.impures := H76 ts lhs;
               SH.pures := @nil (expr ts);
               SH.other := H78 ts lhs |} in
             let '(cr', prog') :=
                  H236 ts tpreds prover hintsFwd hintsBwd n facts
                    (H12 tvar tuvars (H203 tvar qr)) 
                    (H203 tvar ql) lhs' rhs0 (H183 ts) false in
                  match ql with
                  | nil =>
                      match qr with
                      | nil =>
                          match H77 ts lhs with
                          | nil => (cr', prog')
                          | e :: l0 =>
                              (@CANCEL_LOOP.Quant ts 
                                 (H203 tvar ql) (e :: l0) 
                                 (H203 tvar qr) (H183 ts) cr', true)
                          end
                      | _ :: _ =>
                          (@CANCEL_LOOP.Quant ts (H203 tvar ql) 
                             (H77 ts lhs) (H203 tvar qr) 
                             (H183 ts) cr', true)
                      end
                  | _ :: _ =>
                      (@CANCEL_LOOP.Quant ts (H203 tvar ql) 
                         (H77 ts lhs) (H203 tvar qr) 
                         (H183 ts) cr', true)
                  end in
 H237)).
    localize CANCEL_LOOP.cancel.
    Set Printing Implicit.
    Set Printing Depth 1000.
    Show Proof.
  Defined.

  Theorem ApplyCancelSep_with_eq1 :
    forall (funcs : functions types) (preds : SEP.predicates types)
      (algos : TacPackIL.ILAlgoTypes.AllAlgos types)
      (algosC : @TacPackIL.ILAlgoTypes.AllAlgos_correct types funcs preds algos)
      (uvars : env types) (lhs rhs : SEP.sexpr types)
      (hyps : exprs types)
      (cr : CANCEL_LOOP.cancelResult types),
      AllProvable funcs uvars nil hyps ->
      (let bound := 10 in
       let hints :=
         match TacPackIL.ILAlgoTypes.Hints algos with
           | None => {| UNF.Forward := nil ; UNF.Backward := nil |}
           | Some x => x
         end
       in
       let prover :=
         match TacPackIL.ILAlgoTypes.Prover algos with
           | None => Provers.trivialProver types
           | Some x => x
         end
       in
       let '(x,y) :=
         CANCEL_LOOP.cancel (SEP.typeof_preds preds) prover (UNF.Forward hints) (UNF.Backward hints)
         bound hyps (typeof_env uvars) nil lhs rhs in
       (x, SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env uvars) nil rhs && y) = (cr, true)) ->
      CANCEL_LOOP.cancelResultD funcs preds uvars nil cr ->
      SEP.himp funcs preds uvars nil lhs rhs.
  Proof.
  Admitted.

  Theorem ApplyCancelSep_with_eq2 :
    forall (funcs : functions types) (preds : SEP.predicates types)
      (algos : TacPackIL.ILAlgoTypes.AllAlgos types)
      (algosC : @TacPackIL.ILAlgoTypes.AllAlgos_correct types funcs preds algos)
      (uvars : env types) (lhs rhs : SEP.sexpr types)
      (hyps : exprs types),
      AllProvable funcs uvars nil hyps ->
      (let bound := 10 in
       let hints :=
         match TacPackIL.ILAlgoTypes.Hints algos with
           | None => {| UNF.Forward := nil ; UNF.Backward := nil |}
           | Some x => x
         end
       in
       let prover :=
         match TacPackIL.ILAlgoTypes.Prover algos with
           | None => Provers.trivialProver types
           | Some x => x
         end
       in
       let '(x,y) :=
         CANCEL_LOOP.cancel (SEP.typeof_preds preds) prover (UNF.Forward hints) (UNF.Backward hints)
         bound hyps (typeof_env uvars) nil lhs rhs in
       if SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env uvars) nil rhs && y then
         CANCEL_LOOP.cancelResultD funcs preds uvars nil x
       else
         SEP.himp funcs preds uvars nil lhs rhs) ->      
      SEP.himp funcs preds uvars nil lhs rhs.
  Proof.
  Admitted.



(*
  Theorem ApplyCancelSep_with_eq1 :
    forall (funcs : functions types)
      (preds : SEP.predicates types) (prover : ProverT types)
      (algos : TacPackIL.ILAlgoTypes.AllAlgos types)
      (algosC : @TacPackIL.ILAlgoTypes.AllAlgos_correct types funcs preds algos)
      (uvars : env types) (lhs rhs : SEP.sexpr types)
      (hyps : exprs types) (tfuncs : tfunctions)
      (tpreds : SEP.tpredicates) (tuvars : tenv)
      (cr : CANCEL_LOOP.cancelResult types) (prog : bool),
      ProverT_correct prover funcs ->
      typeof_funcs funcs = tfuncs ->
      SEP.typeof_preds preds = tpreds ->
      WellTyped_env tuvars uvars ->
      SEP.WellTyped_sexpr tfuncs tpreds tuvars nil rhs = true ->
      AllProvable funcs uvars nil hyps ->
      (let bound := 10 in
       let hints :=
         match TacPackIL.ILAlgoTypes.Hints algos with
           | None => {| UNF.Forward := nil ; UNF.Backward := nil |}
           | Some x => x
         end
       in
       CANCEL_LOOP.cancel tpreds prover (UNF.Forward hints) (UNF.Backward hints) bound hyps tuvars nil lhs rhs = (cr, prog))
      ->
      (if prog
        then CANCEL_LOOP.cancelResultD funcs preds uvars nil cr
        else SEP.himp funcs preds uvars nil lhs rhs) ->
      SEP.himp funcs preds uvars nil lhs rhs.
  Proof.
    exact CANCEL_LOOP.cancelLoop_with_eq'.
  Qed.
*)
  
(*
  Print CANCEL_LOOP.
  

  Lemma ApplyCancelSep_with_eq : 
    forall (algos_correct : ILAlgoTypes.AllAlgos_correct funcs preds algos),
    forall (meta_env : Expr.env (Env.repr BedrockCoreEnv.core types)) (hyps : Expr.exprs (_)),

    forall (l r : SEP.sexpr types BedrockCoreEnv.pc BedrockCoreEnv.st) res,
    Expr.AllProvable funcs meta_env nil hyps ->
    canceller preds algos (typeof_env meta_env) hyps l r = Some res ->
    forall (WTR : SEP.WellTyped_sexpr (typeof_funcs funcs) (SEP.typeof_preds preds) (typeof_env meta_env) nil r = true) cs,
    match res with
      | {| AllExt := new_vars
         ; ExExt  := new_uvars
         ; Lhs    := lhs'
         ; Rhs    := rhs'
         ; Subst  := subst
         |} =>
        Expr.forallEach new_vars (fun nvs : Expr.env types =>
          let var_env := nvs in
          Expr.AllProvable_impl funcs meta_env var_env
          (existsSubst funcs var_env subst 0 
            (map (fun x => existT (fun t => option (tvarD types t)) (projT1 x) (Some (projT2 x))) meta_env ++
             map (fun x => existT (fun t => option (tvarD types t)) x None) new_uvars)
            (fun meta_env : Expr.env types =>
                (Expr.AllProvable_and funcs meta_env var_env
                  (himp cs 
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures lhs') nil (SH.other lhs'))))
                    (SEP.sexprD funcs preds meta_env var_env
                      (SH.sheapD (SH.Build_SHeap _ _ (SH.impures rhs') nil (SH.other rhs')))))
                  (SH.pures rhs')) ))
            (SH.pures lhs'))
    end ->
    himp cs (@SEP.sexprD _ _ _ funcs preds meta_env nil l)
            (@SEP.sexprD _ _ _ funcs preds meta_env nil r).
  Proof. intros. eapply ApplyCancelSep_with_eq'; eauto. Qed.
*)

  Lemma ApplyCancelSep : forall (types : list type) (funcs : functions types)
      (preds : SEP.predicates types) (prover : ProverT types)
      (hintsFwd hintsBwd : list (SEP_LEMMA.sepLemma types)) 
      (bound : nat) (uvars : env types) (lhs rhs : SEP.sexpr types)
      (hyps : exprs types) (tfuncs : tfunctions)
      (tpreds : SEP.tpredicates) (tuvars : tenv),
      ProverT_correct prover funcs ->
      typeof_funcs funcs = tfuncs ->
      SEP.typeof_preds preds = tpreds ->
      WellTyped_env tuvars uvars ->
      SEP.WellTyped_sexpr tfuncs tpreds tuvars nil rhs = true ->
      AllProvable funcs uvars nil hyps ->
      UNF.hintSideD funcs preds hintsFwd ->
      UNF.hintSideD funcs preds hintsBwd ->
      let '(cr,prog) := CANCEL_LOOP.cancel tpreds prover hintsFwd hintsBwd bound hyps tuvars nil lhs rhs in
      match prog with
        | true => CANCEL_LOOP.cancelResultD funcs preds uvars nil cr
        | false => SEP.himp funcs preds uvars nil lhs rhs
      end ->
      SEP.himp funcs preds uvars nil lhs rhs.
  Proof. 
    intros. consider (CANCEL_LOOP.cancel tpreds prover hintsFwd hintsBwd bound hyps tuvars nil lhs rhs); intros.
(*    eapply ApplyCancelSep_with_eq in H6; eassumption. *)
  Admitted.

End canceller.

Lemma ignore_regs : forall p specs stn st rs,
  interp specs (![ p ] (stn, st))
  -> interp specs (![ p ] (stn, {| Regs := rs; Mem := Mem st |})).
Proof.
  rewrite sepFormula_eq; auto.
Qed.

Lemma interp_interp_himp : forall cs P Q stn_st,
  interp cs (![ P ] stn_st) ->
  (himp P Q) ->
  interp cs (![ Q ] stn_st).
Proof.
  unfold himp. intros. destruct stn_st.
  rewrite sepFormula_eq in *. unfold sepFormula_def in *. simpl in *.
  eapply Imply_E; eauto. 
Qed.

Theorem change_Imply_himp : forall p q s,
  himp p q
  -> forall specs, interp specs (![p] s ---> ![q] s)%PropX.
Proof.
  rewrite sepFormula_eq.
  unfold himp, sepFormula_def.
  eauto.
Qed.


Ltac change_to_himp := try apply ignore_regs;
  match goal with
    | [ H : interp ?specs (![ _ ] ?X)
      |- interp ?specs (![ _ ] ?X) ] =>
      eapply (@interp_interp_himp _ _ _ _ H)
    | [ |- _ ===> _ ] => hnf; intro
    | _ => apply change_Imply_himp
  end.

Definition smem_read stn := SepIL.smem_read_word stn. 
Definition smem_write stn := SepIL.smem_write_word stn. 

(** Symbolic Execution **)
(************************)
Require Import ReifyIL.
Lemma Some_cong : forall A (x y : A),
  x = y
  -> Some x = Some y.
  congruence.
Qed.

Ltac find_reg st r :=
  match goal with
    | [ H : Regs st r = ?x |- _ ] => constr:((x, Some_cong (eq_sym H)))
    | _ => constr:((Regs st r, @refl_equal (option W) (Some (Regs st r))))
  end.

Ltac open_stateD H0 :=
  cbv beta iota zeta delta 
    [ SymIL.stateD Expr.exprD Expr.applyD
      EquivDec.equiv_dec 
      Expr.Range Expr.Domain Expr.Denotation
      Expr.EqDec_tvar Expr.tvar_rec Expr.tvar_rect
      sumbool_rec sumbool_rect
      Peano_dec.eq_nat_dec nat_rec nat_rect eq_rec_r eq_rec eq_rect eq_sym
      nth_error map value
      f_equal

      Expr.AllProvable Expr.Provable Expr.tvarD comparator
    ] in H0; 
    let a := fresh in 
    let b := fresh in
    let zz := fresh in destruct H0 as [ a [ b zz ] ] ;
    destruct a as [ ? [ ? ? ] ];
    repeat match type of zz with
             | True => clear zz
             | _ /\ _ => let v := fresh in destruct zz as [ v zz ]
           end.

Ltac get_instrs st :=
  let rec find_exact H Hs :=
    match Hs with
      | tt => false
      | (H, _) => true
      | (_, ?Hs) => find_exact H Hs
    end
  in
  let rec get_instrs st ignore :=
    match goal with
      | [ H : Structured.evalCond ?l _ ?r _ st = Some _ |- _ ] =>
        match find_exact H ignore with
          | false =>
            let ignore := constr:((H, ignore)) in
            let v := get_instrs st ignore in
            constr:((((l,r), H), v))
        end
      | [ H : Structured.evalCond ?l _ ?r _ st = None |- _ ] =>
        constr:((((l,r), H), tt))
      | [ H : evalInstrs _ st ?is = Some ?X |- _ ] =>
        let v := get_instrs X tt in
        constr:(((is, H), v))
      | [ H : evalInstrs _ st ?is = None |- _ ] =>
        constr:(((is, H), tt))
      | [ |- _ ] => tt
    end
  in get_instrs st tt.

Ltac clear_instrs ins :=
  match ins with
    | tt => idtac
    | ((_,?H), ?ins) => clear H; clear_instrs ins
  end.

Ltac collectAllTypes_instrs is Ts k :=
  match is with
    | tt => k Ts
    | (((?l,?r), _), ?is) =>
       collectTypes_rvalue ltac:(isConst) l Ts ltac:(fun Ts =>
         collectTypes_rvalue ltac:(isConst) r Ts ltac:(fun Ts =>
          collectAllTypes_instrs is Ts k))
    | ((?i, _), ?is) =>
      collectTypes_instrs ltac:(isConst) i Ts ltac:(fun Ts =>
        collectAllTypes_instrs is Ts k)
  end.

Ltac build_path types instrs st uvars vars funcs k :=
  match instrs with
    | tt => 
      let is := constr:(nil : @SymIL.istream types) in
      let pf := constr:(refl_equal (Some st)) in
      k uvars funcs is (Some st) pf
    | ((?i, ?H), ?is) =>
      match type of H with
        | Structured.evalCond ?l ?t ?r _ ?st = ?st' =>
          reify_rvalue ltac:(isConst) l types funcs uvars vars ltac:(fun uvars funcs l =>
            reify_rvalue ltac:(isConst) r types funcs uvars vars ltac:(fun uvars funcs r =>
              match st' with
                | None => 
                  let i := constr:(inr (@SymIL.SymAssertCond types l t r st') :: (nil : @SymIL.istream types)) in
                  k uvars funcs i (@None state) H
                | Some ?st'' => 
                  build_path types is st uvars vars funcs ltac:(fun uvars funcs is sf pf =>
                    let i := constr:(inr (@SymIL.SymAssertCond types l t r st') :: is) in
                    let pf := constr:(@conj _ _ H pf) in
                    k uvars funcs i sf pf)
              end))
        | evalInstrs _ ?st _ = ?st' =>
          reify_instrs ltac:(isConst) i types funcs uvars vars ltac:(fun uvars funcs sis =>
            match st' with
              | None => 
                let i := constr:(inl (sis, None) :: (nil : @SymIL.istream types)) in
                  k uvars funcs i (@None state) H
              | Some ?st'' =>
                build_path types is st'' uvars vars funcs ltac:(fun uvars funcs is sf pf =>
                  let i := constr:(inl (sis, st') :: is) in
                  let pf := constr:(@conj _ _ H pf) in
                  k uvars funcs i sf pf)
            end)
      end
  end.
