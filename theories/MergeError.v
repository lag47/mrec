

Require Import Coq.Lists.List Coq.Sorting.Permutation.

From Coq Require Export Morphisms RelationClasses Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt Props.Divergence Props.Finite.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.
Require Import Lia.
Require Export Refinement Merge.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Open Scope list_scope.


Variant errorE : Type -> Type :=
  | throw : errorE void.
Locate "-<".

(*need stuff for injection *)

Global Instance ResumSpecEvent {E1 E2} : E1 -< E2 -> E1 -< SpecEvent E2 := 
  fun s _ e => Spec_vis (s _ e). 

Definition is_nil {E} `{errorE -< E} (l : list nat) : itree_spec E bool :=
  match l with
  | nil => Ret true
  | _ => Ret false
  end.

Definition head {E} `{errorE -< E} (l : list nat) : itree_spec E nat :=
  match l with
  | nil => trigger throw ;; Ret 0
  | n :: _ => Ret n 
  end.

Definition tail {E} `{errorE -< E} (l : list nat) : itree_spec E (list nat) :=
  match l with
  | nil => trigger throw;; Ret nil
  | _ :: t => Ret t
  end.

Definition halve {E : Type -> Type} `{errorE -< E}: list nat -> itree_spec E (list nat * list nat) :=
  rec_fix_spec (fun rec l1 => 
                 b1 <- is_nil l1;;
                 if b1 : bool
                 then Ret (nil, nil)
                 else l2 <- tail l1;; 
                      b2 <- is_nil l2;;
                      if b2 : bool
                      then 
                        Ret (l1, nil)
                      else
                        x <- head l1;;
                        y <- head l2;;
                        l3 <- tail l2;;
                        '(l4,l5) <- rec l3;;
                        Ret (x :: l4, y :: l5)

               ).

Definition merge {E : Type -> Type} `{errorE -< E} : (list nat * list nat) -> itree_spec E (list nat) :=
  rec_fix_spec (fun rec '(l1,l2) =>
                  b1 <- is_nil l1;;
                  b2 <- is_nil l2;;
                  if b1 : bool then
                    Ret l2
                  else if b2 : bool then
                    Ret l1
                  else
                    x <- head l1;;
                    tx <- tail l1;;
                    y <- head l2;;
                    ty <- tail l2;;
                    if Nat.leb x y then
                      l <- rec (tx, y :: ty);;
                      Ret (x :: l)
                    else
                      l <- rec (x :: tx, ty);;
                      Ret (y :: l)
               ).

Definition sort {E : Type -> Type} `{errorE -< E} : list nat -> itree_spec E (list nat) :=
  rec_fix_spec (fun rec l => 
                  b <- is_nil l;;
                  if b : bool then
                    Ret nil
                  else 
                    '(l1, l2) <- halve l;;
                    l1s <- rec l1;;
                    l2s <- rec l2;;
                    merge (l1s, l2s)
               ).
