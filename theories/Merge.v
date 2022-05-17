

Locate "<=?".

Require Import Coq.Lists.List Coq.Sorting.Permutation.

From Coq Require Export Morphisms Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Open Scope list_scope.

Locate Permutation.
(*
Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted nil
  | sorted_singleton x : sorte
. *)

(*rec_fix*)
Definition merge {E} : (list nat * list nat) -> itree E (list nat) :=
  rec_fix ( fun merge_rec '(l1, l2) =>
              match (l1,l2) with
              | (h1 :: t1, h2 :: t2) => if Nat.leb h1 h2
                                     then
                                       l <-  merge_rec (t1,l2);;
                                       Ret (h1 :: l)
                                     else
                                       l <- merge_rec (l1, t2);;
                                       Ret (h2 :: l)
              | (l1, nil) => Ret l1
              | (nil, l2) => Ret l2 end ).

Definition halve {E} : list nat -> itree E (list nat * list nat) :=
    rec_fix (fun halve_rec l =>
               match l with
               | x :: y :: t => '(l1,l2) <- halve_rec l;; Ret (x :: l1, y :: l2)
               | x :: nil => Ret ( x :: nil  , nil )
               | nil => Ret ( nil , nil ) end

).


(*missing base case*)
Definition sort {E} : list nat -> itree E (list nat) :=
  rec_fix (fun sort_rec l => 
             if Nat.leb (length l) 1
             then Ret l
             else
               '(l1,l2) <- halve l;;
               l1 <- sort_rec l1;;
               l2 <- sort_rec l2;;
               merge (l1,l2)
          ).

(*
Fixpoint merge (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => l2
  | h1 :: t1 => 
      match l2 with
      | nil => l1
      | h2 :: t2 => if Nat.leb h1 h2
                  then h1 :: merge t1 l2
                  else h2 :: merge l1 t2 end end.
*)
