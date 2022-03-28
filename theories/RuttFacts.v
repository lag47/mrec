From Coq Require Export Morphisms Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.

Require Export HeterogeneousEventRelations.

Ltac inj_existT := repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.

Lemma rutt_inv_Vis :   forall (E1 E2 : Type -> Type) (R1 R2 : Type) (REv : forall A B : Type, E1 A -> E2 B -> Prop)
    (RAns : forall A B : Type, E1 A -> A -> E2 B -> B -> Prop) (RR : R1 -> R2 -> Prop) A B
    (e1 : E1 A) (e2 : E2 B) k1 k2,
    rutt REv RAns RR (Vis e1 k1) (Vis e2 k2) ->
    REv A B e1 e2 /\ (forall a b, RAns A B e1 a e2 b -> rutt REv RAns RR (k1 a) (k2 b)).
Proof.
  intros. pinversion H. inj_existT. subst. pclearbot. split; auto.
  intros. apply H7 in H0. pclearbot. auto.
Qed.

Definition extract {E1 E2 A B} (REAns : relationEAnsH E1 E2) 
           (e1 : E1 A) (e2 : E2 B) : relationH A B :=
  fun a b => REAns A B e1 a e2 b.
  

Section MRec.

Context (D1 D2 E : Type -> Type).
Context (bodies1 : D1 ~> itree (D1 +' E)).
Context (bodies2 : D2 ~> itree (D2 +' E)).
(*
Context (A B :Type).
Context (init1 : D1 A).
Context (init2 : D2 B).
*)
Context (REvE : relationEH E E).
Context (REvAns : forall A B : Type, E A -> A -> E B -> B -> Prop ).

Context (REvInv : relationEH D1 D2).
Context (REvAnsInv : forall A B : Type, D1 A -> A -> D2 B -> B -> Prop).

Context (Hbodies : forall A B (d1 : D1 A) (d2 : D2 B), REvInv A B d1 d2 -> 
         rutt (sum_relE REvInv REvE) (sum_relAns REvAnsInv REvAns) (extract REvAnsInv d1 d2)
            (bodies1 A d1) (bodies2 B d2) ).
(*maybe rutt actually needs to be changed? the types seem a little too constrained here
  if rutt took in a family of relations indexed by types? then there might be more hope *)
Lemma rutt_mrec : 
  forall A B (init1 : D1 A) (init2 : D2 B), 
    (*need some constraints on RAB the problem is that RAB seems to need to be reliant
      on init1 and init2, the return relation of two related calls depends on the 
      actual call*)
    REvInv A B init1 init2 -> rutt REvE REvAns (extract REvAnsInv init1 init2)
         (mrec bodies1 init1) (mrec bodies2 init2).
Proof.
  ginit. gcofix CIH.
  (* maybe I need some kind of 6? argument functor
     A -> B -> D1 A -> D2 B -> itree ? A -> itree ? B -> Prop 

     where the itrees are the tree generated by the mutually recusive call 
     (there should be more arguments in the closure but these are the ones 
      that vary coinductively?)

      2 things to make sure that would actually be useful
      1. strong enough to prove mrec rutt (or maybe just eutt) results
               (in fact double implication is what I think I would want)
      2. lets me have a coinductive hypothesis
   *)
  (*this is not good, I need to bring this up with steve on Thursday*)

  (*wtf is going on here
    the extract expression fixes the init 
    I need to further generalize it in some way, but I am not really sure how
    is it even correct behavior or are gpaco and paco acting up
    I think the problem is that the functor relies on init1 and init2
    if I could remove that, then I should be fine
    but that is easier said than done
   *)
  unfold mrec, interp_mrec. intros Hinit. unfold extract. cbn.
  setoid_rewrite unfold_iter.
Admitted.
End MRec.
  
