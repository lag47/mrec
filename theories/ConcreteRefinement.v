From Coq Require Export Morphisms RelationClasses Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.
Require Import Lia.
Require Export Refinement ConvergentRefinement.

Variant no_eventsF {E R} (F : itree E R -> Prop) : itree' E R -> Prop :=
  | no_events_Ret r : no_eventsF F (RetF r)
  | no_events_Tau t : F t -> no_eventsF F (TauF t).

Definition no_events_ {E R} F (t : itree E R) : Prop :=
  no_eventsF F (observe t).


Lemma monot_no_events E R : monotone1 (@no_events_ E R).
Proof.
  red. unfold no_events_. intros.
  induction IN; constructor; auto.
Qed.

Hint Resolve monot_no_events : paco.

Definition no_events {E R } : itree E R -> Prop := paco1 no_events_ bot1.

Global Instance proper_no_events_eutt {E R} : Proper (eutt eq ==> flip impl) (@no_events E R).
Proof.
  pcofix CIH.
  intros t1 t2 Ht Hno. pstep. red.
  punfold Hno. red in Hno. punfold Ht. red in Ht.
  hinduction Ht before r; intros.
  - constructor.
  - constructor. inv Hno. pclearbot. right. eauto.
  - inv Hno.
  - constructor. left. pstep. eapply IHHt; eauto.
  - inv Hno. pclearbot. eapply IHHt; eauto. pstep_reverse.
Qed.

Global Instance proper_isConcrete_eutt {E R} : Proper (eutt eq ==> flip impl) (@isConcrete E R).
Proof.
  pcofix CIH.
  intros t1 t2 Ht Hcon. pstep. red.
  punfold Hcon. red in Hcon. punfold Ht. red in Ht.
  hinduction Ht before r; intros.
  - constructor.
  - inv Hcon. pclearbot. constructor. eauto.
  - inv Hcon. inj_existT. subst. pclearbot. constructor.
    right. eapply CIH; eauto. apply REL. apply H0.
  - constructor. left. pstep. eapply IHHt; eauto.
  - inv Hcon. pclearbot. eapply IHHt; auto. pstep_reverse.
Qed.
(*should it be refines or padded refines? lifting to padded_refines is actually simple 
   because each other predicate respects eutt *)
Theorem concrete_conv_ref_to_no_ev E1 E2 R1 R2 RE REAns RR :
  forall (t : itree_spec E1 R1) (phi : itree_spec E2 R2), isConcrete t -> conv_ref phi ->
                                                     refines RE REAns RR t phi ->
                                                     no_events t.
Proof.
  pcofix CIH.
  intros t phi Hcon Hconv Href.
  punfold Hcon. red in Hcon.
  punfold Hconv. red in Hconv.
  punfold Href. red in Href.
  pstep. red. hinduction Href before r; intros.
  - constructor.
  - constructor. right. inv Hcon. inv Hconv. pclearbot. eauto.
  - inv Hcon. pclearbot. constructor. right. eapply CIH; eauto.
    Unshelve. 3 : (apply (go ophi)). pstep. auto. pstep. auto.
  - inv Hconv. pclearbot. eapply IHHref; eauto. pstep_reverse.
  - inv Hconv.
  - inv Hconv. inj_existT. subst. pclearbot. eapply H0; eauto.
    pstep_reverse.
  - inv Hcon.
  - inv Hconv. inj_existT. subst. pclearbot. eapply IHHref; eauto. pstep_reverse.
  - inv Hcon.
    Unshelve. auto.
Qed.

Theorem concrete_conv_ref_padded_to_no_ev E1 E2 R1 R2 RE REAns RR :
  forall (t : itree_spec E1 R1) (phi : itree_spec E2 R2), isConcrete t -> conv_ref phi ->
                                                     padded_refines RE REAns RR t phi ->
                                                     no_events t.
Proof.
  intros t phi Hcon Hconv Href. red in Href. rewrite  pad_eutt.
  eapply concrete_conv_ref_to_no_ev with (phi := pad phi); eauto.
  - rewrite <- pad_eutt. auto.
  - rewrite <- pad_eutt. auto.
Qed.

(*relies on lem*)
Theorem no_ev_to_dec E R : forall (t : itree E R), no_events t -> 
                                              (exists r, t ≈ Ret r) \/ t ≈ ITree.spin.
Admitted.
