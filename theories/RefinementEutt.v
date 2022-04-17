From Coq Require Export Morphisms Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.

Require Export HeterogeneousEventRelations Padded Refinement.

Variant EvEq {E : Type -> Type} : forall (A B : Type), E A -> E B -> Prop :=
  | eveq (A : Type) (e : E A) : EvEq A A e e.

Variant EvEqAns {E : Type -> Type} : forall A B, E A -> E B -> A -> B -> Prop :=
  | eveqans A (e : E A) (a : A) : EvEqAns A A e e a a.


Lemma eutt_to_refines E R : forall (t1 t2 : itree_spec E R),
    padded t1 -> padded t2 ->
    t1 ≈ t2 -> refines EvEq EvEqAns eq t1 t2.
Proof.
  pcofix CIH. intros.
  pstep. red. punfold H2. red in H2. punfold H0. red in H0.
  punfold H1. red in H1.
  hinduction H2 before r; intros; try destruct e; pclearbot; eauto.
  - constructor. right. eapply CIH; eauto.
    inv H0. pclearbot. auto. inv H1. pclearbot. auto.
  - constructor. constructor. intros. inv H. inj_existT. subst.
    inv H0. inv H1. inj_existT. subst. right. eapply CIH; eauto.
    pstep. constructor. auto. pstep. constructor. auto.
    apply REL.
  - inv H0. inv H1. inj_existT. subst. constructor.
    intros. eapply refines_forallL. constructor. right. eapply CIH; pclearbot; eauto.
    eapply H2. eapply H0. setoid_rewrite <- tau_eutt. eapply REL.
  - inv H0. inv H1. inj_existT. subst. constructor. intros.
    eapply  refines_existsR. constructor. right. pclearbot. eapply CIH; eauto.
    apply H2. apply H0. setoid_rewrite <- tau_eutt. apply REL.
  - constructor. inv H0. pclearbot. punfold H3.
  - constructor. inv H1. pclearbot. punfold H3.
Qed.

Lemma refines_eutt_padded_r E1 E2 R1 R2 RE REAns RR : 
  forall (t1 : itree_spec E1 R1) (t2 t3 : itree_spec E2 R2),
    padded t1 -> padded t2 -> padded t3 -> t2 ≈ t3 ->
    refines RE REAns RR t1 t2 -> refines RE REAns RR t1 t3.
Proof.
  intros. apply eutt_to_refines in H2; auto.
  (* this approach would only work if *)
Abort.
