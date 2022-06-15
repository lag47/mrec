From Coq Require Export Morphisms RelationClasses Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt Props.Divergence Props.Finite.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.
Require Import Lia.
Require Export Refinement.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Variant conv_refF {E : Type -> Type} {R : Type} (F : itree_spec E R -> Prop) : itree_spec' E R -> Prop :=
  | conv_ref_RetF r : conv_refF F (RetF r)
  | conv_ref_TauF t : F t -> conv_refF F (TauF t)
  | conv_ref_existsF (A : Type) (k : A -> itree_spec E R) :
    (forall a, F (k a) ) -> conv_refF F (VisF Spec_exists k)
  | conv_ref_forallF (A : Type) (k : A -> itree_spec E R) :
    A -> (forall a, F (k a)) -> conv_refF F (VisF Spec_forall k)
.

Definition conv_ref_ {E : Type -> Type} {R : Type} (F : itree_spec E R -> Prop) (t : itree_spec E R) :=
  conv_refF F (observe t).

Lemma monotone_conv_refF {E R} (ot : itree_spec' E R) sim sim' 
      (LE : sim <1= sim')
      (IN : conv_refF sim ot) :
  conv_refF sim' ot.
Proof. induction IN; constructor; auto. Qed.

Lemma monotone_conv_ref_ {E R} : monotone1 (@conv_ref_ E R).
Proof. red. intros. eapply monotone_conv_refF; eauto. Qed.

Hint Resolve monotone_conv_ref_ : paco.

Definition conv_ref {E R} : itree_spec E R -> Prop := paco1 conv_ref_ bot1.


Lemma conv_ref_ret_bind E1 E2 R1 S R2 RE REAns RR r (t2 : itree_spec E2 R2) :
  forall (t1 : itree_spec E2 S), 
    conv_ref t1 ->
    @refines E1 E2 R1 R2 RE REAns RR (Ret r) (t1 >> t2) ->
    refines RE REAns RR (Ret r) t2.
Proof.
  intros t1 Ht1 Href. punfold Href. red in Href. cbn in Href.
  punfold Ht1. red in Ht1. pstep. red. cbn.
  remember (RetF r) as x. remember (t1 >> t2) as tbind.
  assert (Htbind : tbind ≅ t1 >> t2). subst. reflexivity.
  clear Heqtbind. punfold Htbind. red in Htbind.
  hinduction Href before RR; intros; inv Heqx; use_simpobs.
  - unfold observe in Htbind. cbn in Htbind. destruct (observe t1) eqn : Ht1';
      inv Htbind; try inv CHECK.
    setoid_rewrite <- H2. constructor. auto.
  - assert (HDEC: (exists t1', observe t1 = TauF t1') \/ (exists r', observe t1 = RetF r') ).
    { unfold observe in Htbind. cbn in Htbind. destruct (observe t1); eauto.
      inv Htbind; inv CHECK. }
    destruct HDEC as [[t1' Ht1']  | [r' Hr'] ].
    + eapply IHHref with (t1 := t1'); eauto.
      rewrite Ht1' in Ht1. inv Ht1. pclearbot. pstep_reverse.
      assert (Tau phi ≅ t1 >> t2). pstep. auto.
      symmetry in Ht1'. use_simpobs. rewrite Ht1' in H. rewrite bind_tau in H.
      pinversion H; try inv CHECK. pclearbot. subst.
      clear - REL. pclearbot. pstep_reverse.
    + assert (Tau phi ≅ t1 >> t2). pstep. auto.
      symmetry in Hr'. use_simpobs. rewrite Hr' in H.
      rewrite bind_ret_l in H.
      punfold H. red in H. cbn in H. inv H; try inv CHECK.
      constructor. pclearbot. eapply IHHref; eauto.
      pstep_reverse. rewrite Hr', bind_ret_l. clear - REL. pclearbot. auto.
  - assert (HDEC : (exists k : A -> _, observe t1 = VisF Spec_forall k) \/ (exists r', observe t1 = RetF r') ).
    {
      unfold observe in Htbind. cbn in Htbind. destruct (observe t1); eauto.
      inv Htbind; inv CHECK.
      cbn in Htbind. inv Htbind. inj_existT. subst. eauto. }
    destruct HDEC as [ [k Hk] | [r' Hr'] ].
    + rewrite Hk in Ht1. inv Ht1. inj_existT. subst. pclearbot. rename X into a.
      eapply H0 with (t1 := k a); eauto. pstep_reverse. Unshelve. all : auto.
      assert (Vis Spec_forall kphi ≅ t1 >> t2). pstep. auto.
      symmetry in Hk. use_simpobs. rewrite Hk in H1. rewrite bind_vis in H1.
      pinversion H1. inj_existT. subst. clear - REL. pclearbot.
      pstep_reverse.
    + symmetry in Hr'. use_simpobs.
      assert (Vis Spec_forall kphi ≅ t1 >> t2). pstep. auto.
      rewrite Hr' in H1. rewrite bind_ret_l in H1.
      pinversion H1; try inv CHECK. inj_existT. subst.
      constructor. intros. clear - H REL. pclearbot.
      rewrite itree_eta' at 1. pstep_reverse. rewrite <- REL. pstep. apply H.
  -  assert (HDEC : (exists k : A -> _, observe t1 = VisF Spec_exists k) \/ (exists r', observe t1 = RetF r') ).
    {
      unfold observe in Htbind. cbn in Htbind. destruct (observe t1); eauto.
      inv Htbind; inv CHECK.
      cbn in Htbind. inv Htbind. inj_existT. subst. eauto. }
    destruct HDEC as [ [k Hk] | [r' Hr'] ].
    + rewrite Hk in Ht1. inv Ht1. inj_existT. subst. pclearbot.
      eapply IHHref with (t1 := k a); eauto. pstep_reverse.
      assert (Vis Spec_exists kphi ≅ t1 >> t2). pstep. auto.
      symmetry in Hk. use_simpobs. rewrite Hk in H. rewrite bind_vis in H.
      pinversion H. inj_existT. subst. clear - REL. pclearbot.
      pstep_reverse.
    + symmetry in Hr'. use_simpobs.
      assert (Vis Spec_exists kphi ≅ t1 >> t2). pstep. auto.
      rewrite Hr' in H. rewrite bind_ret_l in H.
      pinversion H; try inv CHECK. inj_existT. subst. econstructor.
      Unshelve. all : auto. clear - REL Href. pclearbot.
      rewrite itree_eta' at 1. pstep_reverse. rewrite <- REL. pstep. apply Href.
Qed.

Global Instance conv_ref_eqit_proper E R b1 b2 : 
  Proper (@eqit (SpecEvent E) R R eq b1 b2 ==> flip impl) conv_ref.
Proof.
  pcofix CIH.
  intros t1 t2 Ht Ht2. pstep. red. punfold Ht2. red in Ht2.
  punfold Ht. red in Ht.
  hinduction Ht before R; intros; pclearbot; try (constructor; eauto).
  - right. eapply CIH; eauto. inv Ht2. pclearbot. auto.
  - inv Ht2. inj_existT. subst. constructor. right. pclearbot. eapply CIH; eauto.
    apply REL. apply H0.
    inj_existT. subst. constructor; auto. pclearbot. right. eapply CIH; eauto.
    apply REL. apply H0.
  - left. pstep. red. eapply IHHt; eauto.
  - inv Ht2. pclearbot. punfold H0.
Qed.

Lemma padded_conv_ref_ret_bind E1 E2 R1 S R2 RE REAns RR r (t2 : itree_spec E2 R2) :
  forall (t1 : itree_spec E2 S), 
    conv_ref t1 ->
    @padded_refines E1 E2 R1 R2 RE REAns RR (Ret r) (t1 >> t2) ->
    padded_refines RE REAns RR (Ret r) t2.
Proof.
  intros t1 Ht1. unfold padded_refines. setoid_rewrite pad_ret.
  setoid_rewrite pad_bind. intros. rewrite pad_eutt in Ht1. eapply conv_ref_ret_bind; eauto.
Qed.

Lemma conv_ref_bind E R S (k : R -> itree_spec E S) :
  forall t, conv_ref t ->
  (forall r, conv_ref (k r) ) ->
   conv_ref (ITree.bind t k).
Proof.
  intros t Ht Hk. generalize dependent t. pcofix CIH. intros t Ht. punfold Ht. red in Ht.
  pstep. red. unfold observe. cbn. inv Ht.
  - pstep_reverse. eapply paco1_mon; try eapply Hk. intros. contradiction.
  - constructor. right. pclearbot. eapply CIH; eauto.
  - constructor. right. pclearbot. eapply CIH; apply H0.
  - constructor; auto. right. pclearbot. eapply CIH; apply H0.
Qed.

Lemma conv_ref_ret E R (r : R) : 
  @conv_ref E R (Ret r).
Proof.
  pstep. red. constructor.
Qed.

Variant conv_ref_mrecF {E D : Type -> Type} {R : Type} (P : forall A, D A -> Prop) 
        (F : itree_spec (D +' E) R -> Prop) : 
  itree_spec' (D +' E) R -> Prop :=
  | conv_ref_mrec_RetF r : conv_ref_mrecF P F (RetF r)
  | conv_ref_mrec_TauF t : F t -> conv_ref_mrecF P F (TauF t)
  | conv_ref_mrec_existsF (A : Type) (k : A -> itree_spec _ R) :
    (forall a, F (k a) ) -> conv_ref_mrecF P F (VisF Spec_exists k)
  | conv_ref_mrec_forallF (A : Type) (k : A -> itree_spec _ R) :
    A -> (forall a, F (k a)) -> conv_ref_mrecF P F (VisF Spec_forall k)
  | conv_ref_mrec_inlF (A : Type) (d : D A) (k : A -> itree_spec _ R) :
    P A d ->
    (forall a, F (k a) ) -> conv_ref_mrecF P F (VisF (Spec_vis (inl1 d) ) k)
.

Definition conv_ref_mrec_ {E D: Type -> Type} {R : Type} P (F : itree_spec (D +' E) R -> Prop) 
           (t : itree_spec (D +' E) R) :=
  conv_ref_mrecF P F (observe t).

Lemma monotone_conv_ref_mrecF {E D R} P (ot : itree_spec' (D +' E) R) sim sim' 
      (LE : sim <1= sim')
      (IN : conv_ref_mrecF P sim ot) :
  conv_ref_mrecF P sim' ot.
Proof. induction IN; constructor; auto. Qed.

Lemma monotone_conv_ref_mrec_ {E D R} P : monotone1 (@conv_ref_mrec_ E D R P ).
Proof. red. intros. eapply monotone_conv_ref_mrecF; eauto. Qed.

Hint Resolve monotone_conv_ref_mrec_ : paco.

Definition conv_ref_mrec {E D R} P : itree_spec (D +' E) R -> Prop := paco1 (conv_ref_mrec_ P) bot1.

Lemma conv_ref_mrec_bind E D R S P (k : R -> itree_spec (D +' E) S ) :
  forall t, conv_ref_mrec P t ->
  (forall r, conv_ref_mrec P (k r) ) ->
   conv_ref_mrec P (ITree.bind t k).
Proof.
  intros t Ht Hk. generalize dependent t. pcofix CIH. intros t Ht.
  pstep. red. unfold observe. cbn. punfold Ht. red in Ht.
  inv Ht.
  - pstep_reverse. eapply paco1_mon; try apply Hk. intros. contradiction.
  - constructor. right. pclearbot. eapply CIH; eauto.
  - constructor. right. pclearbot. eapply CIH; eauto. apply H0.
  - constructor; auto. right. pclearbot. eapply CIH. apply H0.
  - constructor. auto. pclearbot. right. eapply CIH. apply H1.
Qed.

(*may need a more general induction hype *)

Section ConvRefMRec.
Context (E D : Type -> Type).
Context (Pre : forall A, D A -> Prop).
Context (bodies : D ~> itree_spec (D +' E) ).
Context (A : Type) (init : D A) (Hinit : Pre A init).
Context (Hconv : forall A (d : D A), Pre A d -> conv_ref_mrec Pre (bodies A d)  ).

Lemma conv_ref_interp_mrec_conv_ref:
    forall t : itree_spec (D +' E) A, conv_ref_mrec Pre t -> conv_ref (interp_mrec_spec bodies t).
Proof.
  pcofix CIH. intros t Ht. punfold Ht. red in Ht.
  pstep. red. unfold observe. cbn. inv Ht.
  - constructor.
  - constructor. right. eapply CIH; eauto. pclearbot. auto.
  - constructor. pclearbot. right. eapply CIH; eauto. apply H0.
  - constructor; auto. right. pclearbot. eapply CIH; eauto.
    apply H0.
  - constructor. right. eapply CIH. pclearbot. apply conv_ref_mrec_bind; auto.
Qed.

Lemma conv_ref_mrec_conv_ref : conv_ref (mrec_spec bodies init).
Proof.
  eapply conv_ref_interp_mrec_conv_ref. auto.
Qed.



End ConvRefMRec.

Global Instance conv_ref_mrec_eqit_proper E D R b1 b2 P : 
  Proper (@eqit (SpecEvent (D +' E)) R R eq b1 b2 ==> flip impl) (conv_ref_mrec P).
Proof.
  pcofix CIH.
  intros t1 t2 Ht Ht2. pstep. red. punfold Ht2. red in Ht2.
  punfold Ht. red in Ht.
  hinduction Ht before R; intros; pclearbot; try (constructor; eauto).
  - right. eapply CIH; eauto. inv Ht2. pclearbot. auto.
  - inv Ht2; inj_existT; subst; pclearbot.
    + constructor. right. eapply CIH; eauto. apply REL. apply H0.
    + constructor; auto. right. eapply CIH. apply REL. apply H0.
    + constructor; auto. right. eapply CIH. apply REL. apply H3.
  - left. pstep. red. eapply IHHt; eauto.
  - inv Ht2. pclearbot. punfold H0.
Qed.

Lemma conv_ref_mrec_forall E D R P A k :
  A ->
  (forall a : A, @conv_ref_mrec E D R P (k a) ) ->
  conv_ref_mrec P (Vis Spec_forall k).
Proof.
  intros. pstep. constructor. auto. left. apply H.
Qed.

Lemma conv_ref_mrec_exists E D R P A k :
  (forall a : A, @conv_ref_mrec E D R P (k a) ) ->
  conv_ref_mrec P (Vis Spec_exists k).
Proof.
  intros. pstep. constructor. left. apply H.
Qed.

Lemma conv_ref_mrec_inl E D R P A k (d : D A) :
  (P A d : Prop) ->
  (forall a : A, @conv_ref_mrec E D R P (k a) ) ->
  conv_ref_mrec P (Vis (Spec_vis (inl1 d)) k ).
Proof.
  intros. pstep. constructor. auto. left. apply H0.
Qed.
(*now I want a good reasoning principle for finding conv_ref*)

    (*can infer *)
  (* shouldn't need coinduction *)
  


(*

Lemma monotone_satisfiesF {E R1 R2} (RR : R1 -> R2 -> Prop) ot1 (ot2 : itree_spec' E R2) sim sim' 
  (LE : sim <2= sim' )
  (IN : satisfiesF RR sim ot1 ot2) : 
  satisfiesF RR sim' ot1 ot2.
Proof.
  induction IN; eauto.
Qed.

Lemma monotone_satisfies_ {E R1 R2} RR : monotone2 (@satisfies_ E R1 R2 RR).
Proof. red. intros. eapply monotone_satisfiesF; eauto. Qed.

Hint Resolve monotone_satisfies_ : paco.
*)
