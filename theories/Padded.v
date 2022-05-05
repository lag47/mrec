From Coq Require Export Morphisms Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.

Require Export HeterogeneousEventRelations.


Ltac inj_existT := repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.

Variant paddedF {E R} (F : itree E R -> Prop) : itree' E R -> Prop :=
  | paddedF_Ret r : paddedF F (RetF r)
  | paddedF_Tau t : F t -> paddedF F (TauF t)
  | paddedF_VisTau A e (k : A -> itree E R) :
    (forall a, F (k a)) -> paddedF F (VisF e (fun a => (Tau (k a ))))
.

Definition padded_ {E R} F (t : itree E R) := paddedF F (observe t).

Lemma padded_monot {E R} : monotone1 (@padded_ E R).
Proof.
  unfold padded_. red. intros. inv IN; econstructor; eauto.
Qed.

#[global] Hint Resolve padded_monot : paco.

Definition padded {E R} (t : itree E R) : Prop := paco1 padded_ bot1 t.

Lemma padded_Ret E R r : @padded E R (Ret r).
Proof. pstep. constructor. Qed.

Lemma padded_Tau E R (t : itree E R) : padded t -> padded (Tau t).
Proof. intros. pstep. constructor. left. auto. Qed.

Lemma padded_VisTau E R A (e : E A) (k : A -> itree E R) :
  (forall a, padded (k a)) -> padded (Vis e (fun a => Tau (k a))).
Proof.
  intros. pstep. red. cbn. constructor. left. apply H.
Qed.

Lemma padded_Vis_inv E R A (e : E A) (k : A -> itree E R) : 
  padded (Vis e k ) -> exists k', forall a, k a ≅ Tau (k' a).
Proof.
  intro Hek. pinversion Hek. inj_existT. subst. exists k1. reflexivity.
Qed.
 
CoFixpoint pad_ {E R} (ot : itree' E R) : itree E R :=
  match ot with
  | RetF r => Ret r
  | TauF t => Tau (pad_ (observe t) )
  | VisF e k => Vis e (fun a => Tau (pad_ (observe (k a))))
  end.

Definition pad {E R} (t : itree E R) := pad_ (observe t).


Lemma pad_is_padded E R : forall (t : itree E R), padded (pad t).
Proof.
  pcofix CIH. pstep. intros. red. unfold pad.
  destruct (observe t); cbn.
  - constructor.
  - constructor. right. eauto.
  - constructor. right. eauto.
Qed.

Lemma pad_eutt E R : forall (t : itree E R), t ≈ pad t.
Proof.
  pcofix CIH. intros. pstep. red. unfold pad.
  destruct (observe t); cbn.
  - constructor. auto.
  - constructor. right. eauto.
  - constructor. left. 
    generalize (k v) as t'.
    pcofix CIH'. intros. pstep. constructor; auto.
    destruct (observe t'); cbn.
    + constructor; auto.
    + constructor. right. eauto.
    + constructor. right. eauto.
Qed.

Global Instance pad_Proper {b1 b2 E R} : Proper (eqit eq b1 b2 ==> eqit eq b1 b2) (@pad E R).
Proof.
  pcofix CIH.
  intros t1 t2 Ht12. pstep. red. unfold pad.
  punfold Ht12. red in Ht12. hinduction Ht12 before r;
    intros; cbn; eauto.
  - constructor. auto.
  - constructor. pclearbot. right. eapply CIH; eauto.
  - constructor. left. pstep. constructor. pclearbot. right.
    eapply CIH; eauto. apply REL.
  - constructor; auto.
  - constructor; auto.
Qed.

Theorem pad_ret E R (r : R) : @eq_itree E R R eq (pad (Ret r)) (Ret r).
Proof. unfold pad. cbn. pstep. red. cbn. constructor. auto. Qed.

Theorem pad_tau E R : forall (t : itree E R), pad (Tau t) ≅ Tau (pad t).
Proof.
  intros. pstep. red. cbn. constructor. left.
  enough (pad t ≅ pad t). auto. reflexivity.
Qed.

Theorem pad_vis E R A e (k : A -> itree E R) : 
  pad (Vis e k) ≅ Vis e (fun a => Tau (pad (k a))).
Proof.
  intros. pstep. red. cbn. constructor. left.
  enough (Tau (pad (k v)) ≅ Tau (pad (k v)) ). auto. reflexivity.
Qed.
 
Theorem pad_bind E R S (k : R -> itree E S) : 
  forall t, pad (ITree.bind t k) ≅ ITree.bind (pad t) (fun r => pad (k r)).
Proof.
  ginit. gcofix CIH. intros. destruct (observe t) eqn : Heq; symmetry in Heq; apply simpobs in Heq;
    rewrite Heq.
  - rewrite pad_ret. setoid_rewrite bind_ret_l. gfinal.
    right. eapply paco2_mon with (r := bot2); intros; try contradiction.
    enough (pad (k r0) ≅ pad (k r0)); auto. reflexivity.
  - rewrite bind_tau. repeat rewrite pad_tau. rewrite bind_tau.
    gstep. constructor. gfinal. left. eapply CIH.
  - rewrite bind_vis. repeat rewrite pad_vis. rewrite bind_vis.
    setoid_rewrite bind_tau. gstep. constructor.
    gstep. constructor. gfinal. left. eauto.
Qed.

Theorem pad_iter E R S (body : R -> itree E (R + S)):
  forall r, pad (ITree.iter body r) ≅ ITree.iter (fun r => pad (body r)) r.
Proof.
  ginit. gcofix CIH.
  intros. setoid_rewrite unfold_iter. rewrite pad_bind.
  guclo eqit_clo_bind. econstructor.
  reflexivity. intros. subst. destruct u2.
  - rewrite pad_tau. gstep. constructor. gfinal. left. eauto.
  - rewrite pad_ret. gstep. constructor. auto.
Qed.
