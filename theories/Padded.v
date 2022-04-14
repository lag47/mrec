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
