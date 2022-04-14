(***
 *** A version of the computation monad using the option-set monad
 ***)

From Coq Require Export Morphisms Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.

Require Export HeterogeneousEventRelations.

Infix ">>=" := ITree.bind (at level 58, left associativity).
Notation "m1 >> m2" := (m1 >>= fun _ => m2) (at level 58, left associativity).


(** * `itree_spec` **)

Variant SpecEvent (E:Type -> Type) (A:Type) : Type :=
| Spec_vis : E A -> SpecEvent E A
| Spec_forall : SpecEvent E A
| Spec_exists : SpecEvent E A
.

Arguments Spec_vis {E A}.
Arguments Spec_forall {E A}.
Arguments Spec_exists {E A}.

(* An ITree that defines a set of ITrees *)
Notation itree_spec E := (itree (SpecEvent E)).

(* The body of an itree_spec, inside the observe projection *)
Notation itree_spec' E A := (itree' (SpecEvent E) A).


(***
 *** Satisfaction of itree specs
 ***)

(* An itree satisfies an itree_spec iff it is eutt to an itree that satisfies
all the quantifiers in the itree_spec *)
Inductive satisfiesF {E R1 R2} (RR : R1 -> R2 -> Prop) (F : itree E R1 -> itree_spec E R2 -> Prop) :
  itree' E R1 -> itree_spec' E R2 -> Prop :=
  | satisfies_Ret r1 r2 : RR r1 r2 -> satisfiesF RR F (RetF r1) (RetF r2)
  | satisfies_TauLR phi1 (phi2 : itree_spec E R2) :
      F phi1 phi2 -> satisfiesF RR F (TauF phi1) (TauF phi2)
  | satisfies_TauL phi ophi :
      satisfiesF RR F (observe phi) ophi -> satisfiesF RR F (TauF phi) ophi
  | satisfies_TauR ophi phi :
      satisfiesF RR F ophi (observe phi) -> satisfiesF RR F ophi (TauF phi)
  | satisfies_VisLR A e kphi1 kphi2 :
      (forall a : A, F (kphi1 a) (kphi2 a) ) ->
      satisfiesF RR F (VisF e kphi1) (VisF (Spec_vis e) kphi2)
  | satisfies_forallR A kphi phi :
      (forall a : A, satisfiesF RR F phi (observe (kphi a))) ->
      satisfiesF RR F phi (VisF Spec_forall kphi)
  | satisfies_existsR A kphi phi (a : A) :
      (satisfiesF RR F phi (observe (kphi a))) ->
      satisfiesF RR F phi (VisF Spec_exists kphi)
.
Hint Constructors satisfiesF.
Definition satisfies_ {E R1 R2} (RR : R1 -> R2 -> Prop) F t1 t2 : Prop :=
  @satisfiesF E R1 R2 RR F (observe t1) (observe t2).

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
(*
Instance Proper_upaco2_satisfies_ {E R} :
  Proper ((eq ==> eq ==> impl) ==> eq ==> eq ==> impl) (upaco2 (@satisfies_ E R)).
Proof.
  intros r1 r2 prp_r t1 t2 e12 t3 t4 e34 r13.
  rewrite <- e12. rewrite <- e34.
  destruct r13.
  - left. eapply (paco2_mon _ H).
    intros x y. apply (prp_r x x eq_refl y y eq_refl).
  - right. apply (prp_r _ _ eq_refl _ _ eq_refl H).
Qed.
*)
Definition satisfies {E R1 R2} RR : itree E R1 -> itree_spec E R2 -> Prop :=
  paco2 (satisfies_ RR) bot2.

Ltac inj_existT := repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.

Section satisfies_test.

  CoFixpoint cphi1 {E} (A R : Type) : itree_spec E R := Vis (Spec_forall) (fun _ : A => cphi1 A R).

  CoFixpoint cphi2 {E} (A R : Type) : itree_spec E R := Tau (Vis Spec_forall (fun _ :A => cphi2 A R) ).

  Lemma phi1_empty : forall E R1 R2 (RR : R1 -> R2 -> Prop) (t : itree E R1), ~ satisfies RR t (cphi1 nat R2).
  Proof.
    intros. intro Hcontra. punfold Hcontra. red in Hcontra.
    remember (observe t) as ot.
    cbn in Hcontra. remember (VisF Spec_forall (fun _ : nat => cphi1 nat R2)) as y.
    hinduction Hcontra before RR; intros; inv Heqy; inj_existT; eauto.
    eapply H0; eauto. subst. cbn. auto. Unshelve. apply 0.
  Qed.

  Lemma phi2_nempty : forall E A R1 R2 (RR : R1 -> R2 -> Prop), satisfies RR (@ITree.spin E R1) (cphi2 A R2). 
  Proof.
    intros. pcofix CIH. pstep. red. cbn. constructor. left. 
    pcofix CIH'. pstep. constructor. intros. cbn. constructor.
    right. eauto.
  Qed.

  Lemma phi1_phi2_eutt : forall E R, (@cphi1 E nat R) ≈ (cphi2 nat R).
  Proof.
    intros E R. pcofix CIH. pstep. red. cbn.
    constructor; auto. constructor. intros. right. eauto.
  Qed.
(* this shows that satisfies does not respect eutt
   maybe it respects eutt on the left? I was only able to construct this counter example doing weird stuff on the right
   this raises the question of if the trim normal form stuff will still be useful
*)
End satisfies_test.

Lemma not_Proper_eutt_satisfies_impl {E R1 R2} RR :
  ~ Proper (eutt eq ==> eutt eq ==> impl) (@satisfies E R1 R2 RR).
Proof.
  intro Hcon. eapply phi1_empty. rewrite phi1_phi2_eutt. 
  apply phi2_nempty.
Qed.

Lemma satisfies_TauL_inv:
  forall (E : Type -> Type) (R2 R1 : Type) (RR : R1 -> R2 -> Prop) (m1 : itree E R1)
    (phi2 : itree_spec E R2),
    satisfiesF RR (upaco2 (satisfies_ RR) bot2) (TauF m1) (observe phi2) -> satisfies RR m1 phi2.
Proof.
  intros E R2 R1 RR m1 phi2 H.
  remember (TauF m1) as x. pstep. red.
  hinduction H before RR; intros; inv Heqx; eauto.
  pclearbot. constructor. pstep_reverse.
Qed.

Instance Proper_eutt_satisfies_impl_l {E R1 R2} RR :
  Proper (eutt eq ==> eq ==> impl) (@satisfies E R1 R2 RR).
Proof.
  intros t1 t2 Ht12 t3 t4 Ht34. subst t4. intros Ht13.
  generalize dependent t3. generalize dependent t2. revert t1.
  pcofix CIH. intros t1 t2 Ht12 t3 Ht13.
  pstep. red. punfold Ht12. red in Ht12.
  punfold Ht13. red in Ht13.
  hinduction Ht13 before r; intros; eauto.
  - remember (RetF r1) as x. hinduction Ht12 before r; intros; inv Heqx; eauto.
  - pclearbot. assert (phi1 ≈ t2). rewrite <- (tau_eutt phi1). pstep. auto.
    clear Ht12. rename H0 into Ht12. punfold H. red in H.
    punfold Ht12. red in Ht12.
    hinduction Ht12 before r; intros; subst; eauto.
    + constructor. rewrite itree_eta' at 1. pstep_reverse.
      eapply paco2_mon with (r := bot2). pstep. auto. intros; contradiction.
    + constructor. right. pclearbot. eapply CIH; eauto. revert H.
      apply satisfies_TauL_inv.
    + pclearbot. constructor.
      remember (VisF e k1) as x. hinduction H before r; intros; inv Heqx; inj_existT; subst; eauto.
      econstructor. right. pclearbot. eapply CIH; eauto. apply REL. apply H.
    + eapply IHHt12; eauto. pstep_reverse. apply satisfies_TauL_inv. auto.
  -  eapply IHHt13; eauto. pstep_reverse. rewrite <- (tau_eutt phi). pstep. auto.
  - pclearbot. remember (VisF e kphi1) as x.
    hinduction Ht12 before r; intros; subst; try inv Heqx; eauto.
    inj_existT. subst. pclearbot. constructor. right. eapply CIH; eauto. apply REL. apply H. 
Qed.
(* Print Assumptions not_Proper_eutt_satisfies_impl. *)

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

Section Refines.
(***
 *** Refinement of itree specs
 ***)

Context {E1 E2 : Type -> Type} {R1 R2 : Type}.
Context (RE : relationEH E1 E2) (REAns : relationEAns E1 E2) (RR : R1 -> R2 -> Prop).

(* One itree_spec refines another iff, after turning finitely many quantifier
events to actual quantifiers, they have the same constructor with continuations
such that the first continuation coinductively refines the second *)
Inductive refinesF  (F : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop) : 
  itree_spec' E1 R1 -> itree_spec' E2 R2 -> Prop :=
  | refines_Ret r1 r2 : RR r1 r2 -> refinesF F (RetF r1) (RetF r2)
  | refines_TauLR phi1 phi2 :
      F phi1 phi2 -> refinesF F (TauF phi1) (TauF phi2)
  | refines_TauL phi ophi :
      refinesF F (observe phi) ophi -> refinesF F (TauF phi) ophi
  | refines_TauR ophi phi :
      refinesF F ophi (observe phi) -> refinesF F ophi (TauF phi)
  | refines_VisLR A B e1 e2 kphi1 kphi2 :
      RE A B e1 e2 ->
      (forall a b, REAns A B e1 e2 a b -> F (kphi1 a) (kphi2 b) ) ->
      refinesF F (VisF (Spec_vis e1) kphi1) (VisF (Spec_vis e2) kphi2)
  | refines_forallR A kphi phi :
      (forall a : A, refinesF F phi (observe (kphi a))) ->
      refinesF F phi (VisF Spec_forall kphi)
  | refines_forallL A kphi phi (a : A) :
      (refinesF F (observe (kphi a)) phi) ->
      refinesF F (VisF Spec_forall kphi) phi
  | refines_existsR A kphi phi (a : A) :
      (refinesF F phi (observe (kphi a))) ->
      refinesF F phi (VisF Spec_exists kphi)
  | refines_existsL A kphi phi :
      (forall a : A, refinesF F (observe (kphi a)) phi) ->
      refinesF F (VisF Spec_exists kphi) phi
.
Hint Constructors refinesF.
Definition refines_  F (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2) : Prop :=
  refinesF F (observe t1) (observe t2).

Lemma monotone_refinesF ot1 ot2 sim sim' 
  (LE : sim <2= sim' )
  (IN : refinesF sim ot1 ot2) : 
  refinesF sim' ot1 ot2.
Proof.
  induction IN; eauto.
Qed.

Lemma monotone_refines_  : monotone2 refines_.
Proof. red. intros. eapply monotone_refinesF; eauto. Qed.


(*
Instance Proper_upaco2_refines_ {E R} :
  Proper ((eq ==> eq ==> impl) ==> eq ==> eq ==> impl) (upaco2 (@refines_ E R)).
Proof.
  intros r1 r2 prp_r t1 t2 e12 t3 t4 e34 r13.
  rewrite <- e12. rewrite <- e34.
  destruct r13.
  - left. eapply (paco2_mon _ H).
    intros x y. apply (prp_r x x eq_refl y y eq_refl).
  - right. apply (prp_r _ _ eq_refl _ _ eq_refl H).
Qed.

Lemma bot2_least {T0 T1} (r: rel2 T0 T1) : bot2 <2= r.
Proof.
  intros _ _ [].
Qed.

(* FIXME: there must be a better way to get this result... *)
Lemma upaco2_refinesF_bot_r {E R} r t1 t2 :
  upaco2
    (fun (F : itree_spec E R -> itree_spec E R -> Prop) (t4 t5 : itree_spec E R) =>
     refinesF F (observe t4) (observe t5)) bot2 t1 t2 ->
  upaco2
    (fun (F : itree_spec E R -> itree_spec E R -> Prop) (t0 t4 : itree_spec E R) =>
     refinesF F (observe t0) (observe t4)) r t1 t2.
Proof.
  intro H.
  eapply (Proper_upaco2_refines_ _ _ _ t1 t1 eq_refl t2 t2 eq_refl H). Unshelve.
  intros _ _ _ _ _ _ [].
Qed.
*)

Definition refines : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop :=
  paco2 refines_ bot2.

End Refines.

#[global] Hint Resolve monotone_refines_ : paco.

#[global] Hint Constructors refinesF.

(* need a little library of heterogeneous event relations to express theorems  *)

(* Reflexivity of refinement *)
Instance Reflexive_refines {E R} RE REAns RR : 
  ReflexiveE RE -> ReflexiveEAns REAns -> Reflexive RR -> Reflexive (@refines E E R R RE REAns RR).
Proof.
Abort.
(*  red. pcofix CIH. intros HRR HRE HREAns t. pfold. red.
  destruct (observe t); try destruct e; econstructor; eauto.
  intros. right. apply HRE in H. subst. eauto.
Qed. *)

  (* this exposes a flaw in current definition, could fix by adding restrictions to return values of events like I do in rutt, in the mrec rule it seems like that would be neccesary

  when I make a two related recursive calls, I feel like I need to know that the call events return related
  values otherwise how would I deal with any code that could make a recursive call and then
  use its value to compute something more

  I was confused by something Eddy said before, but now I think I get what was going on,
  in their current setup recursive calls are represented as functions, so a relation over them
  already has the ability to relate inputs and outputs

  in the itrees setting things are more separate, recursive calls are inert events
  a relation over events  cannot on its own impose restrictions on return,
  we will need to impose that separately

  this all seems to come back to the fact that I was right originally

  perhaps the solution should be to have another relation hrefines that is really just for 
  mrec, then can show that hrefines eq eq is the same thing as refines?
  
  although maybe it is simpler to define refines as hrefines eq eq
*)

Lemma refines_Vis_forallR : forall (E1 E2 : Type -> Type) (R1 R2 A : Type) RE REAns RR 
                              (t : itree_spec E1 R1) (k : A -> itree_spec E2 R2),
         refines RE REAns RR t (Vis Spec_forall k) ->
         forall a : A, refines RE REAns RR t (k a).
Proof.
  intros E1 E2 R1 R2 A RE RAns RR. pcofix CIH. intros t k Href a.
  pfold. revert a. red. punfold Href. red in Href.
  cbn in *. remember (observe t) as ot. clear Heqot.
  remember (VisF Spec_forall k) as x.
  hinduction Href before r; intros; inv Heqx; inj_existT; subst; pclearbot; eauto.
  - clear H0. assert (refines RE RAns RR (go phi) (k a) ).
    { pstep. apply H. }
    enough (paco2 (refines_ RE RAns RR) r (go phi) (k a) ).
    { punfold H1. }
    eapply paco2_mon; eauto. intros; contradiction.
Qed.

Lemma refines_Vis_existsL : forall (E1 E2 : Type -> Type) (R1 R2 A : Type) RE REAns RR 
                              (t : itree_spec E1 R1) (k : A -> itree_spec E2 R2),
         refines RE REAns RR (Vis Spec_exists k) t ->
         forall a : A, refines RE REAns RR (k a) t.
Proof.
  intros E1 E2 R1 R2 A RE REAns RR. intros t k Href.
  intros. pfold. red. punfold Href. red in Href.
  remember (observe t) as ot. clear Heqot. cbn in *.
  remember (VisF Spec_exists k) as x. 
  hinduction Href before A; intros; inv Heqx; inj_existT; subst; eauto.
Qed.

(*so this did not give me the inversion principles I naively hoped for,
  but that doesn't necessarily invalidate the padded itree approach,
  it is also worth considering if the trim itree appraoch (which admittedly has problems)
  is better than eddy's tau, multi-refines closure thing
 *)


(* A version of refinesF specialized to a forall on the left *)
Inductive forallRefinesF {E1 E2 R1 R2} RE RAns (RR : R1 -> R2 -> Prop) (F : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop)
          {A} (kphi1: A -> itree_spec E1 R1)
  : itree_spec' E2 R2 -> Prop :=
  | forallRefines_VisLR kphi2 :
      (forall a : A, F (kphi1 a) (kphi2 a)) ->
      forallRefinesF RE RAns RR F kphi1 (VisF Spec_forall kphi2)
  | forallRefines_forallR B kphi2 :
      (forall b : B, forallRefinesF RE RAns RR F kphi1 (observe (kphi2 b))) ->
      forallRefinesF RE RAns RR F kphi1 (VisF Spec_forall kphi2)
  | forallRefines_forallL phi (a : A) :
      refinesF RE RAns RR F (observe (kphi1 a)) phi ->
      forallRefinesF RE RAns RR F kphi1 phi
  | forallRefines_existsR B kphi2 (b : B) :
      (forallRefinesF RE RAns RR F kphi1 (observe (kphi2 b))) ->
      forallRefinesF RE RAns RR F kphi1 (VisF Spec_exists kphi2)
  | forallRefines_TauR phi2 :
    forallRefinesF RE RAns RR F kphi1 (observe phi2) ->
    forallRefinesF RE RAns RR F kphi1 (TauF phi2)
.

(* FIXME: should we replace the recursive call to refinesF in the above with
just a refines? *)

Lemma refinesF_Vis_forallL : forall (E1 E2 : Type -> Type) (R1 R2 A : Type) RE RAns RR F
                                   (t : itree_spec' E2 R2) (k : A -> itree_spec E1 R1),
    refinesF RE RAns RR F (VisF Spec_forall k) t ->
    @forallRefinesF E1 E2 R1 R2 RE RAns RR F A k t.
Proof.
  intros. remember (VisF Spec_forall k) as t1. induction H; try discriminate.
  - constructor. eauto.
  - inversion Heqt1. subst. inj_existT. subst.
    constructor. auto.
  - inversion Heqt1. subst. inj_existT. subst. econstructor; eauto.
  - eapply forallRefines_existsR. eauto.
Qed.

Lemma refines_TauL_inv : forall (E1 E2 : Type -> Type) (R1 R2: Type) RE RAns RR
                                   (phi1 : itree_spec E1 R1) (phi2 : itree_spec E2 R2),
      refines RE RAns RR (Tau phi1) phi2 -> refines RE RAns RR phi1 phi2.
Proof.
  intros E1 E2 R1 R2 RE RAns RR. pcofix CIH.
  intros. pstep. punfold H0. red in H0. red. cbn in *. remember (TauF phi1) as x.
  hinduction H0 before r; intros; inv Heqx; pclearbot; eauto.
  - constructor. pstep_reverse. eapply paco2_mon; eauto. intros; contradiction.
  - rewrite itree_eta'. pstep_reverse.
    apply paco2_mon with (r := bot2). pstep. auto. intros. contradiction.
Qed.

Lemma refines_TauR_inv : forall (E1 E2 : Type -> Type) (R1 R2: Type) RE RAns RR
                                   (phi1 : itree_spec E1 R1) (phi2 : itree_spec E2 R2),
      refines RE RAns RR phi1 (Tau phi2) -> refines RE RAns RR phi1 phi2.
Proof.
  intros E1 E2 R1 R2 RE RAns RR. pcofix CIH.
  intros. pstep. punfold H0. red in H0. red. cbn in *. remember (TauF phi2) as x.
  hinduction H0 before r; intros; inv Heqx; pclearbot; eauto.
  - constructor. pstep_reverse. eapply paco2_mon; eauto. intros; contradiction.
  - rewrite itree_eta' at 1. pstep_reverse.
    apply paco2_mon with (r := bot2). pstep. auto. intros. contradiction.
Qed.
(*
(* it would be a good idea to try to understand if there are other non-trim based counterexamples*)

(*hopefully this should be able to go away now *)
(* A version of refinesF specialized to a Tau on the left *)
Inductive tauRefinesF {E1 E2 R1 R2} (RR : R1 -> R2 -> Prop) (F : itree_spec E1 R1 -> itree_spec E2 R2 -> Prop)
          (phi1: itree_spec E1 R1)
  : itree_spec' E2 R2 -> Prop :=
  | tauRefines_VisLR phi2 : F phi1 phi2 -> tauRefinesF RR F phi1 (TauF phi2)
  | tauRefines_forallR B kphi2 :
      (forall b : B, tauRefinesF  RR F phi1 (observe (kphi2 b))) ->
      tauRefinesF  RR F phi1 (VisF Spec_forall kphi2)
  | tauRefines_existsR B kphi2 (b : B) :
      tauRefinesF RR F phi1 (observe (kphi2 b)) ->
      tauRefinesF RR F phi1 (VisF Spec_exists kphi2)
.

Lemma refinesF_Tau : forall (E1 E2 : Type -> Type) (R1 R2 : Type) RE REAns RR F
                            t1 (t2 : itree_spec' E2 R2),
    refinesF RE REAns RR F (TauF t1) t2 ->
    @tauRefinesF E1 E2 R1 R2 RR F t1 t2.
Proof.
  intros. remember (TauF t1) as t. induction H; inversion Heqt.
  - rewrite <- H1. constructor. assumption.
  - subst. econstructor. intro b. apply H0. assumption.
  - econstructor. apply IHrefinesF. assumption.
Qed.
*)

Inductive isConcreteF {E R} (F : itree_spec E R -> Prop) :
  itree_spec' E R -> Prop :=
  | isConcrete_Ret (r : R) : isConcreteF F (RetF r)
  | isConcrete_Tau (phi : itree_spec E R) :
      F phi -> isConcreteF F (TauF phi)
  | isConcrete_Vis A e kphi :
      (forall a:A, F (kphi a)) -> isConcreteF F (VisF (Spec_vis e) kphi).

Hint Constructors isConcreteF.
Definition isConcrete_ {E R} F (t: itree_spec E R) : Prop :=
  isConcreteF F (observe t).

Lemma monotone_isConcreteF {E R} (ot : itree_spec' E R) sim sim' 
  (LE : sim <1= sim' )
  (IN : isConcreteF sim ot) : 
  isConcreteF sim' ot.
Proof.
  induction IN; eauto.
Qed.

Lemma monotone_isConcrete_ {E R} : monotone1 (@isConcrete_ E R).
Proof. red. intros. eapply monotone_isConcreteF; eauto. Qed.

Hint Resolve monotone_isConcrete_ : paco.

Definition isConcrete {E R} : itree_spec E R -> Prop := paco1 isConcrete_ bot1.

Lemma isConcreteVisInv {E R A} e (k : A -> itree_spec E R) a :
  isConcrete (Vis (Spec_vis e) k) -> isConcrete (k a).
Proof.
  intro isc; punfold isc. inversion isc.
  assert (kphi0 = k); [ inj_existT; assumption | ].
  rewrite H3 in H0. pclearbot. apply H0.
Qed.

Lemma refines_Vis_existsR:
  forall (E1 : Type -> Type) (R1 : Type) (E2 : Type -> Type) (R2 : Type) 
    (RE1 : relationEH E1 E2) (REAns1 : relationEAns E1 E2) (RR1 : R1 -> R2 -> Prop) 
    (A : Type) (kphi : A -> itree_spec E2 R2) (phi1 : itree_spec E1 R1),
    refines RE1 REAns1 RR1 phi1
             (Vis Spec_exists kphi) ->
    isConcrete phi1 -> exists a : A, refines RE1 REAns1 RR1 phi1 (kphi a).
Proof.
  intros E1 R1 E2 R2 RE1 REAns1 RR1 A kphi phi1 Href.
  punfold Href. red in Href.
  cbn in *. intros. punfold H. red in H.
  enough (exists a, refinesF RE1 REAns1 RR1 (upaco2 (refines_ RE1 REAns1 RR1) bot2) 
           (observe phi1) (observe (kphi a))).
  destruct H0. eexists. pstep. eauto.
  remember (VisF Spec_exists kphi) as y.
  hinduction Href before RE1; intros; inv Heqy; eauto.
  - inv H. pclearbot. punfold H1. eapply IHHref in H1; eauto.
    destruct H1. eexists. constructor. eauto.
  - inv H.
  - inv H1.
Qed.


(* so whats next, *)
(* Transitivity of refinement if the LHS is concrete *)
Theorem concreteRefinesTrans {E1 E2 E3 R1 R2 R3} RE1 RE2 REAns1 REAns2 
        (RR1 : R1 -> R2 -> Prop) (RR2 : R2 -> R3 -> Prop) 
        (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2) (t3 : itree_spec E3 R3)
         (isc:isConcrete t1) :
  padded t2 -> padded t3 ->
  refines RE1 REAns1 RR1 t1 t2 -> refines RE2 REAns2 RR2 t2 t3 -> 
  refines (rcomposeE RE1 RE2) (rcomposeEAns REAns1 REAns2 
                                  (fun A B C e1 e2 e3 => RE1 A B e1 e2 /\ RE2 B C e2 e3 ) ) 
          (rcompose RR1 RR2) t1 t3.
Proof.
  revert t1 t2 t3 isc; pcofix CIH. intros t1 t2 t3 isc  Ht2 Ht3 Ht12 Ht23.
  pfold. red. punfold Ht12. red in Ht12.
  punfold Ht23. red in Ht23. punfold Ht3. red in Ht3.
  punfold Ht2. red in Ht2.
  remember (observe t3) as ot3.  clear t3 Heqot3.
  punfold isc. red in isc. remember (observe t1) as ot1. clear t1 Heqot1.
  hinduction Ht12 before r; intros.
  - remember (RetF r2) as x. clear Ht2 Ht3.
    hinduction Ht23 before r; intros; inv Heqx; eauto.
    constructor. econstructor; eauto.
  - pclearbot. 
    assert (Hdec :  (exists t4, ot3 = TauF t4) \/ (forall t4, ot3 <> TauF t4) ).
    { destruct ot3; eauto; right; repeat intro; discriminate. }
    destruct Hdec as [ [t4 Ht4] | Ht4 ]; subst.
    + constructor. right. eapply CIH; eauto. inv isc. pclearbot. auto.
      inv Ht2. pclearbot. auto. inv Ht3. pclearbot. auto.
      apply refines_TauL_inv. apply refines_TauR_inv. pstep. auto.
    + destruct ot3; try (exfalso; eapply Ht4; eauto; fail).
      * constructor. inv Ht23. clear Ht2 Ht3.
        punfold H. red in H. remember (RetF r0) as y.
        remember (observe phi2) as ophi2. 
        hinduction H1 before r; intros; inv Heqy; eauto.
        -- remember (RetF r1) as y. hinduction H0 before r; intros; inv Heqy; eauto.
           constructor. econstructor; eauto.
        -- eapply IHrefinesF; eauto.
           pstep_reverse. apply refines_TauR_inv. pstep. auto.
        -- eapply IHrefinesF; eauto. pstep_reverse.
           eapply refines_Vis_forallR. pstep. auto.
        -- inv isc. pclearbot. 
          assert (exists a, refines RE1 REAns1 RR1 phi1 (kphi a)).
          { apply refines_Vis_existsR; auto. pstep. auto. }
          destruct H2 as [a Ha]. eapply H0; eauto. pstep_reverse.
      * inv Ht3. inj_existT. subst.
        {
          destruct e; pclearbot.
          - inv Ht23. constructor.
            punfold H. red in H. 
            inv isc. pclearbot.
            remember ((VisF (Spec_vis e) (fun a : X => Tau (k1 a)))) as y.
            remember (observe phi2) as ophi2.
            punfold H3. red in H3.
            remember (observe phi1) as ophi1.
            hinduction H2 before r; intros; inv Heqy; inj_existT; subst; eauto.
            + eapply IHrefinesF; eauto. pstep_reverse.
              apply refines_TauR_inv. pstep. auto.
              inv Ht2. rewrite Heqophi2. pclearbot. pstep_reverse.
            +  assert (Hkphi1 : forall a, padded (kphi1 a)).
              {
                inv Ht2. pclearbot. punfold H5. red in H5. rewrite <- Heqophi2 in H5.
                inv H5. inj_existT. subst. intros. pstep. constructor. auto.
              }
              remember (VisF (Spec_vis e1) kphi1 ) as y.
              assert (Hk1 : forall (a : A) (b : X),
                         REAns2 A X e1 e a b -> 
                         upaco2 (refines_ RE2 REAns2 RR2) bot2 (kphi1 a) ((k1 b))).
              intros. apply H0 in H4. clear - H4. pclearbot. left. 
              apply refines_TauR_inv. auto. 
              remember (observe phi1) as ophi1.
              clear H0.
              hinduction H1 before r; intros; inv Heqy; inj_existT; subst; eauto.
              constructor. eapply IHrefinesF; eauto. inv H3. pclearbot. pstep_reverse.
              constructor. econstructor; eauto. intros.
              right. inv H4. inj_existT; subst.
              assert (exists b0 : A0, REAns1 A A0 e1 e0 a b0 /\ REAns2 _ X e0 e b0 b).
              eapply H11; eauto. destruct H4 as [b0 [ Hb01 Hb02] ].
              eapply CIH; eauto. inv H3. inj_existT. subst. pclearbot. apply H5.
              pstep. constructor. left. auto.
              eapply H0 in Hb01. destruct Hb01; eauto. contradiction.
              pstep. constructor. eapply Hk1 in Hb02. pstep_reverse.
              destruct Hb02; auto. contradiction.
              inv H3.
              inv H3.
           + eapply IHrefinesF; eauto. pstep_reverse. eapply refines_Vis_forallR.
             pstep. auto. inv Ht2. pclearbot. punfold H4. red in H4. rewrite <- Heqophi2 in H4.
             inv H4. inj_existT. subst. constructor. left. pstep.
             constructor; auto.
           + remember (VisF Spec_exists kphi) as y. remember (observe phi1) as ophi1.
             hinduction H1 before r; intros; inv Heqy; inj_existT; subst.
             * constructor. eapply IHrefinesF; eauto. inv H3. pclearbot. pstep_reverse.
             * inv H3.
             * eapply H0; eauto. inv Ht2. pclearbot. punfold H5. red in H5.
               rewrite <- Heqophi2 in H5. inv H5. inj_existT. subst.
               constructor. left. pstep. constructor. auto.
             * inv H4.
          - assert (refines RE2 REAns2 RR2 (Tau phi2) (Vis Spec_forall (fun a => Tau (k1 a)) )).
            pstep. auto.
            apply refines_forallR. intros. constructor. right.
            eapply CIH; eauto. inv isc. pclearbot. auto.
            inv Ht2. pclearbot. auto. apply H1.
            apply refines_TauL_inv. apply refines_TauR_inv.
            eapply refines_Vis_forallR in H0. eauto.
          - assert (refines RE2 REAns2 RR2 (Tau phi2) (Vis Spec_exists (fun a => Tau (k1 a)) )).
            pstep. auto. apply refines_TauL_inv in H0.
            punfold H. red in H.
            punfold H0. red in H0.
            cbn in *. remember (VisF Spec_exists (fun a : X => Tau (k1 a))) as y.
            clear Ht23. remember (observe phi2) as ophi2.
            hinduction H0 before r; intros; inv Heqy; inj_existT; subst; eauto.
            + eapply IHrefinesF; eauto. pstep_reverse.
              apply refines_TauR_inv. pstep. auto.  subst.
              inv Ht2. pclearbot. rewrite Heqophi2. pstep_reverse.
            + eapply IHrefinesF; eauto. pstep_reverse.
              eapply refines_Vis_forallR. pstep. auto.
              inv Ht2. pclearbot. punfold H3. red in H3. rewrite <- Heqophi2 in H3.
              inv H3. inj_existT. subst. constructor. left. pclearbot.
              pstep. constructor. left. auto.
            + 
              (*this step did seem to use=need the paddedness condition *)
              eapply refines_existsR. Unshelve. all : auto.
              constructor. right. eapply CIH with (t2 := phi2); eauto. inv isc. pclearbot. auto.
              inv Ht2. pclearbot. auto. apply H1. pstep. auto.
              apply refines_TauR_inv. pstep. auto.
            + (* this may be a mistake, be willing to undo this clear *)
              remember (VisF Spec_exists kphi) as y. remember (observe phi1) as ophi1.
              hinduction H1 before r; intros; inv Heqy.
              * constructor. rewrite <- Heqophi1. eapply IHrefinesF; eauto.
                inv isc. pclearbot. punfold H5. red in H5. rewrite Heqophi1. auto.
              * (* this *) inv isc. pclearbot. clear -H5 Heqophi1. exfalso.
                punfold H5. red in H5. rewrite <- Heqophi1 in H5. inv H5.
              * inj_existT. subst. eapply H0; eauto.
                clear - Heqophi2 Ht2. inv Ht2. pclearbot. punfold H0.
                red in H0. rewrite <- Heqophi2 in H0. inv H0. inj_existT. subst.
                pclearbot. constructor. left. pstep. constructor. left. auto.
              * exfalso. clear - Heqophi1 isc.
                inv isc. pclearbot. punfold H0. red in H0. rewrite <- Heqophi1 in H0.
                inv H0.
          }
  - constructor. eapply IHHt12; eauto. inv isc. pclearbot. punfold H0.
  -  eapply IHHt12; eauto. inv Ht2. pclearbot. pstep_reverse. 
     rewrite itree_eta'. pstep_reverse. apply refines_TauL_inv. pstep. auto.
  - remember (VisF (Spec_vis e2) kphi2) as x.
    hinduction Ht23 before r; intros; inv Heqx; inj_existT; subst; eauto.
    + constructor. eapply IHHt23; eauto. inv Ht3. pclearbot. punfold H2.
    + pclearbot. constructor; eauto. econstructor; eauto.
      intros. right. 
      inv H3. inj_existT. subst.
      assert (exists b0 : B0, REAns1 A0 B0 e0 e3 a b0 /\ REAns2 B0 B e3 e2 b0 b).
      eapply H10; eauto. destruct H3 as [b0 [Hb01 Hb02] ].
      eapply CIH with (t2 := kphi3 b0); eauto.
      * inv isc. inj_existT. subst. pclearbot. apply H4.
      * inv Ht2. inj_existT. subst. pstep. constructor. auto.
      * inv Ht3. inj_existT. subst. pstep. constructor. auto.
      * eapply H2 in Hb01. clear - Hb01. pclearbot. auto.
      * eapply H0 in Hb02. clear - Hb02. pclearbot. auto.
    + constructor. intros. eapply H0; eauto. inv Ht3. inj_existT.
      subst. constructor. left. pclearbot. auto.
    + econstructor. eapply IHHt23; eauto. inv Ht3. inj_existT. subst.
      constructor. auto.
  - remember (refinesF_Vis_forallL _ _ _ _ _ _ _ _ _ _ _ Ht23) as Ht23'.
    clear HeqHt23' Ht23. induction Ht23'; pclearbot.
    * apply refines_forallR. intro a. pclearbot.
      eapply H0. eapply CIH. auto.
      pstep_reverse. Unshelve. all : auto. inv Ht2.
      inj_existT. subst. pstep. constructor. auto. inv Ht3.
      inj_existT. subst. constructor. auto. pstep_reverse. clear - H1. pclearbot.  apply H1.
    * apply refines_forallR. intro b. apply H2.
      inv Ht3. inj_existT. subst. constructor. auto.
    * eapply H0; eauto. inv Ht2. inj_existT. subst. constructor. auto.
    * econstructor. eapply IHHt23'; eauto. inv Ht3. inj_existT. subst. constructor.
      auto.
    * constructor. eapply IHHt23'; eauto. inv Ht3. pclearbot. pstep_reverse.
  - inv isc.
  - eapply IHHt12; eauto. inv Ht2. inj_existT. subst. constructor. auto.
    rewrite itree_eta'.
    pstep_reverse. apply refines_Vis_existsL. pstep. auto.
  - inv isc.
Qed.


Ltac use_simpobs := repeat match goal with
                           | H : RetF _ = observe ?t |- _ => apply simpobs in H 
                           | H : TauF _ = observe ?t |- _ => apply simpobs in H
                           | H : VisF _ _ = observe ?t |- _ => apply simpobs in H
                           end.

Instance eq_itree_refines_Proper1 {E1 E2 R1 R2 RE REAns RR r} :  Proper (eq_itree eq ==> eq_itree eq ==> flip impl) 
                                                           (@refines_ E1 E2 R1 R2 RE REAns RR (upaco2 (refines_ RE REAns RR) r)).
Admitted. (* needs an axiom to prove this *)

Instance eq_itree_refines_Proper2 {E1 E2 R1 R2 RE REAns RR r} :  Proper (eq_itree eq ==> eq_itree eq ==> flip impl) 
                                                           (paco2 (@refines_ E1 E2 R1 R2 RE REAns RR) r).
Admitted.

Theorem refines_bind {E1 E2 R1 R2 S1 S2} RE REAns RR RS
        (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2)
        (k1 : R1 -> itree_spec E1 S1)
        (k2 : R2 -> itree_spec E2 S2) :
  refines RE REAns RR t1 t2 -> (forall r1 r2, RR r1 r2 -> refines RE REAns RS (k1 r1) (k2 r2)) ->
  refines RE REAns RS (ITree.bind t1 k1) (ITree.bind t2 k2).
Proof.
  revert t1 t2. pcofix CIH.
  intros t1 t2 Ht12 Hk12. punfold Ht12. red in Ht12.
  remember (observe t1) as ot1. remember (observe t2) as ot2.
  hinduction Ht12 before r; intros; use_simpobs.
  - cbn. rewrite Heqot1, Heqot2. setoid_rewrite bind_ret_l.
    eapply paco2_mon; [apply Hk12; auto | intros; contradiction] .
  - rewrite Heqot1, Heqot2. repeat rewrite bind_tau. pstep. constructor.
    right. pclearbot. eapply CIH; eauto.
  - rewrite Heqot1, bind_tau. pstep. constructor. 
    pstep_reverse.
  - rewrite Heqot2, bind_tau. pstep. constructor. pstep_reverse.
  - pclearbot. rewrite Heqot1, Heqot2. repeat rewrite bind_vis.
    pstep. constructor; auto. intros. right. eapply CIH; eauto. 

    apply H0 in H1. pclearbot. auto.
 (* - rewrite Heqot1, Heqot2. repeat rewrite bind_vis. pstep. constructor.
    right. eapply CIH; eauto. pclearbot. apply H.
  - rewrite Heqot1, Heqot2. repeat rewrite bind_vis. pstep. constructor.
    right. eapply CIH; eauto. pclearbot. apply H. *)
  - rewrite Heqot2. rewrite bind_vis. pstep. constructor. intros.
    pstep_reverse.
  - rewrite Heqot1. rewrite bind_vis. pstep. econstructor. 
    pstep_reverse.
  - rewrite Heqot2. rewrite bind_vis. pstep. econstructor. pstep_reverse.
  - rewrite Heqot1. rewrite bind_vis. pstep. econstructor. 
    pstep_reverse.
Qed.

(*key lemma for iter here *)
Lemma refines_iter_bind_aux:
  forall (E1 E2 : Type -> Type) (S2 S1 R1 R2 : Type) 
    RE REAns
    (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop)
    (k1 : R1 -> itree_spec E1 (R1 + S1))
    (k2 : R2 -> itree_spec E2 (R2 + S2))
    (r : itree_spec E1 S1 -> itree_spec E2 S2 -> Prop),
    (forall (r1 : R1) (r2 : R2),
        RR r1 r2 -> r (ITree.iter k1 r1) (ITree.iter k2 r2)) ->
    forall (phi1 : itree_spec E1 (R1 + S1)) (phi2 : itree_spec E2 (R2 + S2)),
      refines RE REAns (HeterogeneousRelations.sum_rel RR RS) phi1 phi2 ->
      paco2 (refines_ RE REAns RS) r
            (phi1 >>=
                  (fun lr : R1 + S1 =>
                     match lr with
                     | inl l => Tau (ITree.iter k1 l)
                     | inr r0 => Ret r0
                     end))
            (phi2 >>=
                  (fun lr : R2 + S2 =>
                     match lr with
                     | inl l => Tau (ITree.iter k2 l)
                     | inr r0 => Ret r0
                     end)).
Proof.
  intros E1 E2 S2 S1 R1 R2 RE REAns RR RS k1 k2 r CIH.
  pcofix CIH'. intros phi1 phi2 Hphi.
  punfold Hphi. red in Hphi.
  remember (observe phi1) as ophi1.
  remember (observe phi2) as ophi2.
  hinduction Hphi before r; intros; use_simpobs; try rewrite Heqophi1; try rewrite Heqophi2; pclearbot.
  - setoid_rewrite bind_ret_l. inv H.
    + pstep. constructor. right. eapply CIH; eauto.
    + pstep. constructor; auto.
  - setoid_rewrite bind_tau. pstep. constructor. right. eapply CIH'; eauto.
  - rewrite bind_tau. pstep. constructor. pstep_reverse.
  - rewrite bind_tau. pstep. constructor. pstep_reverse.
  - setoid_rewrite bind_vis. pstep. constructor; auto. right. eapply CIH'; eauto. 
    apply H0 in H1; pclearbot; eauto.
  (*
  - repeat rewrite bind_vis. pstep. constructor. right. eapply CIH'; eauto.
    apply H.
  - repeat rewrite bind_vis. pstep. constructor. right. eapply CIH'; eauto.
    apply H. *)
  - rewrite bind_vis. pstep. constructor. intros. pstep_reverse.
  - rewrite bind_vis. pstep. econstructor. pstep_reverse.
  - rewrite bind_vis. pstep. econstructor. pstep_reverse.
  - rewrite bind_vis. pstep. econstructor. pstep_reverse.
Qed.

(*this one is going to be rougher going to require some nested coinduction, but should be manageable *)
Theorem refines_iter {E1 E2 R1 R2 S1 S2} RE REAns (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop)
        (k1 : R1 -> itree_spec E1 (R1 + S1)) (k2 : R2 -> itree_spec E2 (R2 + S2)) :
  (forall r1 r2, RR r1 r2 -> refines RE REAns (HeterogeneousRelations.sum_rel RR RS) (k1 r1) (k2 r2) ) ->
  forall r1 r2, RR r1 r2 ->  refines RE REAns RS (ITree.iter k1 r1) (ITree.iter k2 r2).
Proof.
  intros Hk. pcofix CIH. intros r1 r2 Hr12.
  rewrite unfold_iter. rewrite unfold_iter.
  specialize (Hk r1 r2 Hr12) as Hkr12.
  punfold Hkr12. red in Hkr12.
  remember (observe (k1 r1) ) as ok1. remember (observe (k2 r2)) as ok2.
  hinduction Hkr12 before r; intros; use_simpobs; try rewrite Heqok1; try rewrite Heqok2.
  - setoid_rewrite bind_ret_l. inv H.
    + pstep. constructor. right. eapply CIH; eauto.
    + pstep. constructor. auto.
  - setoid_rewrite bind_tau. pstep. constructor. left. pclearbot.
    eapply refines_iter_bind_aux; eauto.
  - rewrite bind_tau. pstep. constructor. pstep_reverse.
    eapply refines_iter_bind_aux; eauto.
    apply Hk in Hr12. rewrite Heqok1 in Hr12.
    apply refines_TauL_inv in Hr12. auto.
  - rewrite bind_tau. pstep. constructor. pstep_reverse.
    eapply refines_iter_bind_aux; eauto.
    apply Hk in Hr12. rewrite Heqok2 in Hr12.
    apply refines_TauR_inv in Hr12. auto.
(*  - setoid_rewrite bind_vis. pstep. constructor; auto. left. pclearbot.
    eapply refines_iter_bind_aux; eauto. apply H0 in H1; pclearbot; eauto.
  - setoid_rewrite bind_vis. pstep. constructor; auto. left. pclearbot.
    eapply refines_iter_bind_aux; eauto. apply H. *)
  - setoid_rewrite bind_vis. pstep. constructor; auto. left. pclearbot.
    eapply refines_iter_bind_aux; eauto. 
    eapply H0 in H1. pclearbot. auto.
  - rewrite bind_vis. pstep. constructor. intros. pstep_reverse.
    eapply refines_iter_bind_aux; eauto; subst. all : pstep; apply H; auto.
  - rewrite bind_vis. pstep. econstructor. Unshelve. all : auto. subst.
    pstep_reverse. eapply refines_iter_bind_aux; eauto. pstep. auto.
  - rewrite bind_vis. pstep. econstructor. Unshelve. all : auto.
    pstep_reverse. subst. eapply refines_iter_bind_aux; eauto. pstep. auto.
  - rewrite bind_vis. pstep. constructor. intros. pstep_reverse. subst.
    eapply refines_iter_bind_aux; eauto. pstep. apply H.
Qed.


Definition and_spec {E R} (phi1 phi2 : itree_spec E R) : itree_spec E R :=
  Vis Spec_forall (fun b : bool => if b then phi1 else phi2).

Definition or_spec {E R} (phi1 phi2 : itree_spec E R) : itree_spec E R :=
  Vis Spec_exists (fun b : bool => if b then phi1 else phi2).

Lemma and_spec_correct : forall E R1 R2 (RR : R1 -> R2 -> Prop) (t : itree E R1) (phi1 phi2 : itree_spec E R2),
    satisfies RR t (and_spec phi1 phi2) <-> (satisfies RR t phi1 /\ satisfies RR t phi2).
Proof.
  split; intros.
  - unfold and_spec in H. punfold H. red in H. cbn in *. 
    remember ((VisF Spec_forall (fun b : bool => if b then phi1 else phi2))) as y.
    split; pfold; red; hinduction H before RR; intros; inv Heqy; eauto;
    inj_existT; subst. 
    specialize (H true). eauto. 
    specialize (H false). eauto.
  - pstep. destruct H. red. cbn. constructor. intros [ | ]; cbn; pstep_reverse.
Qed.

Lemma or_spec_correct : forall E R1 R2 (RR : R1 -> R2 -> Prop) (t : itree E R1) (phi1 phi2 : itree_spec E R2),
    satisfies RR t (or_spec phi1 phi2) <-> (satisfies RR t phi1 \/ satisfies RR t phi2).
Proof.
  split; intros.
  - unfold or_spec in H. punfold H. red in H. cbn in *. 
    remember ((VisF Spec_exists (fun b : bool => if b then phi1 else phi2))) as y.
    remember (observe t) as ot. hinduction H before RR; intros; inv Heqy; eauto.
    + use_simpobs.
      assert (t ≈ phi). rewrite Heqot. rewrite tau_eutt. reflexivity. rewrite H0.
      eapply IHsatisfiesF; eauto.
    + inj_existT. subst. destruct a.
      left. pstep. auto.
      right. pstep. auto.
  - pstep. destruct H.
    + econstructor. Unshelve. 2 : apply true. pstep_reverse.
    + econstructor. Unshelve. 2 : apply false. pstep_reverse.
Qed.

Lemma and_spec_bind : forall E R S (phi1 phi2 : itree_spec E R) (kphi : R -> itree_spec E S),
    (and_spec phi1 phi2) >>= kphi ≈ and_spec (phi1 >>= kphi) (phi2 >>= kphi).
Proof.
  intros.
  setoid_rewrite bind_vis. apply eqit_Vis. intros [ | ]; reflexivity.
Qed.

Lemma or_spec_bind : forall E R S (phi1 phi2 : itree_spec E R) (kphi : R -> itree_spec E S),
    (or_spec phi1 phi2) >>= kphi ≈ or_spec (phi1 >>= kphi) (phi2 >>= kphi).
Proof.
  intros.
  setoid_rewrite bind_vis. apply eqit_Vis. intros [ | ]; reflexivity.
Qed.

CoFixpoint interp_mrec_spec' {D E : Type -> Type}
           (ctx : D ~> itree_spec (D +' E)) {R} (ot : itree_spec' (D +' E) R)
  : itree_spec E R :=
  match ot with
  | RetF r => Ret r
  | TauF t' => Tau (interp_mrec_spec' ctx (observe t'))
  | VisF Spec_forall k => Vis Spec_forall (fun x => interp_mrec_spec' ctx (observe (k x)))
  | VisF Spec_exists k => Vis Spec_exists (fun x => interp_mrec_spec' ctx (observe (k x)))
  | VisF (Spec_vis (inl1 d)) k => Tau (interp_mrec_spec' ctx (observe (ctx _ d >>= k)))
  | VisF (Spec_vis (inr1 e)) k =>
    Vis (Spec_vis e) (fun x => interp_mrec_spec' ctx (observe (k x)))
  end.

Definition interp_mrec_spec {D E : Type -> Type}
           (ctx : D ~> itree_spec (D +' E)) {R} (t : itree_spec (D +' E) R) :=
  interp_mrec_spec' ctx (observe t).

Definition mrec_spec {D E : Type -> Type}
           (ctx : D ~> itree_spec (D +' E)) : D ~> itree_spec E :=
  fun R d => interp_mrec_spec ctx (ctx _ d).

Arguments mrec_spec {D E} & ctx [T].

Section Refines5.
  Context {E1 E2 : Type -> Type}.
  Context (RE : relationEH E1 E2) (REAns : relationEAns E1 E2).

  Inductive refines5F (F : forall R1 R2, (R1 -> R2 -> Prop) -> itree_spec E1 R1 -> itree_spec E2 R2 -> Prop) :
     forall R1 R2, (R1 -> R2 -> Prop) -> itree_spec' E1 R1 -> itree_spec' E2 R2 -> Prop := 
  | refines5F_Ret R1 R2 (RR : R1 -> R2 -> Prop) r1 r2 : RR r1 r2 -> refines5F F _ _ RR (RetF r1) (RetF r2)
  | refine5F_Tau R1 R2 RR t1 t2 : F R1 R2 RR t1 t2 -> refines5F F _ _ RR (TauF t1) (TauF t2)
  | refines5F_SpecVis R1 R2 (RR : R1 -> R2 -> Prop) A B (e1 : E1 A) (e2 : E2 B) k1 k2 :
    RE A B e1 e2 ->
    (forall a b, REAns A B e1 e2 a b -> F R1 R2 RR (k1 a) (k2 b) ) ->
    refines5F F R1 R2 RR (VisF (Spec_vis e1) k1) (VisF (Spec_vis e2) k2)
(*  | refines5F_Forall R1 R2 (RR : R1 -> R2 -> Prop) A
                     (k1 : A -> itree_spec E1 R1) (k2 : A -> itree_spec E2 R2) :
    (forall a, F R1 R2 RR (k1 a) (k2 a) ) -> refines5F F _ _ RR 
                                              (VisF Spec_forall k1) (VisF Spec_forall k2)
  | refines5F_Exists R1 R2 (RR : R1 -> R2 -> Prop) A
                     (k1 : A -> itree_spec E1 R1) (k2 : A -> itree_spec E2 R2) :
    (forall a, F R1 R2 RR (k1 a) (k2 a) ) -> refines5F F _ _ RR 
                                              (VisF Spec_exists k1) (VisF Spec_exists k2) *)
  | refines5F_TauL R1 R2 (RR : R1 -> R2 -> Prop) t1 ot2 : 
    refines5F F R1 R2 RR (observe t1) ot2 ->
    refines5F F R1 R2 RR (TauF t1) ot2
  | refines5F_TauR R1 R2 (RR : R1 -> R2 -> Prop) ot1 t2 :
    refines5F F R1 R2 RR ot1 (observe t2) ->
    refines5F F R1 R2 RR ot1 (TauF t2)
  | refines5F_ForallL R1 R2 (RR : R1 -> R2 -> Prop) A
                      (k1 : A -> itree_spec E1 R1) ot (a : A) : 
    refines5F F R1 R2 RR (observe (k1 a)) ot ->
    refines5F F R1 R2 RR (VisF Spec_forall k1) ot
  | refines5F_ForallR R1 R2 (RR : R1 -> R2 -> Prop) A
                      ot (k2 : A -> itree_spec E2 R2) :
    (forall a, refines5F F R1 R2 RR ot (observe (k2 a)) ) ->
    refines5F F R1 R2 RR ot (VisF Spec_forall k2)
  | refines5F_ExistL R1 R2 (RR : R1 -> R2 -> Prop) A
                      (k1 : A -> itree_spec E1 R1) ot :
    (forall a, refines5F F R1 R2 RR (observe (k1 a)) ot ) ->
    refines5F F R1 R2 RR (VisF Spec_exists k1) ot
  | refines5F_ExistR R1 R2 (RR : R1 -> R2 -> Prop) A
                      ot (k2 : A -> itree_spec E2 R2) a:
    refines5F F R1 R2 RR ot (observe (k2 a)) ->
    refines5F F R1 R2 RR ot (VisF Spec_exists k2)
.

  Hint Constructors refines5F.

  Definition refines5_ F R1 R2 RR t1 t2 :=
    refines5F F R1 R2 RR (observe t1) (observe t2).

  Lemma refines5_monot : monotone5 refines5_.
  Proof.
    unfold refines5_. red. intros. 
    induction IN; eauto.
  Qed.

  Definition refines5 := paco5 refines5_ bot5.

End Refines5.

#[global] Hint Resolve refines5_monot : paco.

#[local] Hint Constructors refines5F.

Lemma refines_to_refines5 (E1 E2 : Type -> Type) (R1 R2 : Type) 
      RE REAns (RR : R1 -> R2 -> Prop) : 
  forall (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2),
    refines RE REAns RR t1 t2 -> refines5 RE REAns R1 R2 RR t1 t2.
Proof.
  pcofix CIH. intros. pstep. red.
  punfold H0. red in H0.
  hinduction H0 before r; intros; pclearbot; eauto.
  constructor; auto. intros. eapply H0 in H1. pclearbot.
  right. eapply CIH; eauto.
Qed.

Lemma refines5_to_refines (E1 E2 : Type -> Type) (R1 R2 : Type) 
      RE REAns (RR : R1 -> R2 -> Prop) : 
  forall (t1 : itree_spec E1 R1) (t2 : itree_spec E2 R2),
    refines5 RE REAns R1 R2 RR t1 t2 -> refines RE REAns RR t1 t2.
Proof.
  pcofix CIH. intros. pstep. red.
  punfold H0. red in H0.
  hinduction H0 before r; intros; pclearbot; eauto.
  constructor; auto. intros. eapply H0 in H1. pclearbot.
  right. eapply CIH; eauto.
Qed.


Section MRecSpec.


Context (D1 D2 E1 E2 : Type -> Type).

Context (bodies1 : D1 ~> itree_spec (D1 +' E1)) (bodies2 : D2 ~> itree_spec (D2 +' E2)).

Context (RE : relationEH E1 E2) (REAns : relationEAns E1 E2).
Context (REInv : relationEH D1 D2) (REAnsInv : relationEAns D1 D2).

Context (Hbodies : forall A B (d1 : D1 A) (d2 : D2 B), 
            REInv A B d1 d2 -> refines (sum_relE REInv RE) (sum_relEAns REAnsInv REAns) 
                                 (REAnsInv A B d1 d2) (bodies1 A d1) (bodies2 B d2) ).

(*         (forall (phi2 : itree_spec (D2 +' E2) B) (phi1 : itree_spec (D1 +' E1) A),
            paco2 (refines_ (sum_relE REInv RE) (sum_relEAns REAnsInv REAns) (REAnsInv A B d1 d2)) bot2 phi1
                  phi2 ->
            r A B (REAnsInv A B d1 d2) (interp_mrec_spec' bodies1 (observe phi1))
              (interp_mrec_spec' bodies2 (observe phi2))) *)

    Lemma refines_interp_mrec_aux:
      forall (A : Type) (d1 : D1 A) (B : Type) (d2 : D2 B)
             (r : forall x x0 : Type, (x -> x0 -> Prop) -> itree_spec E1 x -> itree_spec E2 x0 -> Prop),
        (forall (A0 : Type) (init1 : D1 A0) (B0 : Type) (init2 : D2 B0),
            REInv A0 B0 init1 init2 ->
            r A0 B0 (REAnsInv A0 B0 init1 init2) (mrec_spec bodies1 init1) (mrec_spec bodies2 init2)) ->
        forall (phi2 : itree_spec (D2 +' E2) B) (phi1 : itree_spec (D1 +' E1) A),
          paco2 (refines_ (sum_relE REInv RE) (sum_relEAns REAnsInv REAns) (REAnsInv A B d1 d2)) bot2 phi1
                phi2 ->
          paco5 (refines5_ RE REAns) r A B (REAnsInv A B d1 d2) (interp_mrec_spec' bodies1 (observe phi1))
                (interp_mrec_spec' bodies2 (observe phi2)).
    Proof.
      intros A d1 B d2 r. intros CIH1. pcofix CIH2. intros phi2 phi1 Hphi.
      punfold Hphi. red in Hphi. pstep. red. 
      hinduction Hphi before r; intros; eauto.
      - cbn. constructor; auto.
      - cbn. constructor. right. pclearbot. eapply CIH2; eauto.
      - cbn. constructor. eauto.
      - cbn. constructor. eauto.
      - inv H; inj_existT; subst.
        + cbn. constructor. right. eapply CIH2; eauto. 
          eapply refines_bind. eapply Hbodies; eauto.
          intros. eapply sum_relEAns_inl in H. eapply H0 in H.
          pclearbot. auto.
        + cbn. constructor; auto. intros. right. eapply CIH2; eauto.
          eapply sum_relEAns_inr in H. eapply H0 in H. pclearbot. auto.
     (* - cbn. constructor. right. eapply CIH2; pclearbot; eauto.
      - cbn. constructor. right. eapply CIH2; pclearbot; eauto. *)
      - cbn. constructor. intros. eapply H0; eauto.
      - cbn. econstructor. eapply IHHphi; eauto.
      - cbn. econstructor. eapply IHHphi; eauto.
      - cbn. constructor. intros. eapply H0; eauto.
    Qed.

Theorem refines_mrec : forall A B (init1 : D1 A) (init2 : D2 B),
    REInv A B init1 init2 -> refines RE REAns (REAnsInv A B init1 init2)
                                    (mrec_spec bodies1 init1) (mrec_spec bodies2 init2).
Proof.
  intros. apply refines5_to_refines. generalize dependent B.
  generalize dependent A. pcofix CIH. intros A d1 B d2 Hd.
  unfold mrec_spec, interp_mrec_spec.
  pstep. red. cbn.
  eapply Hbodies in Hd as Hd'. punfold Hd'. red in Hd'.
  hinduction Hd' before r; intros; pclearbot; eauto.
  - cbn. constructor; auto.
  - cbn. constructor. left. eapply refines_interp_mrec_aux; eauto.
  - cbn. constructor. eauto.
  - cbn. constructor. eauto.
  - inv H; inj_existT; subst; cbn.
    + constructor. left. eapply refines_interp_mrec_aux; eauto.
      eapply refines_bind; eauto. intros.
      eapply sum_relEAns_inl in H. eapply H0 in H. pclearbot. auto.
    + constructor; auto. intros. left. 
      eapply refines_interp_mrec_aux; eauto.
      eapply sum_relEAns_inr in H. eapply H0 in H. pclearbot. auto.
  (* - cbn. constructor. left. eapply refines_interp_mrec_aux; eauto.
  - cbn. constructor. left. eapply refines_interp_mrec_aux; eauto. *)
  - cbn. constructor. intros. eapply H0; eauto.
  - cbn. econstructor. eapply IHHd'; eauto.
  - cbn. econstructor. eapply IHHd'; eauto.
  - cbn. constructor. intros; eapply H0; eauto.
Qed.


End MRecSpec.
