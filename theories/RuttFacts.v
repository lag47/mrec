From Coq Require Export Morphisms Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.

From Equations Require Import Equations.

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
  

Section Rutt6.

Context (D1 D2 E1 E2 : Type -> Type).
Context (REvE : relationEH E1 E2).
Context (REvAns : forall A B : Type, E1 A -> A -> E2 B -> B -> Prop ).

Context (REvInv : relationEH D1 D2).
Context (REvAnsInv : forall A B : Type, D1 A -> A -> D2 B -> B -> Prop).

Inductive rutt6F (sim : forall (A B : Type), D1 A -> D2 B -> itree E1 A -> itree E2 B -> Prop) :
   forall (A B : Type), D1 A -> D2 B -> itree' E1 A -> itree' E2 B -> Prop := 
  (* shows how the post condition of the itrees is reliant on d1 and d2*)
  | rutt6RetF (A B : Type) (d1 : D1 A) (d2 : D2 B) a b : 
    REvAnsInv A B d1 a d2 b -> rutt6F sim A B d1 d2 (RetF a) (RetF b)
  | rutt6TauF (A B : Type) (d1 : D1 A) (d2 : D2 B) t1 t2 :
    sim A B d1 d2 t1 t2 -> rutt6F sim A B d1 d2 (TauF t1) (TauF t2)
  | rutt6VisF (A B C D : Type) (d1 : D1 A) (d2 : D2 B) (e1 : E1 C) (e2 : E2 D) k1 k2 :
    REvE C D e1 e2 ->
    (forall c d, REvAns C D e1 c e2 d -> sim A B d1 d2 (k1 c) (k2 d) ) ->
    rutt6F sim A B d1 d2 (VisF e1 k1) (VisF e2 k2)

  | rutt5TauL (A B : Type) (d1 : D1 A) (d2 : D2 B) t1 ot2 : 
    rutt6F sim A B d1 d2 (observe t1) ot2 ->
    rutt6F sim A B d1 d2 (TauF t1) ot2
  | rutt5TauR (A B : Type) (d1 : D1 A) (d2 : D2 B) ot1 t2 : 
    rutt6F sim A B d1 d2 ot1 (observe t2) ->
    rutt6F sim A B d1 d2 ot1 (TauF t2)
.

Hint Constructors rutt6F : itree.

Definition rutt6_ sim A B d1 d2 t1 t2 := rutt6F sim A B d1 d2 (observe t1) (observe t2).

Hint Unfold rutt6_ : itree.

Lemma rutt6_monot : monotone6 rutt6_.
Proof.
  repeat intro. red in IN. red.
  induction IN; eauto with itree.
Qed.



Definition rutt6 : forall (A B : Type), D1 A -> D2 B -> itree E1 A -> itree E2 B -> Prop := paco6 rutt6_ bot6.

#[local] Hint Resolve rutt6_monot : paco.

Lemma rutt6_to_rutt (A B : Type) (d1 : D1 A) (d2 : D2 B) :
  forall (t1 : itree E1 A) (t2 : itree E2 B), 
    rutt6 A B d1 d2 t1 t2 ->
    rutt REvE REvAns (extract REvAnsInv d1 d2) t1 t2.
Proof.
  pcofix CIH. intros t1 t2 Ht12. punfold Ht12. red in Ht12. pstep. red.
  hinduction Ht12 before r; intros; pclearbot; eauto with itree.
  - constructor; auto.
  - constructor. right. apply CIH; auto.
  - constructor; auto. intros. apply H0 in H1. pclearbot. right.
    apply CIH; auto.
  - constructor. eauto.
  - constructor; eauto.
Qed.

Lemma rutt_to_rutt6 (A B : Type) (d1 : D1 A) (d2 : D2 B) :
  forall (t1 : itree E1 A) (t2 : itree E2 B), 
    rutt REvE REvAns (extract REvAnsInv d1 d2) t1 t2 ->
    rutt6 A B d1 d2 t1 t2.
Proof.
  pcofix CIH. intros t1 t2 Ht12. punfold Ht12. red in Ht12. pstep. red.
  hinduction Ht12 before r; intros; pclearbot; eauto with itree.
  constructor; auto. intros. apply H0 in H1. pclearbot. right. apply CIH; auto.
Qed.

End Rutt6.

#[global] Hint Resolve rutt6_monot : paco.

Ltac use_simpobs := repeat match goal with
                           | H : RetF _ = observe ?t |- _ => apply simpobs in H 
                           | H : TauF _ = observe ?t |- _ => apply simpobs in H
                           | H : VisF _ _ = observe ?t |- _ => apply simpobs in H
                           end.

Instance grutt_cong_eqit_eq {E1 E2 R1 R2 r rg} {RR : R1 -> R2 -> Prop} {REv RAns} :

  Proper (@eq_itree E1 R1 R1 eq ==> @eq_itree E2 R2 R2 eq  ==> flip impl)
         (gpaco2 (rutt_ REv RAns RR) (euttge_trans_clo RR) r rg  ).
Proof. eapply grutt_cong_eqit; intros; subst; auto. Qed.

Instance grutt_cong_euttge_eq {E1 E2 R1 R2 r rg} {RR : R1 -> R2 -> Prop} {REv RAns} :

  Proper (@euttge E1 R1 R1 eq ==> @euttge E2 R2 R2 eq  ==> flip impl)
         (gpaco2 (rutt_ REv RAns RR) (euttge_trans_clo RR) r rg  ).
Proof. eapply grutt_cong_euttge; intros; subst; auto. Qed.

(*move this to rutt theory*)
Lemma rutt_bind (E1 E2 : Type -> Type) (R1 R2 S1 S2 : Type) (REvE : relationEH E1 E2) (REvAns : relationEAnsH E1 E2) 
  (RR : R1 -> R2 -> Prop) (RS : S1 -> S2 -> Prop) k1 k2 :
  (forall r1 r2, RR r1 r2 -> rutt REvE REvAns RS (k1 r1) (k2 r2) ) ->
  forall t1 t2, rutt REvE REvAns RR t1 t2 -> rutt REvE REvAns RS (bind t1 k1) (bind t2 k2).
Proof.
  intros Hk. ginit. gcofix CIH. intros. punfold H0. red in H0.
  remember (observe t1) as x. remember (observe t2) as y.
  hinduction H0 before r; intros; use_simpobs.
  - rewrite Heqx, Heqy. setoid_rewrite bind_ret_l. gfinal. right.
    eapply paco2_mon; [eapply Hk; eauto | intros; contradiction].
  - rewrite Heqx, Heqy. setoid_rewrite bind_tau. gstep. constructor.
    gfinal. pclearbot. left. apply CIH. auto.
  - rewrite Heqx, Heqy. setoid_rewrite bind_vis. gstep. constructor. auto.
    intros. apply H0 in H1. pclearbot. gfinal. left. eapply CIH. auto.
  - rewrite Heqx. rewrite tau_euttge. eauto.
  - rewrite Heqy. rewrite tau_euttge. eauto.
Qed.


Variant EvEq {E : Type -> Type} : forall (A B : Type), E A -> E B -> Prop :=
  | eveq (A : Type) (e : E A) : EvEq A A e e.

Variant EvEqAns {E : Type -> Type} : forall A B, E A -> A -> E B -> B -> Prop :=
  | eveqans A (e : E A) (a : A) : EvEqAns A A e a e a.

Lemma rutt_to_eutt (E : Type -> Type) R1 R2 RR : 
  forall (t1 : itree E R1) (t2 : itree E R2),
    rutt EvEq EvEqAns RR t1 t2 -> eutt RR t1 t2.
Proof.
  ginit. gcofix CIH. intros t1 t2 Ht12. punfold Ht12. red in Ht12.
  remember (observe t1) as ot1. remember (observe t2) as ot2.
  hinduction Ht12 before r; intros; use_simpobs.
  - rewrite Heqot1, Heqot2. gstep. constructor. auto.
  - rewrite Heqot1, Heqot2. gstep. constructor. gfinal. left. pclearbot. eauto.
  - rewrite Heqot1, Heqot2. dependent destruction H. gstep. constructor. intros.
    gfinal. left. apply CIH. assert (EvEqAns A A e v e v). constructor. apply H0 in H. pclearbot. auto.
  - rewrite Heqot1, tau_euttge. auto.
  - rewrite Heqot2, tau_euttge. auto.
Qed. 

(*this is working fine but very annoying finish it monday morning*)
Lemma rutt_cong_eqit_eql: forall (E1 E2 : Type -> Type) (R1 R2 : Type)
                            (RR : R1 -> R2 -> Prop)
                            (REv : forall A B : Type, E1 A -> E2 B -> Prop)
                            (RAns : forall A B : Type, E1 A -> A -> E2 B -> B -> Prop)
                            (b1 b2 : bool) (t1 t2 : itree E1 R1) (t4 : itree E2 R2),
    eqit eq b1 b2 t1 t2 ->
    rutt REv RAns RR t2 t4 -> rutt REv RAns RR t1 t4.
Proof.
  intros E1 E2 R1 R2 RR REv RAns b1 b2. ginit. gcofix CIH. 
  intros t1 t2 t4 Ht12 Ht24. punfold Ht24. red in Ht24.
  punfold Ht12. red in Ht12. remember (observe t1) as x.
  remember (observe t2) as y. remember (observe t4) as z.
  hinduction Ht24 before r; intros; use_simpobs.
  - remember (RetF r1) as or. hinduction Ht12 before r; intros; inv Heqor; use_simpobs; eauto.
    + rewrite Heqz. rewrite Heqx. gstep. constructor. auto.
    + rewrite Heqx. rewrite tau_euttge. eauto.
  - assert (DEC: (exists m3, x = TauF m3) \/ (forall m3, x <> TauF m3)).
     { destruct x; eauto; right; repeat intro; discriminate. }
     destruct DEC as [ [m3 Hm3]  | Hx ].
     + subst. symmetry in Hm3. use_simpobs. rewrite Hm3, Heqz. gstep. constructor.
       gfinal. left. pclearbot. eapply CIH; eauto. apply eqit_inv_Tau. rewrite <- Hm3.
       pstep. auto.
     + destruct x; try (exfalso; eapply Hx; eauto; fail).
       {
         pclearbot. use_simpobs. rewrite Heqx. clear Heqx t1. rewrite Heqz, tau_euttge. clear Heqz t4 Hx.
         inv Ht12. punfold H. red in H. remember (RetF r0) as x.
         hinduction REL before r; intros; inv Heqx; use_simpobs.
         - gfinal. right. eapply paco2_mon; [ pstep; apply H | intros; contradiction].
         - eapply IHREL; eauto. pstep_reverse. apply rutt_inv_Tau_l. pstep. auto.
       }
       {
         pclearbot. rewrite Heqz, tau_euttge. use_simpobs. rewrite Heqx. inv Ht12. 
         punfold H. red in H. remember (VisF e k) as x. hinduction REL before r; intros; inv Heqx0; inj_existT; subst.
         - pclearbot. remember (VisF e0 k2) as x. remember (observe m2) as om2.
           hinduction H before r; intros; inv Heqx0; inj_existT; subst.
           + use_simpobs. rewrite Heqom2. gstep. constructor; auto. intros. apply H0 in H1.
             pclearbot. gfinal. left. eapply CIH; eauto. apply REL.
           + use_simpobs. rewrite Heqom2. rewrite tau_euttge. eauto.
         - eapply IHREL; eauto. pstep_reverse. apply rutt_inv_Tau_l. pstep. auto.
       }
  - rewrite Heqz. remember (VisF e1 k1) as y. hinduction Ht12 before r; intros; inv Heqy0; inj_existT; subst; use_simpobs.
    + rewrite Heqx. gstep. constructor; auto. intros. pclearbot. gfinal. left. eapply CIH; eauto.
      apply REL. apply H0 in H1. pclearbot. auto.
    + rewrite Heqx, tau_euttge; eauto.
  - subst.
    inv Ht12. pclearbot; use_simpobs.
    + rewrite H0, tau_euttge. eapply IHHt24; eauto. pstep_reverse.
    + use_simpobs. rewrite H0, tau_euttge. inv CHECK. eapply IHHt24; eauto. 
      pstep_reverse. apply eqit_inv_Tau_r. pstep. auto.
    + eapply IHHt24; eauto.
  - rewrite Heqz, tau_euttge. eauto.
Qed.

Lemma rutt_cong_eqit_eqr: forall (E1 E2 : Type -> Type) (R1 R2 : Type)
                            (RR : R1 -> R2 -> Prop)
                            (REv : forall A B : Type, E1 A -> E2 B -> Prop)
                            (RAns : forall A B : Type, E1 A -> A -> E2 B -> B -> Prop)
                            (b1 b2 : bool) (t1 : itree E1 R1) (t2 t4 : itree E2 R2),
    eqit eq b1 b2 t2 t4 ->
    rutt REv RAns RR t1 t2 -> rutt REv RAns RR t1 t4.
Proof.
  intros E1 E2 R1 R2 RR REv RAns b1 b2. ginit. gcofix CIH. 
  intros t1 t2 t4 Ht12 Ht24. punfold Ht24. red in Ht24.
  punfold Ht12. red in Ht12. remember (observe t1) as x.
  remember (observe t2) as y. remember (observe t4) as z.
  hinduction Ht24 before r; intros; use_simpobs.
  - remember (RetF r2) as or. hinduction Ht12 before r; intros; inv Heqor; use_simpobs; eauto.
    + rewrite Heqz. rewrite Heqx. gstep. constructor. auto.
    + rewrite Heqz. rewrite tau_euttge. eauto.
  - assert (DEC: (exists m3, z = TauF m3) \/ (forall m3, z <> TauF m3)).
     { destruct z; eauto; right; repeat intro; discriminate. }
     destruct DEC as [ [m3 Hm3]  | Hz ].
     + subst. symmetry in Hm3. use_simpobs. rewrite Hm3, Heqx. gstep. constructor.
       gfinal. left. pclearbot. eapply CIH; eauto. apply eqit_inv_Tau. rewrite <- Hm3.
       pstep. auto.
     + destruct z; try (exfalso; eapply Hz; eauto; fail).
       {
         pclearbot. use_simpobs. rewrite Heqx. clear Heqx t1. rewrite Heqz, tau_euttge.
         inv Ht12. punfold H. red in H. remember (RetF r0) as x.
         hinduction REL before r; intros; inv Heqx; use_simpobs.
         - gfinal. right. eapply paco2_mon; [ pstep; apply H | intros; contradiction].
         - eapply IHREL; eauto. pstep_reverse. apply rutt_inv_Tau_r. pstep. auto.
       }
       {
         pclearbot. use_simpobs. rewrite Heqz, Heqx, tau_euttge. inv Ht12. 
         punfold H. red in H. remember (VisF e k) as x. hinduction REL before r; intros; inv Heqx0; inj_existT; subst.
         - pclearbot. remember (VisF e0 k1) as x. remember (observe m1) as om2.
           hinduction H before r; intros; inv Heqx0; inj_existT; subst.
           + use_simpobs. rewrite Heqom2. gstep. constructor; auto. intros. apply H0 in H1.
             pclearbot. gfinal. left. eapply CIH; eauto. apply REL.
           + use_simpobs. rewrite Heqom2. rewrite tau_euttge. eauto.
         - eapply IHREL; eauto. pstep_reverse. apply rutt_inv_Tau_r. pstep. auto.
       }
  - rewrite Heqx. remember (VisF e2 k2) as y. hinduction Ht12 before r; intros; inv Heqy0; inj_existT; subst; use_simpobs.
    + rewrite Heqz. gstep. constructor; auto. intros. pclearbot. gfinal. left. eapply CIH; eauto.
      apply REL. apply H0 in H1. pclearbot. auto.
    + rewrite Heqz, tau_euttge; eauto.
  - rewrite Heqx, tau_euttge. eapply IHHt24; eauto.
  - inv Ht12. pclearbot; use_simpobs.
    + rewrite H1, tau_euttge. eapply IHHt24; eauto. pstep_reverse.
    + eapply IHHt24; eauto.
    + use_simpobs. rewrite H0, tau_euttge. eapply IHHt24; eauto. inv CHECK. pstep_reverse.
      eapply eqit_inv_Tau_l. pstep. auto.
Qed.

Instance rutt_cong_eqit_eq {E1 E2 R1 R2} {RR : R1 -> R2 -> Prop} {REv RAns} b1 b2 :
  Proper (@eqit E1 R1 R1 eq b1 b2 ==> @eqit E2 R2 R2 eq b1 b2 ==> flip impl) (rutt REv RAns RR).
Proof.
  intros t1 t2 Ht12 t3 t4 Ht34 H.
  eapply rutt_cong_eqit_eql; eauto. eapply rutt_cong_eqit_eqr; eauto. apply eqit_flip in Ht34. 
  eapply eqit_mon; try apply Ht34; eauto.
Qed.

(*turn rutt6 to rutt5*)
(*come up with a transitivity closure for rutt5*)
(* prove euttge and eq_itree rewrite rules*)
(*come up with a bind closure for rutt5*)      

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



Instance eq_itree_Proper {E1 E2 R1 R2} {R : itree E1 R1 -> itree E2 R2 -> Prop} :  Proper (@eq_itree E1 R1 R1 eq ==> @eq_itree E2 R2 R2 eq ==> flip impl) R.                                                           
Admitted. (* needs an axiom to prove this, can be more specific later, possibly even do some gpaco stuff, but for now I just
             want to see how it works out *)


Lemma rutt_mrec_interp_mrec_aux:
  forall (A : Type) (d1 : D1 A) (B : Type) 
    (d2 : D2 B)
    (r : forall x x0 : Type, D1 x -> D2 x0 -> itree E x -> itree E x0 -> Prop),
    (forall (A0 : Type) (init1 : D1 A0) (B0 : Type)
       (init2 : D2 B0),
        REvInv A0 B0 init1 init2 ->
        r A0 B0 init1 init2 (mrec bodies1 init1) (mrec bodies2 init2)) ->
    (forall (m1 : itree (D1 +' E) A) (m2 : itree (D2 +' E) B),
        paco2
          (rutt_ (sum_relE REvInv REvE) (sum_relAns REvAnsInv REvAns)
                 (extract REvAnsInv d1 d2)) bot2 m1 m2 ->
        r A B d1 d2 (interp_mrec bodies1 m1) (interp_mrec bodies2 m2)) ->
    forall (m1 : itree (D1 +' E) A) (m2 : itree (D2 +' E) B),
      paco2
        (rutt_ (sum_relE REvInv REvE) (sum_relAns REvAnsInv REvAns)
               (extract REvAnsInv d1 d2)) bot2 m1 m2 ->
      paco6 (rutt6_ D1 D2 E E REvE REvAns REvAnsInv) r A B d1 d2
            (interp_mrec bodies1 m1) (interp_mrec bodies2 m2).
Proof.
  intros A d1 B d2 r. intros CIH1 CIH2 m1 m2 Hm.
  punfold Hm. red in Hm. remember (observe m1) as x. remember (observe m2) as y.
  hinduction Hm before r; intros; use_simpobs.
  - rewrite Heqx, Heqy. setoid_rewrite unfold_iter. cbn. setoid_rewrite bind_ret_l.
    pstep. constructor; auto.
  - pclearbot. rewrite Heqx, Heqy. setoid_rewrite unfold_iter.
    cbn. setoid_rewrite bind_ret_l. pstep. constructor. right.
    eapply CIH2; eauto.
  - rewrite Heqx, Heqy. inversion H; inj_existT; subst.
    + setoid_rewrite unfold_iter. cbn.
      setoid_rewrite bind_ret_l. pstep. constructor. right. eapply CIH2.
      eapply rutt_bind; eauto.
      intros. red in H1.
      eapply sum_relEAns_inl in H1. apply H0 in H1. pclearbot. auto.
    + setoid_rewrite unfold_iter. cbn.
      setoid_rewrite bind_vis. setoid_rewrite bind_ret_l.
      pstep. constructor; auto. intros. left. pstep. constructor.
      right. eapply CIH2; eauto. 
      assert (sum_relAns REvAnsInv REvAns A0 B0 (inr1 f1) c (inr1 f2) d). constructor. auto.
      apply H0 in H2. pclearbot. auto.
  - rewrite Heqx. setoid_rewrite unfold_iter at 1. cbn. setoid_rewrite bind_ret_l.
    pstep. constructor. pstep_reverse.
  - rewrite Heqy. setoid_rewrite unfold_iter at 2. cbn. setoid_rewrite bind_ret_l.
    pstep. constructor. pstep_reverse.
Qed.

Theorem rutt_mrec : 
  forall A B (init1 : D1 A) (init2 : D2 B), 
    REvInv A B init1 init2 -> rutt REvE REvAns (extract REvAnsInv init1 init2)
         (mrec bodies1 init1) (mrec bodies2 init2).
Proof.
  intros. apply rutt6_to_rutt. generalize dependent B. generalize dependent A.
  pcofix CIH. unfold mrec. intros A d1 B d2 Hd12.
  specialize (Hbodies A B d1 d2 Hd12) as Hbodiesd.
  punfold Hbodiesd. red in Hbodiesd. remember (observe (bodies1 A d1)) as x.
  remember (observe (bodies2 B d2)) as y. hinduction Hbodiesd before r; intros; use_simpobs; pclearbot.
  - rewrite Heqx, Heqy. unfold interp_mrec. setoid_rewrite unfold_iter. setoid_rewrite bind_ret_l. 
    pstep. constructor. auto.
  - rewrite Heqx, Heqy. 
    unfold interp_mrec at 1. rewrite unfold_iter. cbn. rewrite bind_ret_l.
    fold (interp_mrec bodies1 m1).
    unfold interp_mrec at 2. rewrite unfold_iter. cbn. rewrite bind_ret_l.
    fold (interp_mrec bodies2 m2). pstep. constructor. left. 
    clear Heqx Heqy. generalize dependent m2. revert m1.
    pcofix CIH'. eapply rutt_mrec_interp_mrec_aux; eauto.
  - (* this may be set up wrong*)
    assert (Vis e1 k1 ≅ bind (trigger e1) k1 ). setoid_rewrite bind_trigger. reflexivity.
    assert (Vis e2 k2 ≅ bind (trigger e2) k2 ). setoid_rewrite bind_trigger. reflexivity.
    rewrite Heqx, Heqy. rewrite H1, H2. setoid_rewrite interp_mrec_bind. inversion H; inj_existT; subst; pclearbot.
    + (*interp_mrec_trigger   : interp_mrec ctx (ITree.trigger a) ≳ mrecursive ctx U a *)
      unfold interp_mrec at 1. rewrite unfold_iter. cbn. setoid_rewrite bind_ret_l. rewrite bind_tau.
      fold (interp_mrec bodies1  (ITree.bind (bodies1 A0 e0) (fun x : A0 => Ret x))).
      setoid_rewrite <- interp_mrec_bind.
      unfold interp_mrec at 2. rewrite unfold_iter. cbn. rewrite bind_ret_l. setoid_rewrite bind_ret_l.
      fold (interp_mrec bodies2  (ITree.bind (bodies2 _ e3) (fun x => k2 x))). setoid_rewrite bind_ret_r.
      pstep. constructor. left. 
      assert (Hb12 : rutt (sum_relE REvInv REvE)
               (sum_relAns REvAnsInv REvAns)
               (extract REvAnsInv d1 d2) (ITree.bind (bodies1 A0 e0) k1) (ITree.bind (bodies2 B0 e3) k2)).
      { 
        eapply rutt_bind; eauto.
        intros. red in H3. eapply sum_relEAns_inl in H3. apply H0 in H3.
        pclearbot. auto.
      }
      remember (ITree.bind (bodies1 A0 e0) k1) as t1.
      remember (ITree.bind (bodies2 B0 e3) k2) as t2. clear Heqt1 Heqt2.
      generalize dependent t2. generalize dependent t1. pcofix CIH'.
      eapply rutt_mrec_interp_mrec_aux; eauto.
    + unfold interp_mrec at 1. rewrite unfold_iter. cbn. rewrite bind_vis. setoid_rewrite bind_ret_l. 
      rewrite bind_vis. setoid_rewrite unfold_iter at 1. cbn. setoid_rewrite bind_ret_l.
      setoid_rewrite bind_tau. setoid_rewrite bind_ret_l. 
      unfold interp_mrec at 2. rewrite unfold_iter. cbn. rewrite bind_vis. setoid_rewrite bind_ret_l. 
      rewrite bind_vis. setoid_rewrite unfold_iter at 2. cbn. setoid_rewrite bind_ret_l.
      setoid_rewrite bind_tau. setoid_rewrite bind_ret_l. pstep. constructor; auto.
      intros. left. pstep. constructor. left.
      assert (Hcd : sum_relAns REvAnsInv REvAns _ _ (inr1 f1) c (inr1 f2) d). econstructor. auto.
      apply H0 in Hcd. pclearbot. remember (k1 c) as kc. remember (k2 d) as kd.
      clear Heqkc Heqkd. generalize dependent kd. revert kc. pcofix CIH.
      eapply rutt_mrec_interp_mrec_aux; eauto.
  - rewrite Heqx. 
    unfold interp_mrec at 1. rewrite unfold_iter. cbn. rewrite bind_ret_l.
    fold (interp_mrec bodies1 t1). pstep. constructor. pstep_reverse. 
    assert (Htd2 : rutt (sum_relE REvInv REvE)
               (sum_relAns REvAnsInv REvAns)
               (extract REvAnsInv d1 d2) t1 (bodies2 B d2) ).
    {
      apply Hbodies in Hd12.
      assert (bodies1 A d1 ≈ t1). rewrite Heqx, tau_eutt. reflexivity. rewrite <- H. auto.
    }
    remember (bodies2 B d2) as t2. clear Heqx Heqy Heqt2 IHHbodiesd Hbodiesd. generalize dependent t2. generalize dependent t1.
    pcofix CIH. intros. eapply rutt_mrec_interp_mrec_aux; eauto.
  - rewrite Heqy. 
    unfold interp_mrec at 2. rewrite unfold_iter. cbn. rewrite bind_ret_l.
    fold (interp_mrec bodies2 t2). pstep. constructor. pstep_reverse. 
    assert (Htd2 : rutt (sum_relE REvInv REvE)
               (sum_relAns REvAnsInv REvAns)
               (extract REvAnsInv d1 d2) (bodies1 A d1) t2 ).
    {
      apply Hbodies in Hd12.
      assert (bodies2 _ d2 ≈ t2). rewrite Heqy, tau_eutt. reflexivity. rewrite <- H. auto.
    }
    remember (bodies1 _ d1) as t1. clear Heqx Heqy Heqt1 IHHbodiesd Hbodiesd. generalize dependent t2. generalize dependent t1.
    pcofix CIH. intros. eapply rutt_mrec_interp_mrec_aux; eauto.
Qed.

End MRec.

Theorem eutt_mrec (E D1 D2 : Type -> Type) 
        (REvInv : relationEH D1 D2)  (REvAnsInv : forall A B : Type, D1 A -> A -> D2 B -> B -> Prop)
        (bodies1 : D1 ~> itree (D1 +' E) ) (bodies2 : D2 ~> itree (D2 +' E) ) :
  ( forall A B (d1 : D1 A) (d2 : D2 B), REvInv A B d1 d2 -> 
                                   rutt (sum_relE REvInv EvEq) (sum_relAns REvAnsInv EvEqAns) (extract REvAnsInv d1 d2)
                                        (bodies1 A d1) (bodies2 B d2) ) ->
  forall A B (init1 : D1 A) (init2 : D2 B) , 
    REvInv A B init1 init2 -> eutt (extract REvAnsInv init1 init2)
         (mrec bodies1 init1) (mrec bodies2 init2).
Proof.
  intros.
  apply rutt_to_eutt. eapply rutt_mrec; eauto.
Qed.


Section MrecTauTest.

  Variant BoolRec : Type -> Type :=
    boolrec : BoolRec bool.

  Definition bodies1 (A : Type) (b : BoolRec A) : itree (BoolRec +' BoolRec)  A.
    destruct b. apply (Ret false).
  Defined.

  Definition bodies2 (A : Type) (b : BoolRec A) : itree (BoolRec +' BoolRec) A.
    destruct b. apply (Vis (inr1 boolrec) (fun b => Ret b)).
  Defined.
  

  Goal mrec bodies1 boolrec ≅ (Ret false).
    Proof.
      unfold mrec, interp_mrec. rewrite unfold_iter. cbn. rewrite bind_ret_l.
      reflexivity.
    Qed.

  Goal mrec bodies2 boolrec ≅ ((Vis (boolrec) (fun b => Tau (Ret b)))).
  Proof.
    setoid_rewrite unfold_iter. cbn. rewrite bind_vis.
    setoid_rewrite bind_ret_l. setoid_rewrite unfold_iter. cbn.
    setoid_rewrite bind_ret_l. reflexivity.
  Qed.

  (*
    Ret false <= Vis exists (fun b => Ret b)


    ~ Ret false <= Vis exists (fun b => Tau (Ret b)) 

    ~ Ret false <= Tau (Ret false)

   *)

  (*this demonstrates that extra taus get in which is why I need a solution to the eutt 
    problem, the thing is that it is not clear what that problem would be
    the saturated thing sounds like a good idea but I looked at the proof and don't see 
    where it helps, suggesting there may be other counter examples
   *)

End MrecTauTest.
