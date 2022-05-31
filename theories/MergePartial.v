Require Import Coq.Lists.List Coq.Sorting.Permutation.

From Coq Require Export Morphisms RelationClasses Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt Props.Divergence Props.Finite.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts Logic.Classical.
Require Import Lia.
Require Export Refinement Merge ConvergentRefinement.

Import Monads.
Import MonadNotation.
Local Open Scope monad_scope.

Open Scope list_scope.


Lemma or_spec_l E1 E2 RE REAns R1 R2 RR (t1 t2 : itree_spec E1 R1) (t3 : itree_spec E2 R2) : 
  @padded_refines E1 E2 R1 R2 RE REAns RR t1 t3 ->
  @padded_refines E1 E2 R1 R2 RE REAns RR t2 t3 ->
  @padded_refines E1 E2 R1 R2 RE REAns RR (or_spec t1 t2) t3.
Proof.
  intros. unfold or_spec. unfold padded_refines in *.
  rewrite pad_vis. pstep. constructor. intros [ | ]; constructor; pstep_reverse.
Qed.

Lemma or_spec_r E1 E2 RE REAns R1 R2 RR (t1 : itree_spec E1 R1) (t2 t3: itree_spec E2 R2) : 
  (@padded_refines E1 E2 R1 R2 RE REAns RR t1 t2 \/
  @padded_refines E1 E2 R1 R2 RE REAns RR t1 t3) ->
  @padded_refines E1 E2 R1 R2 RE REAns RR t1 (or_spec t2 t3).
Proof.
  intros. unfold or_spec. unfold padded_refines in *.
  rewrite pad_vis. pstep.
  destruct H.
  - econstructor. constructor. Unshelve. all : try (apply true). pstep_reverse.
  - econstructor. constructor. Unshelve. all : try (apply false). pstep_reverse.
Qed.

Lemma spin_bind E R S k :  (@ITree.spin E R) >>= k ≅ @ITree.spin E S.
Proof.
  ginit. gcofix CIH. gstep. red. cbn. constructor.
  gfinal. eauto.
Qed.

Lemma and_or_spec E R (t1 t2 : itree_spec E R) : 
  padded_refines_eq eq (and_spec t1 t2) (or_spec t1 t2).
Proof.
  unfold and_spec, or_spec, padded_refines_eq, padded_refines.
  setoid_rewrite pad_vis. pstep. red. cbn. econstructor. constructor.
  Unshelve. all : try apply true. econstructor. cbn. constructor.
  Unshelve. all : try apply true. pstep_reverse. 
  enough (padded_refines_eq eq t1 t1). auto. reflexivity.
Qed.

Fixpoint trepeat {E R} (n : nat) (t : itree E R) : itree E unit :=
  match n with
  | 0 => Ret tt
  | S m => t;; trepeat m t end.

Lemma trepeat_Sn E R (n : nat) (t : itree E R) :
  trepeat (S n) t ≅ t;; trepeat n t.
Proof.
  apply eqit_bind; reflexivity.
Qed.

Lemma trepeat_0 E R (t : itree E R) : 
  trepeat 0 t ≅ Ret tt.
Proof. reflexivity. Qed.

Definition halve_spec_fix {E} : list nat -> itree_spec E (list nat * list nat) :=
  rec_fix_spec (fun halve_spec_rec l =>
                  n <- spec_exists nat;;
                  trepeat n ( l' <- spec_exists (list nat);; halve_spec_rec l' );;
                  halve_spec l
               ).


Theorem padded_refines_ret E1 E2 R1 R2 RE REAns RR r1 r2 :
  (RR r1 r2 : Prop) ->
  @padded_refines E1 E2 R1 R2 RE REAns RR (Ret r1) (Ret r2).
Proof.
  intros Hr. red. repeat rewrite pad_ret. pstep. constructor. auto.
Qed.

Theorem padded_refines_vis E1 E2 R1 R2 A B 
        RE REAns RR (e1 : E1 A) (e2 : E2 B)
        (k1 : A -> itree_spec E1 R1) (k2 : B -> itree_spec E2 R2) : 
  (RE A B e1 e2 : Prop) -> 
  (forall a b, (REAns A B e1 e2 a b : Prop) -> padded_refines RE REAns RR (k1 a) (k2 b) ) ->
  padded_refines RE REAns RR (Vis (Spec_vis e1) k1) (Vis (Spec_vis e2) k2).
Proof.
  unfold padded_refines. setoid_rewrite pad_vis. intros.
  pstep. constructor; auto. intros. left. pstep. constructor.
  left. eapply H0; auto.
Qed.

Variant halve_call : forall A, callE (list nat) (list nat * list nat) A -> A -> Prop :=
  | halve_call_i (l l1 l2: list nat) : 
    Permutation l (l1 ++ l2) ->
    (length l1 >= length l2 /\ (length l > length l1 \/ length l <= 1)) ->
    halve_call _ (Call l) (l1,l2).

Lemma halve_correct' E l : padded_refines_eq eq (@halve E l) (halve_spec_fix l).
Proof.
  eapply padded_refines_monot with (RE1 := eqE) 
                                   (REAns1 := eqEAns) 
                                   (RR1 := sub_eqEAns halve_call _ _ (Call l) (Call l) ); eauto.
  { intros [l1 l2] [l3 l4]. intros. inv PR. inj_existT. subst. auto. }
  eapply padded_refines_mrec with (REInv := eqE) 
                                  (* in this post condition need to include *)
                                  (REAnsInv := sub_eqEAns halve_call).
  2 : constructor. intros.
  eqE_inv H. clear l. destruct d2 as [l]. cbn.
  destruct l as [ | a [ | b l] ].
  - existssr 0. rewrite trepeat_0. rewrite bind_ret_l.
    existssr (@nil nat). existssr (@nil nat). assertsr. reflexivity.
    assertsr. cbn. lia.
    apply padded_refines_ret. do 2 constructor. reflexivity.
    cbn. lia. (*note reflexivity is not enough this is a subreflexive rel*)
  - existssr 0. rewrite trepeat_0. rewrite bind_ret_l.
    existssr (a :: nil). existssr (@nil nat). assertsr. reflexivity.
    assertsr. cbn. lia. apply padded_refines_ret. do 2 constructor.
    reflexivity. cbn. lia.
  - cbn. existssr 1. rewrite trepeat_Sn. setoid_rewrite trepeat_0.
    cbn. repeat rewrite bind_bind. existssr l.
    eapply padded_refines_bind with (RR :=
                                    sub_eqEAns halve_call (list nat * list nat) (list nat * list nat) (Call (l)) (Call (l))).
    + unfold call_spec. apply padded_refines_vis. repeat constructor.
      intros [l1 l2] r Hl12. inv Hl12. inj_existT. subst.
      inv H5. inj_existT. subst. apply padded_refines_ret.
      constructor. auto.
    + intros [l1 l2] r2 Heq. inv Heq. inj_existT. subst.
      inv H4. inj_existT. injection H5. intros. subst. 
      rewrite bind_ret_l.
      existssr (a :: l1). existssr (b :: l2). assertsr. 
      { cbn. rewrite Permutation_app_comm. cbn.
      rewrite H0. rewrite Permutation_app_comm. reflexivity. }
      assertsr.
      { cbn. rewrite H0. repeat rewrite app_length. lia. }
      apply padded_refines_ret. do 2 constructor.
      { cbn. rewrite Permutation_app_comm. cbn.
      rewrite H0. rewrite Permutation_app_comm. reflexivity. }
      cbn. repeat rewrite H0. repeat rewrite app_length. lia.
Qed.
(*
Section ConvRef.
Context (E D : Type -> Type).
Context (Pre : forall A, D A -> Prop).
Context (bodies : D ~> itree_spec (D +' E) ).
Context (A : Type) (init : D A) (Hinit : Pre A init).
Context (Hconv : forall A (d : D A), Pre A d -> )



Context {A B: Type} {E : Type -> Type}.
Context (body : ((A -> itree_spec (callE A B +' E) B) -> A -> itree_spec (callE A B +' E) B)).
Context (Inv : A -> Prop).

Lemma rec_fix_conv_rev : 
  (* (forall a, Inv a -> conv_ref (body a) ) -> *)
  forall a, Inv a -> conv_ref (rec_fix_spec body a).


End ConvRef. *)

Global Instance padded_refines_eq_itree E1 E2 R1 R2 RE REAns RR
  : Proper (eq_itree eq ==> eq_itree eq ==> impl) 
           (@padded_refines E1 E2 R1 R2 RE REAns RR).
Proof.
  repeat intro. assert (x ≈ y). rewrite H. reflexivity.
  rewrite <- H2. assert (x0 ≈ y0). rewrite H0. reflexivity.
  rewrite <- H3. auto.
Qed.

Lemma interp_mrec_spec_or  (E : Type -> Type) (R : Type) (D : Type -> Type) (ctx : forall T : Type, D T -> itree_spec (D +' E) T) 
  (t1 t2 : itree_spec _ R)
  : interp_mrec_spec ctx (or_spec t1 t2) ≅ or_spec (interp_mrec_spec ctx t1) (interp_mrec_spec ctx t2).
Proof.
  setoid_rewrite interp_mrec_spec'_exists. apply eqit_Vis. intros [ | ]; reflexivity.
Qed.

Lemma interp_mrec_spec_spin (E : Type -> Type) (R : Type) (D : Type -> Type) (ctx : forall T : Type, D T -> itree_spec (D +' E) T) :
  interp_mrec_spec ctx ITree.spin ≅ @ITree.spin _ R.
Proof.
  pcofix CIH. pstep. red. cbn. constructor.
  right. eauto.
Qed.

Lemma conv_ref_mrec_spin (E D : Type -> Type) (R : Type) (P : forall A : Type, D A -> Prop) : 
  @conv_ref_mrec E D R P ITree.spin.
Proof.
  pcofix CIH. pstep. red. cbn. constructor.
  eauto.
Qed.

Lemma conv_ref_mrec_ex (E D : Type -> Type) (R A : Type) (P : forall A : Type, D A -> Prop) k : 
  (forall a, conv_ref_mrec P (k a)) ->
  @conv_ref_mrec E D R P (Vis (@Spec_exists _ A) k ).
Proof.
  intros. pstep. constructor. left. apply H.
Qed.

(*should be able to generalize this to cany concrete tree *)
Lemma or_spec_r_Ret_inv E1 E2 R1 R2 RE REAns RR r t2 t3 :
  @padded_refines E1 E2 R1 R2 RE REAns RR (Ret r) (or_spec t2 t3) ->
  padded_refines RE REAns RR (Ret r) t2 \/ padded_refines RE REAns RR (Ret r) t3.
Proof.
  intros Hor. unfold padded_refines in *. setoid_rewrite pad_ret in Hor.
  setoid_rewrite pad_ret. setoid_rewrite pad_vis in Hor.
  pinversion Hor. inj_existT. subst. inv H1. destruct a.
  - left. pstep. auto.
  - right. pstep. auto.
Qed.

Section SpecFix.
  Context {A B: Type} {E : Type -> Type}.
  Context (Pre : A -> Prop) (Post : A -> B -> Prop).
  Context (prog : A -> itree_spec E B).

  Context (Hprog : forall a, (exists b, prog a ≈ Ret b) \/ prog a ≈ ITree.spin).

  Definition total_spec (a : A) : itree_spec E B :=
    assume_spec (Pre a);;
    b <- spec_exists B;;
    assert_spec (Post a b);;
    Ret b.

  (* better for using as a final spec *)
  Definition partial_spec (a : A) : itree_spec E B :=
    or_spec (total_spec a) ITree.spin.
  (* better for syntax driven solving *)
  (**)

  Definition partial_spec_fix : A -> itree_spec E B :=
    rec_fix_spec (fun rec a => 
                    assume_spec (Pre a);;
                    (
                      n <- spec_exists nat;;
                      trepeat n (a' <- spec_exists A;; assert_spec (Pre a');; rec a' )
                    );;
                    b <- spec_exists B;;
                    assert_spec (Post a b);;
                    Ret b
                 ).

  Definition partial_spec_fix' : A -> itree_spec E B :=
    rec_fix_spec (fun rec a => 
                        assume_spec (Pre a);;
                        (
                          n <- spec_exists nat;;
                          trepeat n (a' <- spec_exists A;; assert_spec (Pre a');; rec a' )
                        );;
                        or_spec (
                            b <- spec_exists B;;
                            assert_spec (Post a b);;
                            Ret b)
                        ITree.spin
                 ).



  Lemma partial_spec_fix_partial_spec_assume_succeed':
    forall (a : A) (b : B),
      Pre a ->
      padded_refines_eq eq (Ret b) (partial_spec_fix' a) ->
      padded_refines_eq eq (Ret b) (partial_spec a).
  Proof.
    intros a b Ha Hfix. unfold partial_spec_fix' in Hfix. cbn in Hfix.
    repeat setoid_rewrite interp_mrec_spec_or in Hfix.

    (*need an inversion principle for or spec *)
    (*could use rewrite for interp_mrec_spec and or_spec *)
    do 2 setoid_rewrite interp_mrec_spec_bind in Hfix. revert Hfix.
    match goal with | |- context [ interp_mrec_spec ?f _ ] => set f as body end.
    intro Hfix. 
    assert (
        padded_refines_eq eq (interp_mrec_spec body (or_spec (b <- spec_exists B;; _ <- assert_spec (Post a b);; Ret b) ITree.spin)) (partial_spec a)).
    {
      rewrite interp_mrec_spec_or. unfold partial_spec.
      apply or_spec_l.
      - apply or_spec_r. left. unfold total_spec.
        assumesr. intros. repeat setoid_rewrite interp_mrec_spec_bind. 
        normalize_interp_mrec_spec. setoid_rewrite interp_mrec_spec_ret.
        setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
        eapply padded_refines_bind. reflexivity.
        intros. subst. eapply padded_refines_bind. reflexivity.
        intros. subst. reflexivity.
      - apply or_spec_r. right. rewrite interp_mrec_spec_spin. reflexivity.
    } setoid_rewrite H in Hfix.
    setoid_rewrite interp_mrec_spec_ret in Hfix.
    match type of Hfix with padded_refines_eq eq _ ?t => set t as t1 end.
    fold t1 in Hfix.
    
    assert (t1 ≈ (interp_mrec_spec body (trigger (@Spec_forall _ (Pre a) ) ) >>
                 Ret tt >> 
                  (interp_mrec_spec body
           (ITree.bind (spec_exists nat)
              (fun n : nat => trepeat n (ITree.bind (spec_exists A) (fun a' : A => 
                       trigger (@Spec_exists _ (Pre a') ) >> Ret tt >> call_spec a'))))) >> partial_spec a)
                 ).
    {
      unfold t1. repeat rewrite bind_bind.
      apply eqit_bind. reflexivity. intro.
      reflexivity.
    }
    rewrite H0 in Hfix. clear H0. 
    (*might have dropped an important assumption *)
    eapply padded_conv_ref_ret_bind; eauto.
    normalize_interp_mrec_spec. cbn.
    apply conv_ref_bind.
    { pstep. red. cbn. constructor; auto. intros a0.
          left. pstep. red. cbn. constructor. }
    intros _.  setoid_rewrite bind_ret_l.
    eapply conv_ref_interp_mrec_conv_ref.
    Unshelve. 3 : { intros C c. destruct c. apply (Pre a0). }
    - cbn.
      intros. destruct d. cbn.
      clear - H0 Ha. setoid_rewrite bind_bind. 
      apply conv_ref_mrec_bind.
      { pstep. red. cbn. constructor. auto. left.
        pstep. constructor. }
      intros _. rewrite bind_ret_l.
      repeat rewrite bind_bind. unfold or_spec. setoid_rewrite bind_vis.
      apply conv_ref_mrec_ex. intros n.
      rewrite bind_ret_l.
      eapply conv_ref_mrec_bind.
      + induction n. cbn. pstep. constructor.
        cbn. apply conv_ref_mrec_bind; intros; eauto.
        apply conv_ref_mrec_bind. apply conv_ref_mrec_ex.
        intros. pstep. constructor. intros.
        rewrite bind_bind.
        setoid_rewrite bind_vis.
        apply conv_ref_mrec_ex. intros Hr.
        repeat rewrite bind_ret_l. apply conv_ref_mrec_inl.
        auto. intros. pstep. constructor.
      + intros []. apply conv_ref_mrec_ex.
        intros [ | ]; try apply conv_ref_mrec_spin.
        setoid_rewrite bind_vis. apply conv_ref_mrec_ex.
        intros. setoid_rewrite bind_ret_l. rewrite bind_bind. setoid_rewrite bind_vis.
        apply conv_ref_mrec_ex. intros.
        repeat rewrite bind_ret_l. pstep. constructor.
    - setoid_rewrite bind_vis. setoid_rewrite bind_ret_l.
      apply conv_ref_mrec_exists. intros n. clear - n Ha.
      induction n. cbn. pstep. constructor.
      cbn. eapply conv_ref_mrec_bind; eauto.
      setoid_rewrite bind_bind. setoid_rewrite bind_ret_l. 
      setoid_rewrite bind_vis.
      apply conv_ref_mrec_exists. intros a0. rewrite bind_ret_l.
      setoid_rewrite bind_vis. apply conv_ref_mrec_exists. intros Ha0.
      rewrite bind_ret_l. apply conv_ref_mrec_inl. auto. intros. pstep. constructor.
  Qed.

  Lemma partial_spec_fix_partial_spec_assume_fail a :
    ~ Pre a -> padded_refines_eq eq (prog a) (partial_spec a).
  Proof.
    intros HPre. apply or_spec_r.
    left. assumesr. intros. contradiction.
  Qed.

  Lemma partial_spec_fix_partial_spec_assume_succeed:
    forall (a : A) (b : B),
      padded_refines_eq eq (Ret b) (partial_spec_fix a) ->
      padded_refines_eq eq (Ret b) (partial_spec a).
  Proof.
    intros a b Hfix. 
    apply or_spec_r. left. unfold total_spec.
    assumesr. intros Ha.
    unfold partial_spec_fix in Hfix.
    do 2 setoid_rewrite interp_mrec_spec_bind in Hfix. revert Hfix.
    match goal with | |- context [ interp_mrec_spec ?f _ ] => set f as body end.
    intro Hfix. 
    assert (interp_mrec_spec body (b <- spec_exists B;; _ <- assert_spec (Post a b);; Ret b) ≈ 
                             (b <- spec_exists B;; _ <- assert_spec (Post a b);; Ret b)).
    {
      repeat setoid_rewrite interp_mrec_spec_bind.
      normalize_interp_mrec_spec.
      setoid_rewrite interp_mrec_spec_ret. cbn. reflexivity.
    } setoid_rewrite H in Hfix.
    (* need to manage diff between padded_refines and refines *)
    cbn in Hfix. setoid_rewrite <- bind_bind in Hfix.
    eapply padded_conv_ref_ret_bind; eauto.
    setoid_rewrite interp_mrec_spec_ret. 
    apply conv_ref_bind.
    { pstep. red. cbn. constructor; auto. intros a0.
          left. pstep. red. cbn. constructor. }
    intros _. 
    eapply conv_ref_interp_mrec_conv_ref.
    Unshelve. 3 : { intros C c. destruct c. apply (Pre a0). }
    - cbn.
      intros. destruct d. cbn.
      clear - H0 Ha. 
      repeat rewrite bind_bind. setoid_rewrite bind_ret_l.
      apply conv_ref_mrec_bind.
      apply conv_ref_mrec_forall. auto. intros. pstep. constructor.
      intros. rewrite <- bind_bind.
      apply conv_ref_mrec_bind.
      + rewrite bind_bind. apply conv_ref_mrec_bind. 
        apply conv_ref_mrec_exists. intros. pstep. constructor.
        intros n.
        induction n; cbn. rewrite bind_ret_l. apply conv_ref_mrec_exists.
        intros. pstep. constructor. rewrite bind_bind.
        eapply conv_ref_mrec_bind; intros; eauto.
        setoid_rewrite bind_vis. apply conv_ref_mrec_exists.
        intros. setoid_rewrite bind_ret_l. rewrite bind_bind. setoid_rewrite bind_vis.
        apply conv_ref_mrec_exists. intros. repeat rewrite bind_ret_l.
        apply conv_ref_mrec_inl. auto. intros. pstep. constructor.
      + intros b. rewrite bind_bind. setoid_rewrite bind_vis.
        apply conv_ref_mrec_exists. intros HPost. repeat rewrite bind_ret_l.
        pstep. constructor.
    - setoid_rewrite bind_vis. setoid_rewrite bind_ret_l.
      apply conv_ref_mrec_exists. intros n. clear - n Ha.
      induction n. cbn. pstep. constructor.
      cbn. eapply conv_ref_mrec_bind; eauto.
      setoid_rewrite bind_bind. setoid_rewrite bind_ret_l. 
      setoid_rewrite bind_vis.
      apply conv_ref_mrec_exists. intros a0. rewrite bind_ret_l.
      setoid_rewrite bind_vis. apply conv_ref_mrec_exists. intros Ha0.
      rewrite bind_ret_l. apply conv_ref_mrec_inl. auto. intros. pstep. constructor.
  Qed.


  Lemma partial_spec_fix_partial_spec a :
    (Pre a -> padded_refines_eq eq (prog a) (partial_spec_fix a)) ->
    padded_refines_eq eq (prog a) (partial_spec a).
  Proof.
    intros Hfix.
    destruct (Hprog a) as [ [b Hb] | Hspin].
    - destruct (classic (Pre a) ) as [Ha | Ha]; auto.
      + rewrite Hb. rewrite Hb in Hfix. 
        apply partial_spec_fix_partial_spec_assume_succeed; auto.
      + apply or_spec_r. left. assumesr. intros. contradiction.
    - rewrite Hspin. apply or_spec_r. right. reflexivity.
  Qed.

  Lemma partial_spec_fix_partial_spec' a :
    (Pre a -> padded_refines_eq eq (prog a) (partial_spec_fix' a)) ->
    padded_refines_eq eq (prog a) (partial_spec a).
  Proof.
    intros Hfix.
    destruct (Hprog a) as [ [b Hb] | Hspin].
    - destruct (classic (Pre a) ) as [Ha | Ha]; auto.
      + rewrite Hb. rewrite Hb in Hfix. 
        apply partial_spec_fix_partial_spec_assume_succeed'; auto.
      + apply or_spec_r. left. assumesr. intros. contradiction.
    - rewrite Hspin. apply or_spec_r. right. reflexivity.
  Qed.   

  Variant pre_call : forall C, callE A B C -> Prop :=
    | pre_call_intro (a : A) : Pre a -> pre_call B (Call a).
  Variant post_call : forall C, callE A B C -> C -> Prop :=
    | post_call_intro a b : Post a b -> post_call B (Call a) b.

  (*
  (* TODO : restructure this section so something like this can work *)
  Lemma partial_spec_fix_partial_spec_inv a :
    padded_refines (sub_eqE pre_call) (sub_eqEAns post_call) (sub_eq (Post a) ) 
                   (prog a) (partial_spec_fix a).
  *)
  (* should work as long as Pre is inhabitted that allows *)
  Lemma partial_spec_fix_spin a :
    padded_refines_eq eq ITree.spin (partial_spec_fix a).
  Proof.
    unfold partial_spec_fix. setoid_rewrite interp_mrec_spec_bind.
    setoid_rewrite interp_mrec_spec_assume. assumesr.
    intros Ha. cbn. rewrite <-  bind_bind.
    match goal with | |- padded_refines _ _ _ _ (interp_mrec_spec _ ( ITree.bind ?t1 ?t2) ) =>
                        remember t2 as t end.
    clear Heqt. generalize dependent t.
    (* this seems like a good coind hyp*)
    (* better solution might be to create a divergent refinement,
       showing that there is a path that you can keep getting taus in 
       then give that some kind of mrec rule
     *)
    pcofix CIH.
  Admitted.

  Lemma partial_spec_fix_spin' a :
    padded_refines_eq eq ITree.spin (partial_spec_fix' a).
  Proof.
    unfold partial_spec_fix'. setoid_rewrite interp_mrec_spec_bind.
    repeat normalize_interp_mrec_spec. assumesr. intros.
    setoid_rewrite interp_mrec_spec_bind. 
    setoid_rewrite interp_mrec_spec_bind.
    normalize_interp_mrec_spec. 
    match goal with |- context [ interp_mrec_spec ?body_ _  ] => set body_ as body end.
    setoid_rewrite interp_mrec_spec_exists. existssr 0. cbn.
    rewrite interp_mrec_spec_ret, bind_ret_l. rewrite interp_mrec_spec_or.
    apply or_spec_r. right. rewrite interp_mrec_spec_spin. reflexivity.
  Qed.


End SpecFix.

Opaque assume_spec.
Opaque assert_spec.
Opaque spec_forall.
Opaque spec_exists.

Lemma halve_spec_fix_correct' E l : 
  padded_refines_eq eq (@halve E l) (partial_spec_fix (fun _ => True) 
                                                   (fun l '(l1,l2) => Permutation l (l1 ++ l2) /\ 
                               (length l1 >= length l2 /\ (length l > length l1 \/ length l <= 1)) ) l ).
Proof.
  eapply padded_refines_monot with (RE1 := eqE) 
                                   (REAns1 := eqEAns) 
                                   (RR1 := sub_eqEAns halve_call _ _ (Call l) (Call l) ); eauto.
  { intros [l1 l2] [l3 l4]. intros. inv PR. inj_existT. subst. auto. }
    eapply padded_refines_mrec with (REInv := eqE) 
                                  (* in this post condition need to include *)
                                  (REAnsInv := sub_eqEAns halve_call).
  2 : constructor. intros.
  eqE_inv H. clear l. destruct d2 as [l]. cbn.
  destruct l as [ | a [ | b l] ].
  - assumesr. intros _. rewrite bind_bind. existssr 0.
    cbn. rewrite bind_ret_l. existssr (@nil nat,@nil nat).
    assertsr. split. reflexivity. lia.
    apply padded_refines_ret. do 2 constructor. reflexivity. cbn. lia.
  - assumesr. intros _. rewrite bind_bind. existssr 0.
    cbn. rewrite bind_ret_l. existssr (a :: nil, @nil nat).
    assertsr. split. reflexivity. cbn. lia.
    apply padded_refines_ret. do 2 constructor. reflexivity. cbn. lia.
  - assumesr. intros _. rewrite bind_bind. existssr 1.
    cbn. repeat rewrite bind_bind. existssr l.
    repeat rewrite bind_bind.
    assertsr. auto. setoid_rewrite bind_ret_l.
    eapply padded_refines_bind with  (RR :=
                                    sub_eqEAns halve_call (list nat * list nat) (list nat * list nat) (Call (l)) (Call (l))).
    { apply padded_refines_vis. constructor. constructor. intros [l1 l2] b0 Hl12.
      inv Hl12. inj_existT. subst. inv H5. inj_existT. subst.
      apply padded_refines_ret. constructor. auto. }
    intros [l1 l2] r Hl12. inv Hl12. inj_existT. subst. inv H4. inj_existT.
    injection H5; intros; subst. existssr (a :: l1,b :: l2). assertsr.
    split.
    { cbn. rewrite Permutation_app_comm. cbn.
      rewrite H0. rewrite Permutation_app_comm. reflexivity. }
    { cbn. repeat rewrite H0. repeat rewrite app_length. lia. }
    apply padded_refines_ret. constructor. constructor.
    { cbn. rewrite Permutation_app_comm. cbn.
      rewrite H0. rewrite Permutation_app_comm. reflexivity. }
    { cbn. repeat rewrite H0. repeat rewrite app_length. lia. }
 Qed.
(* this requires lem *)
Lemma halve_ret_spin E l : (exists l', @halve E l ≈ Ret l') \/ (@halve E l ≈ ITree.spin).
Admitted.


(* ok so there is a bunch of small things I still need to do but I think I have solved the problem *)
Theorem halve_correct'' E l : padded_refines_eq eq (@halve E l) (partial_spec (fun _ => True) 
                                                   (fun l '(l1,l2) => Permutation l (l1 ++ l2) /\ 
                               (length l1 >= length l2 /\ (length l > length l1 \/ length l <= 1)) ) l).
Proof.
  eapply  partial_spec_fix_partial_spec. intros. apply halve_ret_spin.
  intros _.
  apply halve_spec_fix_correct'.
Qed.

Lemma sub_eqE_eq_type E P A B (ea : E A) (eb : E B) : sub_eqE P A B ea eb -> A = B.
Proof.
  intros. inv H. auto.
Qed.

Lemma sub_eqE_eq E P A (e1 : E A) (e2 : E A) : sub_eqE P A A e1 e2 -> e1 = e2 /\ P A e1.
Proof.
  intros. inv H. inj_existT. subst. auto.
Qed.

Lemma sub_eqEAns_eq_type E P A B (ea : E A) (eb : E B) a b : sub_eqEAns P A B ea eb a b -> A = B.
Proof.
  intros. inv H. auto.
Qed.

Lemma sub_eqEAns_eq E P A (e1 : E A) (e2 : E A) a1 a2 : sub_eqEAns P A A e1 e2 a1 a2 -> e1 = e2 /\ a1 = a2 
                                                                                 /\ P A e1 a1.
Proof.
  intros. inv H. inj_existT. subst. auto.
Qed.

Ltac sub_eqE_inv H := eapply sub_eqE_eq_type in H as ?H; subst; eapply sub_eqE_eq in H as [?H ?H] ; subst.
Ltac sub_eqEAns_inv H := apply sub_eqEAns_eq_type in H as ?H; subst; apply sub_eqEAns_eq in H as [?H [?H ?H] ]; subst.

Section merge_correct.
  Definition merge_pre '(l1,l2) := sorted l1 /\ sorted l2.
  Definition merge_post '(l1,l2) l := sorted l /\ Permutation l (l1 ++ l2).

  Theorem merge_correct'' E l1 l2 : padded_refines_eq eq (@Merge.merge E (l1,l2)) 
                                                  (partial_spec merge_pre merge_post (l1,l2)).
  Proof.
    eapply partial_spec_fix_partial_spec. admit. (* proof that merge has no event *)
    (* I should be able to assume here that Pre holds, because if it does not,
       then I can easily *)
    intros Hl12.
    eapply padded_refines_monot with (RE1 := eqE ) 
                                   (REAns1 := eqEAns) 
                                   (RR1 := sub_eqEAns (post_call (merge_post) ) _ _ 
                                                      (Call (l1,l2)) (Call (l1,l2)) ); eauto.
    { intros. inv PR. inj_existT. subst. auto. }
    eapply padded_refines_mrec with (REInv := sub_eqE (pre_call merge_pre) )
                                    (REAnsInv := sub_eqEAns (post_call (merge_post) ) ).
    2 : { do 2 constructor. auto. } 
    intros. sub_eqE_inv H.
    clear Hl12 l1 l2. destruct d2 as [ [ l1 l2] ]. inv H0. destruct H1 as [Hl1 Hl2].
    cbn.
    destruct l1; destruct l2.
    - assumesr. intros _. repeat rewrite bind_bind. existssr (0). setoid_rewrite bind_ret_l.
      existssr (@nil nat). assertsr. split; auto. apply padded_refines_ret.
      repeat constructor.
    - assumesr. intros _. repeat rewrite bind_bind. existssr 0. setoid_rewrite bind_ret_l.
      existssr (n :: l2). assertsr. auto.  apply padded_refines_ret.
      do 2 constructor. split; auto.
    - assumesr. intros _. repeat rewrite bind_bind. existssr 0. setoid_rewrite bind_ret_l.
      existssr (n :: l1). assertsr. split; auto. rewrite app_nil_r. auto. apply padded_refines_ret.
      do 2 constructor. split. auto. rewrite app_nil_r. auto.
    - rename n0 into m. destruct (Nat.leb n m) eqn : Hnm.
      + cbn. assumesr. intros _. repeat rewrite bind_bind. existssr 1.
        cbn. repeat rewrite bind_bind. existssr (l1, m :: l2). setoid_rewrite bind_bind. assertsr.
        split; auto. eapply sorted_tail. eauto. apply padded_refines_bind with (RR := sub_eq (merge_post (l1, m :: l2) ) ).
        { apply padded_refines_vis. do 3 constructor. split; auto. eapply sorted_tail. eauto.
          intros. inv H. inj_existT. subst. sub_eqEAns_inv  H6.
          inv H2. inj_existT. subst. apply padded_refines_ret. constructor. auto.
        }
        intros ? lm Hlm. inv Hlm. setoid_rewrite bind_ret_l. existssr (n :: lm).
        assertsr.
        { destruct H. split.
          - admit. (*fact about sorted list *)
          - rewrite H0. reflexivity. 
        }
        apply padded_refines_ret. destruct H. do 3 constructor.
        * admit.
        * setoid_rewrite H0. reflexivity.
      + cbn. assumesr. intros _. repeat rewrite bind_bind. existssr 1.
        cbn. repeat rewrite bind_bind. existssr (n :: l1, l2). setoid_rewrite bind_bind. assertsr.
        split; auto. eapply sorted_tail. eauto. apply padded_refines_bind with (RR := sub_eq (merge_post (n :: l1,  l2) ) ).
        { apply padded_refines_vis. do 3 constructor. split; auto. eapply sorted_tail. eauto.
          intros. inv H. inj_existT. subst. sub_eqEAns_inv  H6.
          inv H2. inj_existT. subst. apply padded_refines_ret. constructor. auto.
        }
        intros ? lm Hlm. inv Hlm. setoid_rewrite bind_ret_l. existssr (m :: lm).
        assertsr.
        { destruct H. split.
          - admit. (*fact about sorted list *)
          - rewrite H0. cbn. rewrite (Permutation_app_comm (l1) (m :: l2) ) .  cbn. rewrite Permutation_app_comm.
            constructor.
        }
        apply padded_refines_ret. destruct H. do 3 constructor.
        * admit.
        * rewrite H0. cbn. rewrite (Permutation_app_comm (l1) (m :: l2) ) .  cbn. rewrite Permutation_app_comm.
          constructor.
 Admitted.

End merge_correct.

(* this should be contravariant, you can weaken the first and strengthen the second *)


(*
Instance test_le2 n : Proper (le ==> flip impl) (fun m => le m n).
Proof.
  repeat intro. subst. lia.
Qed.
                           
Instance test_le1 : Proper (le ==> (flip le) ==> flip impl) le.
Proof.
  repeat intro. red in H0. lia.
Qed.

Instance test_le1' : Proper (le ==> (flip le) ==> impl) (flip le).
Proof.
  repeat intro. red in H0. red. red in H1. lia.
Qed. *)
(*
Instance le_trans : Transitive le.
Proof.
  repeat intro. lia.
Qed.

Goal 1 <= 2 -> 2 <= 3 -> 1 <= 3.
*)

Global Instance padded_refines_sub_eq E R (RR : R -> R -> Prop) (P1 : forall A, E A -> Prop) (P2 : forall A, E A -> A -> Prop) :
  Transitive RR ->
  Transitive (padded_refines (sub_eqE P1) (sub_eqEAns P2) RR ).
Proof.
  intros HRR t1 t2 t3 Ht12 Ht23. unfold padded_refines in *.
  eapply refines_monot; try eapply refinesTrans; eauto with solve_padded; try apply pad_is_padded.
  - intros A B ea eb PR. inv PR. inj_existT. subst. sub_eqE_inv H3. auto.
  - intros. sub_eqEAns_inv  PR. constructor. intros. destruct H. sub_eqE_inv H. 
    exists x1. split; constructor; auto.
  - intros. inv PR. etransitivity; eauto.
Qed.

Global Instance sub_eqEAns_trans E (P : forall A, E A -> A -> Prop) A (e : E A) : Transitive (sub_eqEAns P A A e e).
Proof.
  intros x y z Hxy Hyz. sub_eqEAns_inv Hxy. auto.
Qed.

(* I think I can save the rest for tomorrow*)

(*
Global Instance refines_proper_bind_RE E R RE REAns S :
  Proper (@padded_refines E  R R eq ==> pointwise_relation _ (padded_refines_eq eq) ==> @padded_refines_eq E S S  eq ) ITree.bind.
Proof.
  repeat intro. subst. unfold padded_refines_eq in *. eapply padded_refines_bind; eauto.
  intros; subst. auto.
Qed.
*)

(*do I need the proper instances? Probably *)

Global Instance  padded_refines_eq_gen E1 E2 R1 R2 RE REAns RR : Proper (padded_refines_eq eq ==> flip (padded_refines_eq eq) ==> flip impl )
                                                                (@padded_refines E1 E2 R1 R2 RE REAns RR).
Proof.
  intros t1 t2 Ht12 t3 t4 Ht43. red in Ht43. intro.
  unfold padded_refines_eq, padded_refines in *. rename H into H24.
  specialize @refinesTrans with (E1 := E1) (E2 := E1) (E3 := E2) (RE1 := eqE) (RE2 := RE) as Htrans.
  eapply Htrans in Ht12; eauto; try apply pad_is_padded. clear Htrans.
  specialize @refinesTrans with (E1 := E1) (E2 := E2) (E3 := E2) (RE1 := rcomposeE eqE RE) (RE2 := eqE) as Htrans.
  eapply Htrans in Ht12; eauto; try apply pad_is_padded. eapply refines_monot; try eapply Ht12.
  { intros. destruct PR. destruct H. eqE_inv H. eqE_inv H0. auto. }
  { intros. econstructor. intros. destruct H. eqE_inv H0. 
    inv H. inj_existT. subst. eqE_inv H4. exists x1. split. 2 : constructor.
    constructor. intros. destruct H. eqE_inv H. exists x0. split; auto. constructor.
  }
  { intros. inv PR. inv REL1. auto. }
Qed.
  (* this is maybe a tad more subtle then I realized, does it require transitivity?,
     that would not be problematic for these relations because there seem to be PER's

   *)

Lemma or_spec_bind_l  E1 E2 R1 S R2 RE REAns RR (t1 t2 : itree_spec E1 S) (k : S -> itree_spec E1 R1) (t3 : itree_spec E2 R2) : 
  padded_refines RE REAns RR (ITree.bind t1 k) t3 ->
  padded_refines RE REAns RR (ITree.bind t2 k) t3 ->
  padded_refines RE REAns RR (ITree.bind (or_spec t1 t2) k) t3.
Proof.
  unfold padded_refines. intros. setoid_rewrite bind_vis. setoid_rewrite pad_vis.
  pstep. constructor. intros [ | ]; constructor; pstep_reverse.
Qed.

Section sort_correct.
  Definition sort_pre (l : list nat) := True.
  Definition sort_post (l l' : list nat) := Permutation l l' /\ sorted l'.

  Theorem sort_correct' E l : padded_refines_eq eq (@sort E l) (partial_spec sort_pre sort_post l).
  Proof.
    eapply partial_spec_fix_partial_spec'. admit.
    intros _.
    eapply padded_refines_monot with (RE1 := eqE ) 
                                   (REAns1 := eqEAns) 
                                   (RR1 := sub_eqEAns (post_call (sort_post) ) _ _ 
                                                      (Call (l)) (Call (l)) ); eauto.
    { intros. sub_eqEAns_inv  PR. auto. }
    eapply padded_refines_mrec with (REInv := sub_eqE (pre_call sort_pre) )
                                    (REAnsInv := sub_eqEAns (post_call (sort_post) ) ).
    2 : { repeat constructor. }
    intros. clear l. sub_eqE_inv  H. destruct d2. inv H0.
    cbn. destruct (Nat.leb (length l) 1 ) eqn : Hlen.
    - assumesr. intros _. repeat rewrite bind_bind. existssr 0.
      cbn. rewrite bind_ret_l. apply or_spec_r. left.
      existssr l. 
      assert (sort_post l l).
      { destruct l. split; auto. constructor. destruct l. split; auto.
        constructor. discriminate. }
      assertsr. auto. apply padded_refines_ret. do 2 constructor. auto.
    - rewrite halve_correct''. 
      (* here I really want to push the or_spec left, probably only works if only quantifiers,
         if I can get past this then it should work *)

      unfold partial_spec, total_spec. rewrite or_spec_bind.
      apply or_spec_l.
      2 : { setoid_rewrite spin_bind. 
            assumesr. intros _ . repeat rewrite bind_bind. existssr 0.
            cbn. rewrite bind_ret_l. apply or_spec_r. right.
            apply padded_refines_spin.
          }
      setoid_rewrite bind_bind at 1. assumesl. auto.  setoid_rewrite bind_bind at 1.
      existssl. intros [l1 l2]. setoid_rewrite bind_bind at 1. assertsl.
      intros Hl12. rewrite bind_ret_l.
      (* now I really need to push the or_spec further because in order to get to the 
         merge call (which itself might diverge , unless I actually  I need to just add more off ramps with o) *)

      setoid_rewrite bind_bind. assumesr. intros _ .
      existssr 2. cbn. repeat rewrite bind_bind.
      existssr l1. rewrite bind_bind. assertsr.
      auto. apply padded_refines_bind with (RR := sub_eq (sort_post l1) ).
      { apply padded_refines_vis. repeat constructor.
        intros. inv H. inj_existT. subst. sub_eqEAns_inv H7.
        subst. apply padded_refines_ret. constructor. inv H3. inj_existT.
        subst. auto.
      }
      intros ? l1s Hl1s. inv Hl1s.
      repeat rewrite bind_bind.
      existssr l2. repeat rewrite bind_bind. assertsr.
      auto. apply padded_refines_bind with (RR := sub_eq (sort_post l2) ).
      {
        apply padded_refines_vis. repeat constructor. intros.
        inv H0. inj_existT. subst. sub_eqEAns_inv H8.
        subst. apply padded_refines_ret. constructor. inv H3. inj_existT.
        subst. auto. }
      intros ? l2s Hl2s. inv Hl2s. rewrite bind_ret_l.
      rewrite merge_correct''. unfold partial_spec.
      apply or_spec_l.
      2 : { apply or_spec_r. right. apply padded_refines_spin. } (*same lemma as before*)
      apply or_spec_r. left. unfold total_spec. cbn. red in H. red in H0.
      assumesl. tauto.
      existssl. intros ls. assertsl. intros Hls. destruct H. destruct H0. 
      destruct Hls. existssr ls. assertsr.
      split; auto.
      destruct Hl12. rewrite H6, H, H0, H5. reflexivity.
      apply padded_refines_ret.
      constructor. split; auto.
      destruct Hl12. 
      split; auto.
      rewrite H6, H, H0, H5. reflexivity.
Admitted.

End sort_correct.

(*
Theorem merge
*)
