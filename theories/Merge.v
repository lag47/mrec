

Locate "<=?".

Require Import Coq.Lists.List Coq.Sorting.Permutation.

From Coq Require Export Morphisms Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts Eq.Rutt.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.

Require Export Refinement.

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


Inductive sorted : list nat -> Prop :=
  | sorted_nil : sorted nil
  | sorted_single x : sorted (x :: nil)
  | sorted_cons x y l : x <= y -> sorted (y :: l) -> sorted (x :: y :: l).

Lemma sorted_tail : forall l x, sorted (x :: l) -> sorted l.
Proof.
  intros l. induction l; intros; try (constructor; fail).
  inv H. auto.
Qed.
(*
Definition list_ind2_principle' (A : Type) (P : list A -> Prop) (Hnil : P nil)
         (Hcons1 : forall a, P (a :: nil) ) (Hcons2 : forall a b l, P l -> P (a :: b :: l))
         l : P l :=
  fix rec l :=
    match l with
    | nil => Hnil
    | a :: nil => Hcons1 a
    | a :: b :: t => Hcons2 a b t (rec t) end. l.
*)
Lemma list_ind2_principle :
    forall (A : Type) (P : list A -> Prop),
      P nil ->
      (forall (a:A), P (a :: nil)) ->
      (forall (a b : A) (l : list A), P l -> P (a :: b :: l)) ->
      forall l : list A, P l.
Proof. 
  intros. 
  set (fix rec l := 
         match l return P l with 
         | nil => H
         | a :: nil => H0 a
         | a :: b :: t => H1 a b t (rec t)
         end
      ) as f. auto.
Qed.

(*rec_fix*)

Definition halve {E} : list nat -> itree E (list nat * list nat) :=
    rec_fix (fun halve_rec l =>
               match l with
               | x :: y :: t => '(l1,l2) <- halve_rec t;; Ret (x :: l1, y :: l2)
               | x :: nil => Ret ( x :: nil  , nil )
               | nil => Ret ( nil , nil ) end

).

Definition assert_spec {E} (P : Type) : itree_spec E unit :=
  trigger (@Spec_exists E P );; Ret tt.

Lemma padded_assert_pad_elim {E1 E2} RE REAns R1 R2 RR P
      (phi : itree_spec E1 R1) (kphi : unit -> itree_spec E2 R2) :
  P -> padded_refines RE REAns RR phi (kphi tt) ->
  padded_refines RE REAns RR phi (ITree.bind (assert_spec P) kphi ).
Proof.
  intros. setoid_rewrite bind_trigger.
  unfold padded_refines in *. rewrite pad_bind, pad_vis.
  setoid_rewrite pad_ret. rewrite bind_vis. setoid_rewrite bind_tau.
  setoid_rewrite bind_ret_l. pstep. constructor. auto. constructor. pstep_reverse.
Qed.

Lemma padded_assert_pad_eliml {E1 E2} RE REAns R1 R2 RR P
      (phi : itree_spec E1 R1) (kphi : unit -> itree_spec E2 R2) :
  (P -> padded_refines RE REAns RR (kphi tt) phi) ->
  padded_refines RE REAns RR (ITree.bind (assert_spec P) kphi ) phi.
Proof.
  intros. setoid_rewrite bind_trigger.
  unfold padded_refines in *. rewrite pad_bind, pad_vis.
  setoid_rewrite pad_ret. rewrite bind_vis. setoid_rewrite bind_tau.
  setoid_rewrite bind_ret_l. pstep. constructor. 
  intros HP. specialize (H HP). constructor. pstep_reverse.
Qed.


Definition assume_spec {E} (P : Type) : itree_spec E unit :=
  trigger (@Spec_forall E P );; Ret tt.

Lemma padded_assume_pad_elim {E1 E2} RE REAns R1 R2 RR P
      (phi : itree_spec E1 R1) (kphi : unit -> itree_spec E2 R2) :
  (P -> padded_refines RE REAns RR phi (kphi tt)) ->
  padded_refines RE REAns RR phi (ITree.bind (assume_spec P) kphi ).
Proof.
  intros. setoid_rewrite bind_trigger.
  unfold padded_refines in *. rewrite pad_bind, pad_vis.
  setoid_rewrite pad_ret. rewrite bind_vis. setoid_rewrite bind_tau.
  setoid_rewrite bind_ret_l. pstep. constructor. 
  intros HP. specialize (H HP). constructor. pstep_reverse.
Qed.  

Lemma padded_assume_pad_eliml {E1 E2} RE REAns R1 R2 RR P
      (phi : itree_spec E1 R1) (kphi : unit -> itree_spec E2 R2) :
  P -> padded_refines RE REAns RR (kphi tt) phi ->
  padded_refines RE REAns RR (ITree.bind (assume_spec P) kphi ) phi.
Proof.
  intros. setoid_rewrite bind_trigger.
  unfold padded_refines in *. rewrite pad_bind, pad_vis.
  setoid_rewrite pad_ret. rewrite bind_vis. setoid_rewrite bind_tau.
  setoid_rewrite bind_ret_l. pstep. constructor. auto. constructor. pstep_reverse.
Qed.

Definition spec_exists {E} (T : Type) : itree_spec E T :=
  trigger (@Spec_exists E T).


(**)
Lemma spec_exists_elim {E1 E2} S1 R2 S2 RE REAns RR (phi : itree_spec E1 S1) 
      (kphi : R2 -> itree_spec E2 S2 ) r :
  refines RE REAns RR phi (kphi r) ->
  refines RE REAns RR phi (ITree.bind (spec_exists R2) kphi ).
Proof.
  intros. unfold spec_exists. setoid_rewrite bind_trigger.
  pstep. econstructor. pstep_reverse.
Qed.

Opaque assert_spec.

(*maybe there is a simpler way to derive this proof from the previous one*)
Lemma padded_spec_exists_elim {E1 E2} S1 R2 S2 RE REAns RR (phi : itree_spec E1 S1) 
      (kphi : R2 -> itree_spec E2 S2 ) r :
  padded_refines RE REAns RR phi (kphi r) ->
  padded_refines RE REAns RR phi (ITree.bind (spec_exists R2) kphi ).
Proof.
  intros.  unfold padded_refines in *. rewrite pad_bind. setoid_rewrite pad_vis.
  rewrite bind_vis. 
  setoid_rewrite pad_ret. setoid_rewrite bind_tau. setoid_rewrite bind_ret_l.
  pstep. econstructor. Unshelve. all : auto. constructor. pstep_reverse.
Qed.

Lemma padded_spec_exists_eliml {E1 E2} S1 R2 S2 RE REAns RR (phi : itree_spec E1 S1) 
      (kphi : R2 -> itree_spec E2 S2 ) :
  (forall r, padded_refines RE REAns RR (kphi r) phi) ->
  padded_refines RE REAns RR (ITree.bind (spec_exists R2) kphi ) phi .
Proof.
  intros.  unfold padded_refines in *. rewrite pad_bind. setoid_rewrite pad_vis.
  rewrite bind_vis. 
  setoid_rewrite pad_ret. setoid_rewrite bind_tau. setoid_rewrite bind_ret_l.
  pstep. econstructor. intros. constructor. pstep_reverse. apply H.
Qed.

Ltac existssr a := apply padded_spec_exists_elim with (r := a).

Ltac eexistssr := eapply padded_spec_exists_elim.

Ltac existssl := apply padded_spec_exists_eliml.


Definition spec_forall {E} (T : Type) : itree_spec E T :=
  trigger (@Spec_forall E T).

Lemma spec_forall_elim {E1 E2} S1 R2 S2 RE REAns RR (phi : itree_spec E1 S1) 
      (kphi : R2 -> itree_spec E2 S2 ) :
  (forall r, refines RE REAns RR phi (kphi r)) ->
  refines RE REAns RR phi (ITree.bind (spec_forall R2) kphi ).
Proof.
  intros. unfold spec_forall. rewrite bind_trigger.
  pstep. constructor. intros. pstep_reverse. apply H.
Qed.

Lemma padded_spec_forall_elim {E1 E2} S1 R2 S2 RE REAns RR (phi : itree_spec E1 S1) 
      (kphi : R2 -> itree_spec E2 S2 ):
  (forall r, padded_refines RE REAns RR phi (kphi r)) ->
  padded_refines RE REAns RR phi (ITree.bind (spec_forall R2) kphi ).
Proof.
  intros.  unfold padded_refines in *. rewrite pad_bind. setoid_rewrite pad_vis.
  rewrite bind_vis. 
  setoid_rewrite pad_ret. setoid_rewrite bind_tau. setoid_rewrite bind_ret_l.
  pstep. constructor. intros.  constructor. pstep_reverse.
  apply H.
Qed.

Lemma padded_spec_forall_eliml {E1 E2} S1 R2 S2 RE REAns RR (phi : itree_spec E1 S1) 
      (kphi : R2 -> itree_spec E2 S2 ) r:
  padded_refines RE REAns RR (kphi r) phi ->
  padded_refines RE REAns RR (ITree.bind (spec_forall R2) kphi ) phi.
Proof.
  intros.  unfold padded_refines in *. rewrite pad_bind. setoid_rewrite pad_vis.
  rewrite bind_vis. 
  setoid_rewrite pad_ret. setoid_rewrite bind_tau. setoid_rewrite bind_ret_l.
  pstep. econstructor. constructor. pstep_reverse.
Qed.

Definition halve_spec {E} (l : list nat) : itree_spec E (list nat * list nat) :=
  l1 <- spec_exists (list nat);; 
  l2 <- spec_exists (list nat);;
  assert_spec (Permutation l (l1 ++ l2) );;
  Ret (l1, l2).

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

Definition merge_spec1 {E} l1 l2 : itree_spec E (list nat) :=
  l <- spec_exists (list nat);;
  assert_spec (Permutation l (l1 ++ l2) );;
  Ret l.

Definition merge_spec2 {E} l1 l2 : itree_spec E (list nat) :=
  assume_spec (sorted l1);;
  assume_spec (sorted l2);;
  l <- spec_exists (list nat);;
  assert_spec (sorted l);;
  Ret l.

Definition merge_spec {E} l1 l2 : itree_spec E (list nat) := 
  and_spec (merge_spec1 l1 l2) (merge_spec2 l1 l2).

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

Definition sort_spec {E} (l : list nat) : itree_spec E (list nat) :=
  l' <- spec_exists (list nat);;
  assert_spec (Permutation l l');;
  assert_spec (sorted l');;
  Ret l'.


Definition padded_refines_eq {E R1 R2} RR (phi1 : itree_spec E R1) (phi2 : itree_spec E R2) :=
  padded_refines eqE eqEAns RR phi1 phi2.

Global Instance padded_refines_eq_refl {E R} : Reflexive (@padded_refines_eq E R R eq).
Proof.
  red. intros. unfold padded_refines_eq, padded_refines. apply refl_refines; auto.
  - red. intros. constructor.
  - red. intros. inv H. inj_existT. subst. auto.
  - apply pad_is_padded.
Qed.

Global Instance padded_refines_eq_trans {E R} : Transitive (@padded_refines_eq E R R eq).
Proof.
  intros phi1 phi2 phi3 Hphi12 Hphi23. unfold padded_refines_eq, padded_refines in *.
  eapply refines_monot; try eapply refinesTrans; eauto with solve_padded; try apply pad_is_padded.
  - intros. assert (A = B). inv PR. auto. subst.  assert (ea = eb). inv PR. inj_existT.
    subst. auto. subst. assert (x0 = x1). inv PR. inj_existT. subst. auto.
    subst. clear PR. constructor. intros. destruct H. inv H. inj_existT. subst.
    inv H0. inj_existT. subst. exists x1.
    split; constructor.
  - intros. inv PR. inj_existT. subst. 
    assert (A = B0). inv H3. auto. subst. assert (B = B0). inv H4. auto.
    subst. assert (x0 = e2). inv H3. inj_existT. subst. auto. subst. auto.
  - intros. inv PR. auto.
Qed.
(*
Global Instance padded_refines_eq_bind_proper  E1 E2 RE REAns R1 R2 RR : 
  Proper (padded_refines_eq eq ==> eq ==> @padded_refines E1 E2 R1 R2 RE REAns RR ) ITree.bind.
*)
(*from there there is a bit more *)

Lemma interp_mrec_ret : 
  forall {D E : Type -> Type} (ctx : forall T : Type, D T -> itree (D +' E) T) R (r :R),
    interp_mrec ctx (Ret r) ≅ Ret r.
Proof.
  intros. setoid_rewrite unfold_iter. cbn. rewrite bind_ret_l. reflexivity.
Qed.


Instance perm_eq A : Equivalence (@Permutation A).
Proof.
  constructor.
  - red. apply Permutation_refl.
  - red. apply Permutation_sym.
  - red. apply Permutation_trans.
Qed.

(* in addition to needing more lemmas and stuff, I think I should be careful 
   about what I am inducting on, its rather subtle*)
Lemma halve_correct E l : padded_refines_eq eq (halve l) (@halve_spec E l).
Proof.
  revert l.
  apply list_ind2_principle.
  - unfold halve, halve_spec, rec_fix, rec, mrec. cbn.
    rewrite interp_mrec_ret. existssr (@nil nat). existssr (@nil nat). 
    apply padded_assert_pad_elim. constructor. 
    reflexivity.
  - intros n. cbn. unfold halve, halve_spec, rec_fix, rec, mrec. cbn.
    rewrite interp_mrec_ret. existssr ( n :: nil ). existssr (@nil nat).
    apply padded_assert_pad_elim. cbn. repeat constructor.
    reflexivity.
  - intros a b l Hl.
    unfold halve, halve_spec, rec_fix, rec, mrec. cbn. cbn.
    rewrite interp_mrec_bind.
    setoid_rewrite interp_mrec_trigger. cbn.
    match goal with |- padded_refines_eq eq (ITree.bind ?h _) _ => set h as t end.
    assert (t = halve l).
    { unfold halve, rec_fix, rec, t. reflexivity. }
    rewrite H. clear H t. etransitivity.
    eapply padded_refines_bind; eauto. intros; subst. destruct r2 as [l1 l2].
    rewrite interp_mrec_ret. Unshelve. 3 : { apply (fun '(l1,l2) => Ret (a :: l1, b :: l2) ). } cbn. reflexivity.
    cbn. rewrite bind_bind.
    existssl. intros l1. setoid_rewrite bind_bind. existssl. intros l2.
    existssr (a :: l1). existssr (b :: l2). rewrite bind_bind.
    apply padded_assert_pad_eliml. intros. apply padded_assert_pad_elim.
    { (* this is a permutation fact *) cbn. rewrite Permutation_app_comm. cbn.
      rewrite H. rewrite Permutation_app_comm. reflexivity. }
    rewrite bind_ret_l. reflexivity.
Qed.
(*got everything except a single Permutation fact*)
