From ITree Require Export ITree ITreeFacts.
From Paco Require Import paco.
From Coq Require Export Eqdep EqdepFacts.
Section MrecBind.

  Context {D E : Type -> Type}.
  Context (bodies : D ~> itree (D +' E) ).
  Context {R S : Type}.
  Context (entry : D R).
  Check (mrec bodies entry).
  Context (k : R -> itree E S).
  Check (ITree.bind (mrec bodies entry) k ).

(*
  D1 D2
  RD (forall A B, D1 A -> D2 B -> Prop)
  d1 d2, RD d1 d2

  forall d1 d2, RD d1 d2 -> refines (RD + RE) RR (bodies1 d1) (bodies d2) 
  
  refines _ (trigger d1) (trigger d2) *)
(*
  Definition tagged (T : Type) (F : Type -> Type) : Type -> Type :=
    fun R => ((F R) * T)%type. 

  Definition tag {T R : Type} {F} (x : T) (f : F R) : tagged T F R := (f,x).
*)

(*
  bodies : (A1 -> M B1) -> (A2 -> M B2) -> ... -> (A1 -> M B1, A2 -> M B2, ...)
  cont : (A1 -> M B1) -> (A2 -> M B2) -> ... -> M C
  [letrec bodies entry]

*)

  Variant top_tagged : Type -> Type :=
    | tt_top : D R -> top_tagged S
    | tt_else A : D A -> top_tagged A.


  Definition end_with : (top_tagged ~> itree (top_tagged +' E) ).
  intros T [ | ].
  - assert (k' : R -> itree (D +' E) S ). 
    { clear -k. intros r.
      eapply interp; [ idtac | apply (k r)]. intros T e. apply (trigger e). }
    exact (interp (bimap (fun _ d => trigger (tt_else _ d) ) (id_ _) ) (ITree.bind (bodies _ d) k')).
  - exact (interp (bimap (fun _ d => trigger (tt_else _ d) ) (id_ _) ) (bodies _ d)).
 Defined.

  (*
    end_with = 
             fun (D E : Type ->  Type) (bodies : forall T : Type, D T -> itree (D +' E) T)
             (R S : Type) (k : R -> itree E S) (T : Type) (X : top_tagged T) =>
             match X in (top_tagged T0) return (itree (top_tagged +' E) T0) with
             | tt_top d =>
               let k' := fun r : R => interp (fun (T0 : Type) (e : E T0) => trigger e) (k r) in
             interp (bimap (fun (x1 : Type) (d0 : D x1) => trigger (tt_else x1 d0)) (id_ E))
             (ITree.bind (bodies R d) k')
             | tt_else A d =>
             interp (bimap (fun (x1 : Type) (d0 : D x1) => trigger (tt_else x1 d0)) (id_ E))
             (bodies A d)
             end
  *)

(*
  Definition end_with' T (t : top_tagged T) : itree (top_tagged +' E) T :=
    match t with
    | tt_top d => 
      let k' := fun r : R => interp (fun (T0 : Type) (e : E T0) => trigger e) (k r) in
      interp (bimap (fun (x1 : Type) (d0 : D x1) => trigger (tt_else x1 d0)) (id_ E)) 
             (ITree.bind (bodies R d) k')
    | tt_else _ d => interp (bimap (fun (x1 : Type) (d0 : D x1) => trigger (tt_else x1 d0)) (id_ E)) (bodies _ d) end. *)

Ltac inj_existT := repeat match goal with | H : existT _ _ _ = _ |- _ => apply inj_pair2 in H end.
Ltac use_simpobs := repeat match goal with
                           | H : RetF _ = observe ?t |- _ => apply simpobs in H 
                           | H : TauF _ = observe ?t |- _ => apply simpobs in H
                           | H : VisF _ _ = observe ?t |- _ => apply simpobs in H
                           end.

  Definition mrec_bind : itree E S :=
    mrec end_with (tt_top entry).

  Variant top_taggedR : forall A B, top_tagged A -> D B -> Prop :=
    | top_taggedR_top (d : D R) : top_taggedR S R (tt_top d) d
    | top_taggedR_else T (d : D T) : top_taggedR T T (tt_else _ d) d.

  Goal mrec end_with (tt_top entry) ≈ bind (mrec bodies entry) k.
    cbn. unfold mrec, interp_mrec. 
    (* I think I need to use the iter_natural law here to make it clear how the simulation will work *)
    (* will need to generalize tt_top entry to an arbitrary tagged, with some invariant
       that the payload is the same as entry, this may lead to some weird typing stuff
       also will probably
     *)
    assert (Htag : top_taggedR _ _ (tt_top entry) entry ).
    constructor.
    generalize dependent (tt_top entry). revert entry.

    ginit. gcofix CIH.
    intros entry entryt Hentry. inversion Hentry; subst; inj_existT; subst. 
    -  admit.
    - subst. inj_existT. unfold end_with. cbn.
      (*this is actually stranger than I thought, if it is a tt_else
                           
                          *) cbn.
    (* going further then this is a mistake until you know it is needed
       although if when I do it might be a good idea to start with a relation
       between end_with and bodies, they behave the same on a tt_else
       acts as bodies >>> k on a tt_top
     *)
  Admitted.

End MrecBind.

