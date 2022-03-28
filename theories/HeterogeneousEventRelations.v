From Coq Require Export Morphisms Setoid Program.Equality.
From ITree Require Export ITree ITreeFacts HeterogeneousRelations.


Definition relationEH (E1 E2 : Type -> Type) : Type := forall A B, E1 A -> E2 B -> Prop.

(*this is stronger than we need *)
Class ReflexiveE {E : Type -> Type} (RE : relationEH E E) :  Prop :=
  reflexiveE : forall A (e : E A), RE A A e e.

Class SymmetricE {E : Type -> Type} (RE : relationEH E E) :  Prop :=
  symmetricE : forall A B (e1 : E A) (e2 : E B), RE A B e1 e2 -> RE B A e2 e1.

Class TransitiveE {E : Type -> Type} (RE : relationEH E E) :  Prop :=
  transitiveE : forall A B C (e1 : E A) (e2 : E B) (e3 : E C),
    RE A B e1 e2 -> RE B C e2 e3 -> RE A C e1 e3.

Definition flipE {E1 E2 : Type -> Type} (RE : relationEH E1 E2) : relationEH E2 E1 :=
  fun A B e1 e2 => RE B A e2 e1.

Variant rcomposeE {E1 E2 E3 : Type -> Type}
           (RE12 : relationEH E1 E2) (RE23 : relationEH E2 E3) : forall A C, E1 A -> E3 C -> Prop := 
  rcomposeE_intro (A B C: Type) e1 e2 e3 : RE12 A B e1 e2 -> RE23 B C e2 e3 -> rcomposeE RE12 RE23 A C e1 e3.
  
(* notation issues*)
Variant sum_relE {E1 E2 F1 F2} (REE : relationEH E1 E2) (REF : relationEH F1 F2) : forall A B, (E1 +' F1) A -> (E2 +' F2) B -> Prop :=
| sum_relE_inl A B (e1 : E1 A) (e2 : E2 B) : REE A B e1 e2 -> sum_relE REE REF A B (inl1 e1) (inl1 e2)
| sum_relE_inr A B (f1 : F1 A) (f2 : F2 B) : REF A B f1 f2 -> sum_relE REE REF A B (inr1 f1) (inr1 f2).

Definition relationEAnsH (E1 E2 : Type -> Type) : Type := forall A B, E1 A -> A -> E2 B -> B -> Prop.


Variant sum_relAns {E1 E2 F1 F2} (REE : relationEAnsH E1 E2) (REF : relationEAnsH F1 F2) : 
  forall A B, (E1 +' F1) A -> A -> (E2 +' F2) B -> B -> Prop :=
| sum_relEAns_inl A B (e1 : E1 A) (e2 : E2 B) a b : REE A B e1 a e2 b -> sum_relAns REE REF A B (inl1 e1) a (inl1 e2) b
| sum_relEAns_inr A B (f1 : F1 A) (f2 : F2 B) a b : REF A B f1 a f2 b -> sum_relAns REE REF A B (inr1 f1) a (inr1 f2) b
.
