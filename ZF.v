(** * Zeromelo-Fraenkel set theory. *)

Module Type ZF.

(** Set, membership, and subsets *)
Parameter set : Type.
Parameter In : set -> set -> Prop.
Notation "x ∈ A" := (In A x) (at level 70).
Notation "x ∉ A" := (~ x ∈ A) (at level 70).

Definition Included (A B : set) : Prop := forall x, x ∈ A -> x ∈ B.
Infix "⊂" := Included (at level 70).
Notation "A ⊄ B" := (~ A ⊂ B) (at level 70).
Notation "A ⊊ B" := (A ⊂ B /\ A <> B) (at level 70).

(** Extensionality *)
Axiom set_ext : forall A B, A ⊂ B -> B ⊂ A -> A = B.

(** Foundation *)
Axiom epsilon_induction :
  forall P : set -> Prop, (forall A, (forall x, x ∈ A -> P x) -> P A) -> forall B, P B.

(** Empty set *)
Parameter empty : set.
Notation "∅" := empty.
Axiom in_empty : forall x, x ∉ ∅.

(** Pairing *)
Parameter upair : set -> set -> set.
Axiom in_upair : forall a b x, x ∈ upair a b <-> x = a \/ x = b.
Notation "{ a , }" := (upair a a) (format "{  a ,  }").

(** Unions *)
Parameter union : set -> set.
Notation "⋃" := union.
Axiom in_union : forall F x, x ∈ ⋃ F <-> exists A, A ∈ F /\ x ∈ A.

(** Power sets *)
Parameter power : set -> set.
Definition ℙ := power.
Axiom in_power : forall X A, A ∈ ℙ X <-> A ⊂ X.

(** Separation (specification) *)
Parameter sep : set -> (set -> Prop) -> set.
Notation "{ a 'in' X | P }" := (sep X (fun a => P)) (format "{  a  in  X  |  P  }").
Axiom in_sep : forall X P x, x ∈ { a in X | P a } <-> x ∈ X /\ P x.

(** Additional notations *)
Definition bin_union (A B : set) : set := ⋃ (upair A B).
Infix "∪" := bin_union (at level 50).

Definition bin_intersection (A B : set) : set := { x in A | x ∈ B }.
Infix "∩" := bin_intersection (at level 40).

Notation "{ a , .. , b , c }" := ({a,} ∪ .. ({b,} ∪ {c,}) ..) (format "{  a ,  .. ,  b ,  c  }").

(** Infinity *)
Parameter Inf_set : set.
Axiom axiom_inf : ∅ ∈ Inf_set /\ forall n, n ∈ Inf_set -> n ∪ {n,} ∈ Inf_set.

(** Functional replacement *)
Parameter replace : (set -> set) -> set -> set.
Axiom axiom_replacement : forall f A y, y ∈ replace f A <-> exists x, x ∈ A /\ y = f x.

End ZF.
