(** * Set axiom implementations with Aczel's tree type. *)
Require Import ClassicalFacts.
Require Import Setoid.
Require Import Utf8.
From ZF Require Import ZF.

(** This implementation relies on the predicate extensionality. *)
Axiom predicate_extensionality : ∀ {A : Type} (P Q : A → Prop), (∀ a, P a ↔ Q a) → P = Q.

(** The implementation of the axiom of replacement relies on the functional choice. *)
Axiom functional_choice : ∀ {A : Type} (R : A → A → Prop), (∀ x, ∃ y, R x y) → ∃ f, ∀ x, R x (f x).

Module Acz_set : ZF.

(** Preliminary lemmata *)
Lemma proof_irrelevance : ∀ (P : Prop) (p q : P), p = q.
Proof.
  apply ext_prop_dep_proof_irrel_cic. intros A B AiffB.
  assert (H: (λ _ : True, A) = (λ _ : True, B)). { apply predicate_extensionality. intro. apply AiffB. }
  apply (f_equal (λ f, f I)) in H. apply H. Qed.

Lemma exist_eq {A : Type} (P : A → Prop) a b p q : a = b → exist P a p = exist P b q.
Proof. intro aeqb. subst b. rewrite (proof_irrelevance (P a) p q). reflexivity. Qed.

(** Aczel's tree type *)
Inductive Acz : Type := acz : ∀ (J : Type), (J → Acz) → Acz.
Definition dom (a : Acz) : Type := match a with acz J _ => J end.
Definition fn (a : Acz) : dom a → Acz := match a with acz _ f => f end.

(** Equivalence *)
Fixpoint equiv (a b : Acz) : Prop :=
  (∀ i, ∃ j, equiv (fn a i) (fn b j)) ∧ (∀ j, ∃ i, equiv (fn a i) (fn b j)).

Infix "≃" := equiv (at level 70).

Lemma equiv_refl : ∀ a, a ≃ a.
Proof. intro a. induction a as [I f ind]. split; intro j; exists j; apply ind. Qed.

Lemma equiv_symm : ∀ a b, a ≃ b → b ≃ a.
Proof.
  intro a. induction a as [I f ind]. intros [J g] [i2j j2i]. split.
  - intro j. destruct (j2i j) as [i fi_eqv_gj]. exists i. apply ind, fi_eqv_gj.
  - intro i. destruct (i2j i) as [j fi_eqv_gj]. exists j. apply ind, fi_eqv_gj.
  Qed.

Lemma equiv_trans : ∀ a b c, a ≃ b → b ≃ c → a ≃ c.
Proof.
  intro a. induction a as [I f ind]. intros [J g] [K h] [i2j j2i] [j2k k2j]. split.
  - intro i. destruct (i2j i) as [j fi_eqv_gj]. destruct (j2k j) as [k gj_eqv_hk].
    exists k. apply (ind _ (g j)); [apply fi_eqv_gj | apply gj_eqv_hk].
  - intro k. destruct (k2j k) as [j gj_eqv_hk]. destruct (j2i j) as [i fi_eqv_gj].
    exists i. apply (ind _ (g j)); [apply fi_eqv_gj | apply gj_eqv_hk].
  Qed.

(** Use setoid tactics for concise proofs. *)
Add Relation Acz equiv reflexivity proved by equiv_refl
                       symmetry proved by equiv_symm
                       transitivity proved by equiv_trans as equiv_rel.

Add Parametric Morphism : equiv with signature equiv ==> eq as equiv_mor.
Proof. intros. apply predicate_extensionality. intro. rewrite H. apply iff_refl. Qed.

Lemma equiv_elem : ∀ (A B : Acz), A ≃ B → ∀ i, ∃ j, fn A i ≃ fn B j.
Proof. intros [I f] [J g] eqv. apply eqv. Qed.

(** Equivalence-based membership and subsets *)
Definition AIn (A a : Acz) : Prop := ∃ i, a ≃ (fn A i).
Notation "a ∈' A" := (AIn A a) (at level 70).

Add Parametric Morphism : AIn with signature equiv ==> equiv ==> iff as AIn_mor.
Proof.
  intros [I f] [J g] [i2j j2i] a b a_eqv_b. split.
  - intros [i a_eqv_fi]. destruct (i2j i) as [j fi_eqv_gj]. exists j.
    rewrite <- a_eqv_b, a_eqv_fi, fi_eqv_gj. reflexivity.
  - intros [j b_eqv_gj]. destruct (j2i j) as [i fi_eqv_gj]. exists i.
    rewrite a_eqv_b, b_eqv_gj, fi_eqv_gj. reflexivity.
  Qed.

Lemma elem (A : Acz) (i : dom A) : fn A i ∈' A.
Proof. exists i. reflexivity. Qed.

Definition AIncluded (A B : Acz) : Prop := ∀ i, ∃ j, fn A i ≃ fn B j.
Infix "⊂'" := AIncluded (at level 70).

(** [set] is defined as the equivalence classes. *)
Definition equiv_class (p : Acz → Prop) : Prop := ∃ a, p = equiv a.
Definition set := sig equiv_class.
Definition set_of (A : Acz) : set := exist _ (equiv A) (ex_intro _ A eq_refl).

Add Parametric Morphism : set_of with signature equiv ==> eq as set_of_mor.
Proof. intros a b a_eqv_b. apply exist_eq. rewrite a_eqv_b. reflexivity. Qed.

Tactic Notation "lower" constr(x) "as" simple_intropattern(a) :=
  let f := fresh "f" in let f_eq := fresh "f_eq" in
  destruct x as [f [a f_eq]]; subst f; fold (set_of a) in *.
Tactic Notation "lower" ident(x) := lower x as x.
Tactic Notation "lower" ident(x) ident(y) := lower x; lower y.
Tactic Notation "lower" ident(x) ident(y) ident(z) := lower x; lower y; lower z.

Lemma set_of_eq (A B : Acz) : set_of A = set_of B ↔ A ≃ B.
Proof.
  split; [|apply set_of_mor]. intros AeqB. apply (f_equal (@proj1_sig _ equiv_class)) in AeqB.
  simpl in AeqB. rewrite AeqB. reflexivity. Qed.

(** Class-preserving function is lifted to set function.
    This result will extensively be used to define set level functions. *)
Definition equiv_compat (f : Acz → Acz) : Prop := ∀ a b, a ≃ b → f a ≃ f b.

Lemma equiv_compat_class (f : Acz → Acz) (x : set) :
  equiv_compat f → equiv_class (λ b, ∃ a, proj1_sig x a ∧ b ≃ f a).
Proof.
  intro compat_f. lower x. exists (f x). apply predicate_extensionality. intro y. split.
  - intros [a [x_eqv_a y_eqv_fa]]. rewrite y_eqv_fa. apply compat_f, x_eqv_a.
  - intros fx_eqv_y. exists x. split; [simpl; reflexivity | symmetry; apply fx_eqv_y].
  Qed.

Definition Lift {f} (P : equiv_compat f) (X : set) : set := exist _ _ (equiv_compat_class f X P).

Definition equiv_compat2 (f : Acz → Acz → Acz) : Prop :=
  ∀ a a', a ≃ a' → ∀ b b', b ≃ b' → f a b ≃ f a' b'.

Lemma equiv_compat2_class (f : Acz → Acz → Acz) (x y : set) :
  equiv_compat2 f → equiv_class (λ c, ∃ a b, proj1_sig x a ∧ proj1_sig y b ∧ c ≃ f a b).
Proof.
  intro compat_f. lower x y. exists (f x y). apply predicate_extensionality. intro z. simpl. split.
  - intros [a [b [x_eqv_a [y_eqv_b z_eqv_fab]]]]. rewrite z_eqv_fab. apply compat_f; assumption.
  - intro fxy_eqv_z. exists x, y. rewrite fxy_eqv_z. repeat split; reflexivity.
  Qed.

Definition Lift2 {f} (P : equiv_compat2 f) (X Y : set) : set := exist _ _ (equiv_compat2_class f X Y P).

(** set-level membership and inclusion *)
Definition In (X x : set) := ∀ A a, proj1_sig X A → proj1_sig x a → a ∈' A.
Notation "x ∈ X" := (In X x) (at level 70).
Notation "x ∉ X" := (~ x ∈ X) (at level 70).

Definition Included (X Y : set) : Prop := ∀ x, x ∈ X → x ∈ Y.
Infix "⊂" := Included (at level 70).

Lemma set_of_in (A a : Acz) : set_of a ∈ set_of A ↔ a ∈' A.
Proof. split.
  - intros a_in_A. apply a_in_A; simpl; reflexivity.
  - intros a_in_A A' a' AeqvA' aeqva'. rewrite <- AeqvA', <- aeqva'. apply a_in_A.
  Qed.

(* Lemma set_of_in_class (a : Acz) (P : Acz → Prop) (C : equiv_class P) :
  set_of a ∈ exist _ P C ↔ ∀ A, P A → a ∈' A.
Proof. split.
  - intros a_in_class A PA. apply a_in_class; [apply PA | simpl; reflexivity].
  - intros P_imp_a_in A a' PA a_eqv_a'. rewrite <- a_eqv_a'. apply P_imp_a_in, PA.
  Qed. *)

Lemma set_of_in_class (a : Acz) (P : Acz → Prop) (C : equiv_class P) :
  (∀ A, P A → a ∈' A) → set_of a ∈ exist _ P C.
Proof. intros Pimp A a' PA a_eqv_a'. rewrite <- a_eqv_a'. apply Pimp, PA. Qed.

Lemma set_of_in_class_ex (a : Acz) (P : Acz → Prop) (C : equiv_class P) :
  set_of a ∈ exist _ P C → ∃ A, P A ∧ a ∈' A.
Proof.
  intro a_in_PC. destruct C as [A Peq]. subst P. exists A. split; [reflexivity|].
  apply set_of_in, a_in_PC. Qed.

Lemma set_of_sub (A B : Acz) : set_of A ⊂ set_of B ↔ A ⊂' B.
Proof. split.
  - intros AsubB i. apply set_of_in, AsubB, set_of_in, elem.
  - intros AsubB a a_in_A. lower a. apply set_of_in. apply set_of_in in a_in_A as [i a_eqv_Ai].
    destruct (AsubB i) as [j Ai_eqv_Bj]. exists j. rewrite a_eqv_Ai, Ai_eqv_Bj. reflexivity.
  Qed.

(** Extensionality *)
Theorem set_ext : ∀ X Y, X ⊂ Y → Y ⊂ X → X = Y.
Proof.
  intros X Y XsubY YsubX. lower X Y. apply set_of_eq. apply set_of_sub in XsubY, YsubX.
  destruct X as [I f], Y as [J g]. split; [apply XsubY|].
  intro j. destruct (YsubX j) as [i gj_eqv_fi]. exists i. symmetry. apply gj_eqv_fi.
  Qed.

(** Foundation *)
Theorem epsilon_induction : ∀ P : set → Prop, (∀ A, (∀ x, x ∈ A -> P x) -> P A) -> ∀ B, P B.
Proof.
  intros P Eind Y. lower Y. induction Y as [I f Pfi]. apply Eind. intros x x_in_B.
  lower x. apply set_of_in in x_in_B as [i x_eqv_fi]. rewrite x_eqv_fi. apply Pfi. Qed.

(** Empty set *)
Definition AEmpty : Acz := @acz False (λ a, match a with end).
Definition empty : set := set_of AEmpty.
Notation "∅" := empty.

Theorem in_empty : ∀ x : set, x ∉ ∅.
Proof. intros x x_in_E. lower x. apply set_of_in in x_in_E as []. contradiction. Qed.

(** Pairing *)
Definition APair (a b : Acz) : Acz := acz bool (λ x, if x then a else b).
Definition ASing (a : Acz) : Acz := APair a a.

Add Parametric Morphism : APair with signature equiv ==> equiv ==> equiv as APair_mor.
Proof. intros a a' a_eq_a' b b' b_eq_b'. split; intro i; exists i; destruct i; assumption. Qed.

Definition upair : set → set → set := Lift2 APair_mor.

Theorem in_upair : ∀ (a b x : set), x ∈ upair a b ↔ x = a ∨ x = b.
Proof.
  intros a b x. lower a b x. split.
  - intro x_in_ab.
    apply set_of_in_class_ex in x_in_ab as [A [[a' [b' [a_eqv_a' [b_eqv_b' A_eqv_a'b']]]] x_in_A]].
    rewrite A_eqv_a'b' in x_in_A. destruct x_in_A as [[|] x_eqv].
    + left. apply set_of_eq. rewrite x_eqv, a_eqv_a'. reflexivity.
    + right. apply set_of_eq. rewrite x_eqv, b_eqv_b'. reflexivity.
  - intros [x_eq_a | x_eq_b] A.
    + intros a' [a0 [b0 [a_eqv_a0 [b_eqv_b0 A_eqv_a0b0]]]] x_eqv_a'. rewrite A_eqv_a0b0. exists true.
      simpl in *. rewrite <- x_eqv_a', <- a_eqv_a0. apply set_of_eq, x_eq_a.
    + intros b' [a0 [b0 [a_eqv_a0 [b_eqv_b0 A_eqv_a0b0]]]] x_eqv_b'. rewrite A_eqv_a0b0. exists false.
      simpl in *. rewrite <- x_eqv_b', <- b_eqv_b0. apply set_of_eq, x_eq_b.
  Qed.

(** Unions *)
Inductive AUnion_dom (A : Acz) : Type := AUnion_ipair : ∀ i, dom (fn A i) → AUnion_dom A.
Definition AUnion_fn (A : Acz) (k : AUnion_dom A) : Acz :=
  match k with AUnion_ipair _ i j => fn (fn A i) j end.
Definition AUnion (A : Acz) : Acz := acz (AUnion_dom A) (AUnion_fn A).

Add Parametric Morphism : AUnion with signature equiv ==> equiv as AUnion_mor.
Proof.
  intros [I f] [J g] [AsubB BsubA]. split; simpl in *.
  - intros [i i2]. destruct (AsubB i) as [j fi_eqv_gj].
    destruct (equiv_elem _ _ fi_eqv_gj i2) as [j2 fii2_eqv_gjj2].
    exists (AUnion_ipair (acz J g) j j2). apply fii2_eqv_gjj2.
  - intros [j j2]. destruct (BsubA j) as [i fi_eqv_gj].
    symmetry in fi_eqv_gj. destruct (equiv_elem _ _ fi_eqv_gj j2) as [i2 gjj2_eqv_fii2].
    exists (AUnion_ipair (acz I f) i i2). symmetry. apply gjj2_eqv_fii2. 
  Qed.

Definition union : set → set := Lift AUnion_mor.
Notation "⋃" := union.

Theorem in_union : ∀ F x, x ∈ ⋃ F ↔ ∃ X, X ∈ F ∧ x ∈ X.
Proof.
  intros F x. lower F x. split.
  - intro x_in_UF.
   destruct (x_in_UF (AUnion F) x) as [[i j] x_eqv_UFij]; simpl in *.
    + exists F. split; [reflexivity|]. split; intro i; exists i; reflexivity.
    + reflexivity.
    + exists (set_of (fn F i)). split; apply set_of_in; [| rewrite x_eqv_UFij]; apply elem.
  - intros [X [XinF x_in_X]]. lower X. apply set_of_in in x_in_X as [i x_eqv_Xi], XinF as [j XeqvFj].
    apply set_of_in_class. intros U [F' [FeqvF' UeqvUF']]. simpl in FeqvF'.
    destruct (equiv_elem X (fn F j) XeqvFj i) as [k Xi_eqv_Fjk].
    rewrite UeqvUF', <- FeqvF', x_eqv_Xi, Xi_eqv_Fjk.
    exists (AUnion_ipair _ j k). reflexivity.
  Qed.

(** Power sets *)
Definition APower (A : Acz) : Acz :=
  acz (dom A → Prop) (λ P, acz (sig P) (λ s, fn A (proj1_sig s))).

Add Parametric Morphism : APower with signature equiv ==> equiv as APower_mor.
Proof.
  intros [I f] [J g] [AsubB BsubA]. split; simpl in *.
  - intro p. exists (λ j, ∃ i, p i ∧ f i ≃ g j). split.
    + intros [i pi]. destruct (AsubB i) as [j fi_eq_gj].
      exists (exist _ j (ex_intro _ i (conj pi fi_eq_gj))). apply fi_eq_gj.
    + intros [j [i [pi fi_eq_gj]]]. exists (exist _ i pi). apply fi_eq_gj.
  - intro q. exists (λ i, ∃ j, q j ∧ f i ≃ g j). split.
    + intros [i [j [qj fi_eq_gj]]]. exists (exist _ j qj). apply fi_eq_gj.
    + intros [j qj]. destruct (BsubA j) as [i fi_eq_gj].
      exists (exist _ i (ex_intro _ j (conj qj fi_eq_gj))). apply fi_eq_gj.
  Qed.

Definition power : set → set := Lift APower_mor.
Definition ℙ := power.

Theorem in_power : ∀ Y X, X ∈ ℙ Y ↔ X ⊂ Y.
Proof.
  intros Y X. lower Y X. split.
  - intros XinPY. apply set_of_in_class_ex in XinPY as [P [[A [YeqvA PeqvPA]] XinP]].
    rewrite PeqvPA, <- YeqvA in XinP. apply set_of_sub. intro i. destruct XinP as [p XeqvPYp].
    destruct (equiv_elem _ _ XeqvPYp i) as [[j pj] Xi_eqv_Yj]. exists j. apply Xi_eqv_Yj.
  - intros XsubY P B [Y' [YeqvY' PeqvPY']] XeqvB. simpl in *. rewrite PeqvPY', <- XeqvB, <- YeqvY'.
    apply set_of_sub in XsubY. exists (λ j, ∃ i, fn X i ≃ fn Y j). destruct X as [I f]. split; simpl.
    + intro i. destruct (XsubY i) as [j fi_eqv_Yj].
      exists (exist _ j (ex_intro _ i fi_eqv_Yj)). apply fi_eqv_Yj.
    + intros [j [i fi_eqv_Yj]]. exists i. apply fi_eqv_Yj.
  Qed.

(** Separation *)
Definition ASep (P : set → Prop) (A : Acz) : Acz :=
  acz { i | P (set_of (fn A i)) } (λ s, fn A (proj1_sig s)).

Add Parametric Morphism (P : set → Prop) : (ASep P) with signature equiv ==> equiv as ASep_mor.
Proof.
  intros [I f] [J g] [i2j j2i]. split; simpl in *.
  - intros [i PAi]. destruct (i2j i) as [j fi_eqv_gj].
    assert (PBj: P (set_of (g j))). { rewrite <- fi_eqv_gj. apply PAi. }
    exists (exist _ j PBj). apply fi_eqv_gj.
  - intros [j PBj]. destruct (j2i j) as [i fi_eqv_gj].
    assert (PAi: P (set_of (f i))). { rewrite fi_eqv_gj. apply PBj. }
    exists (exist _ i PAi). apply fi_eqv_gj.
  Qed.

Definition sep (X : set) (P : set → Prop) : set := Lift (ASep_mor P) X.
Notation "{ a 'in' X | P }" := (sep X (λ a, P)) (format "{  a  in  X  |  P  }").

Theorem in_sep : ∀ X P x, x ∈ { a in X | P a } ↔ x ∈ X ∧ P x.
Proof.
  intros X P x. lower X x. split.
  - intro x_in_comp. apply set_of_in_class_ex in x_in_comp as [A [[X' [XeqvX' AeqvSep]] x_in_A]].
    rewrite AeqvSep, <- XeqvX' in x_in_A. destruct x_in_A as [[i PXi] x_eqv_Xi]. simpl in *. split.
    + apply set_of_in. exists i. apply x_eqv_Xi.
    + rewrite x_eqv_Xi. apply PXi. 
  - intros [x_in_X Px] S x' [X' [XeqvX' SeqvSep]] x_eqv_x'. apply set_of_in in x_in_X as [i x_eqv_Xi].
    rewrite <- x_eqv_x', SeqvSep, <- XeqvX', x_eqv_Xi. rewrite x_eqv_Xi in Px.
    exists (exist _ i Px). reflexivity.
  Qed.

(** Infinity *)
Definition bin_union (A B : set) : set := ⋃ (upair A B).
Infix "∪" := bin_union (at level 50).

Definition bin_intersection (A B : set) : set := { x in A | x ∈ B }.
Infix "∩" := bin_intersection (at level 40).

Notation "{ a , }" := (upair a a) (format "{ a , }").
Notation "{ a , .. , b , c }" := ({a,} ∪ .. ({b,} ∪ {c,}) ..) (format "{  a ,  .. ,  b ,  c  }").

Fixpoint AInf_fn (n : nat) : Acz := match n with
                                    | O => AEmpty
                                    | S n => AUnion (APair (AInf_fn n) (ASing (AInf_fn n)))
                                    end.

Definition Inf_set : set := set_of (acz nat AInf_fn).

Theorem axiom_inf : ∅ ∈ Inf_set ∧ ∀ n, n ∈ Inf_set → n ∪ {n,} ∈ Inf_set.
Proof.
  split; [apply set_of_in; exists O; reflexivity|]. intros n. lower n.
  intros n_in_I J m [IsubJ JsubI] [s [[a [b [n_a [[c [d [n_c [n_d b_cd]]]] s_ab]]]] m_Us]].
  apply set_of_in in n_in_I as [k n_Ik]. simpl in *. destruct (IsubJ (S k)) as [j ISk_eqv_Jj].
  rewrite m_Us, s_ab, <- n_a, b_cd, <- n_c, <- n_d, n_Ik, ISk_eqv_Jj. apply elem.
  Qed.

(** Replacement *)
Lemma ALower (F : set → set) : ∃ f : Acz → Acz, ∀ a, F (set_of a) = set_of (f a).
Proof.
  apply (functional_choice (λ a b, F (set_of a) = set_of b)). intro a.
  lower (F (set_of a)) as b. exists b. reflexivity. Qed.

Lemma AReplace_class (f : set → set) (X : set) :
  equiv_class (λ B, ∀ y, y ∈ set_of B ↔ ∃ x, x ∈ X ∧ y = f x).
Proof.
  lower X. destruct X as [I u]. destruct (ALower f) as [f' fa_eq_f'a].
  exists (acz I (λ i, f' (u i))). apply predicate_extensionality. intros [J v]. split.
  - intro vdef. split; simpl; [intro i | intro j].
    + assert (fui_in_v: f' (u i) ∈' acz J v). {
        apply set_of_in. rewrite <- fa_eq_f'a. apply vdef. exists (set_of (u i)).
        split; [apply set_of_in, elem | reflexivity].
      }
      destruct fui_in_v as [j fui_eqv_vj]. exists j. apply fui_eqv_vj.
    + destruct (proj1 (vdef (set_of (v j))) ltac:(apply set_of_in, elem)) as [x [x_in_u vj_eq_fx]].
      lower x. apply set_of_in in x_in_u as [i x_eqv_ui]. exists i.
      apply set_of_eq. rewrite <- fa_eq_f'a, vj_eq_fx, x_eqv_ui. reflexivity.
  - intros [fXsubY YsubfX] y. simpl in fXsubY, YsubfX. lower y. split.
    + intros y_in_v. apply set_of_in in y_in_v as [j y_eqv_vj]. destruct (YsubfX j) as [i fui_eqv_vj].
      exists (set_of (u i)). split; [apply set_of_in, elem|].
      rewrite fa_eq_f'a. apply set_of_eq. rewrite fui_eqv_vj, y_eqv_vj. reflexivity.
    + intros [x [x_in_u y_eq_fx]]. lower x. apply set_of_in.
      apply set_of_in in x_in_u as [i x_eqv_ui]. destruct (fXsubY i) as [j fui_eqv_vj].
      exists j. rewrite <- fui_eqv_vj. apply set_of_eq. rewrite <- fa_eq_f'a, y_eq_fx. f_equal.
      apply set_of_eq, x_eqv_ui.
  Qed.

Definition replace (f : set → set) (X : set) : set := exist _ _ (AReplace_class f X).

Theorem axiom_replacement : ∀ f X y, y ∈ replace f X ↔ ∃ x, x ∈ X ∧ y = f x.
Proof. split.
  - lower X y. intro y_in_rfX. apply set_of_in_class_ex in y_in_rfX as [Y [Ydef y_in_Y]].
    apply Ydef, set_of_in, y_in_Y.
  - intros [x [x_in_X y_eq_fx]]. subst y. destruct (ALower f) as [f' fa_eq_f'a].
    lower X x. rewrite fa_eq_f'a. apply set_of_in_class. intros Y Ydef. apply set_of_in, Ydef.
    exists (set_of x). split; [apply x_in_X | rewrite fa_eq_f'a; reflexivity].
  Qed.
  
End Acz_set.
