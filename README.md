# Zeromelo-Fraenkel set theory in Coq

This is a self-study project of implementing ZF axioms in Coq.

- `ZF.v` defines the axioms of ZF.
- `Aczel.v` implements the axioms.

The following axioms are used to implement them.

- Predicate extensionality `∀ P Q, (∀ a, P a ↔ Q a) → P = Q` is used to prove set equalities.
- Functional choice: `∀ R, (∀ x, ∃ y, R x y) → ∃ f, ∀ x, R x (f x)` is used to implement the axiom of replacement.

See [https://www.ps.uni-saarland.de/settheory.html] for the resources I consulted.
