section

/-!
# Logic exercises

Try and fill in the following `sorry`s.
-/

example (p q r : Prop) : (p → q) → (p → r) → p → q :=
  sorry

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r :=
  sorry

example (p q r s : Prop) : (p → (q → r)) → (p → (r → s)) → (p → (q → s)) :=
  sorry

example (p q : Prop) : (p → q) → (p → ¬ q) → ¬ p :=
  sorry

example (α β : Type) (p : α → β → Prop) : (∀ x y, p x y) → ∀ y x, p x y :=
  sorry

example (α : Type) (p q : α → Prop) :
    (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x :=
  sorry

example (α β : Type) (p : α → β → Prop) (h : ∃ x, ∀ y, p x y) : ∀ y, ∃ x, p x y :=
  sorry

example (α : Type) (p : α → Prop) (h : ∀ x, ¬ p x) : ¬ ∃ x, p x :=
  sorry
