import Mathlib

section

variable (P Q R : Prop)

-- Week 2, Day 1: Disjunction

-- Worked example
example : P → P ∨ Q := by
  intro hP
  left
  exact hP

-- Exercise 1
theorem week2_or_comm :
    P ∨ Q → Q ∨ P := by
  intro h
  rcases h with hP | hQ
  · right
    exact hP
  · left
    exact hQ

theorem week2_or_elim
    (hPR : P → R)
    (hQR : Q → R) :
    P ∨ Q → R := by
  intro h
  rcases h with hP | hQ
  · exact hPR hP
  · exact hQR hQ

theorem week2_and_or_distrib :
    P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  intro h
  rcases h.2 with hQ | hR
  · left
    exact ⟨h.1, hQ⟩
  · right
    exact ⟨h.1, hR⟩

-- Week 2, Day 2: Universal quantification

variable (α : Type) (A B C : α → Prop)

-- Worked example
example : (∀ x, A x) → ∀ x, A x := by
  intro h x
  exact h x

-- Exercise 1
theorem week2_forall_comp :
    (∀ x, A x → B x) →
    (∀ x, A x) →
    ∀ x, B x := by
  intro h g x
  exact (h x) (g x)

theorem week2_forall_and :
    (∀ x, A x ∧ B x) ↔
    (∀ x, A x) ∧ (∀ x, B x) := by
  constructor
  · intro h
    constructor
    · intro x
      exact (h x).1
    · intro x
      exact (h x).2
  · intro h x
    constructor
    · exact h.1 x
    · exact h.2 x

theorem week2_forall_swap
    {β : Type}
    (C : α → β → Prop) :
    (∀ x y, C x y) → ∀ y x, C x y := by
  intro h y x
  exact (h x) y

-- Week 2, Day 3: Existential quantification

-- Worked example
example : (∃ x, A x) → ∃ x, A x := by
  intro h
  rcases h with ⟨x, hx⟩
  exact ⟨x, hx⟩

-- Exercise 1
theorem week2_exists_map :
    (∀ x, A x → B x) →
    (∃ x, A x) →
    ∃ x, B x := by
  intro h g
  rcases g with ⟨x, gx⟩
  exact ⟨x, (h x) gx⟩

theorem week2_exists_and :
    (∃ x, A x ∧ B x) →
    (∃ x, A x) ∧ (∃ x, B x) := by
  intro h
  rcases h with ⟨x, hx⟩
  constructor
  · exact ⟨x, hx.1⟩
  · exact ⟨x, hx.2⟩

theorem week2_exists_or :
    (∃ x, A x ∨ B x) →
    (∃ x, A x) ∨ (∃ x, B x) := by
  intro h
  rcases h with ⟨x, hx⟩
  rcases hx with hxA | hxB
  · left
    exact ⟨x, hxA⟩
  · right
    exact ⟨x, hxB⟩

-- Week 2, Day 4: Negation and contradiction

-- Worked example
example : ¬ (P ∧ ¬ P) := by
  intro h
  exact h.2 h.1

-- Exercise 1
theorem week2_contrapositive :
    (P → Q) → (¬ Q → ¬ P) := by
  intro h g j
  exact g (h j)

theorem week2_not_or :
    ¬ (P ∨ Q) ↔ (¬ P ∧ ¬ Q) := by
  constructor
  · intro h
    constructor
    · intro g
      apply h
      left
      exact g
    · intro g
      apply h
      right
      exact g
  · intro h g
    rcases g with gP | gQ
    · exact h.1 gP
    · exact h.2 gQ

theorem week2_exists_classification :
    (∀ x, A x → B x ∨ C x) →
    (∃ x, A x) →
    (∃ x, B x) ∨ (∃ x, C x) := by
  intro h g
  rcases g with ⟨x, gx⟩
  rcases (h x) gx with h1 | h2
  · left
    exact ⟨x, h1⟩
  · right
    exact ⟨x, h2⟩


theorem week2_no_counterexample :
    (∀ x, A x → B x) →
    ¬ (∃ x, B x) →
    ¬ (∃ x, A x) := by
  intro h g j
  rcases j with ⟨x, jx⟩
  apply g
  exact ⟨x, (h x) jx⟩


theorem week2_exists_to_forall :
    ((∃ x, A x) → P) ↔
    (∀ x, A x → P) := by
  constructor
  · intro h x g
    exact h ⟨x, g⟩
  · intro h g
    rcases g with ⟨x, gx⟩
    exact (h x) gx

end
