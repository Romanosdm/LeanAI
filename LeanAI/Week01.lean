import Mathlib

#check Prop
#check True
#check False
#check And
#check Or

section

variable (P Q R : Prop)

example : P → P := by
  intro hP
  exact hP

theorem identity : P → P := by
  intro hP
  exact hP

theorem apply_hypothesis (h : P → Q) : P → Q := by
  intro hP
  exact h hP

-- Day 2: Implications and composition

-- Worked example
example (hPQ : P → Q) (hQR : Q → R) : P → R := by
  intro hP
  exact hQR (hPQ hP)

-- Exercise 1
theorem implication_chain
    (hPQ : P → Q)
    (hQR : Q → R) :
    P → R := by
  intro hP
  exact hQR (hPQ hP)

-- Exercise 2
theorem keep_first : P → Q → P := by
  intro hP hQ
  exact hP

-- Exercise 3
theorem swap_arguments :
    (P → Q → R) → (Q → P → R) := by
  intro h hQ hP
  exact h hP hQ

-- Exercise 4
theorem implication_transitivity :
    (P → Q) → (Q → R) → P → R := by
  intro hPQ hQR hP
  exact hQR (hPQ hP)

-- Day 3: Conjunction

-- Worked example: constructing a conjunction
example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor
  · exact hP
  · exact hQ

-- Exercise 1
theorem and_left : P ∧ Q → P := by
  intro h
  exact h.1

-- Exercise 2
theorem and_right : P ∧ Q → Q := by
  intro h
  exact h.2

-- Exercise 3
theorem week1_and_comm : P ∧ Q → Q ∧ P := by
  intro h
  constructor
  · exact h.2
  · exact h.1

-- Exercise 4
theorem week1_and_assoc :
    (P ∧ Q) ∧ R → P ∧ (Q ∧ R) := by
  intro h
  constructor
  · exact h.1.1
  · constructor
    · exact h.1.2
    · exact h.2

-- Day 4: Logical equivalence

theorem week1_iff_symm :
    (P ↔ Q) → (Q ↔ P) := by
  intro h
  constructor
  · exact h.2
  · exact h.1

theorem week1_and_self :
    P ∧ P ↔ P := by
  constructor
  · intro h
    exact h.1
  · intro h
    constructor
    · exact h
    · exact h

theorem week1_curry :
    ((P ∧ Q) → R) ↔ (P → Q → R) := by
  constructor
  · intro h hP hQ
    exact h ⟨hP, hQ⟩
  · intro h hPQ
    exact (h hPQ.1) hPQ.2

theorem week1_imp_and :
    (P → Q ∧ R) ↔ ((P → Q) ∧ (P → R)) := by
  constructor
  · intro h
    constructor
    · intro hP
      exact (h hP).1
    · intro hP
      exact (h hP).2
  · intro h hP
    exact ⟨(h.1 hP), (h.2 hP)⟩

end
