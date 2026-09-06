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

end
