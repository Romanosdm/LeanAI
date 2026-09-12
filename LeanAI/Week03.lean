import Mathlib

-- Week 3, Day 1: Equality and rewriting

-- Reflexivity
example (x : ℝ) : x = x := by
  rfl

-- Worked example
example (a b c : ℝ) (h : a = b) :
    a + c = b + c := by
  rw [h]

-- Exercise 1
theorem week3_rewrite_chain
    (a b c : ℝ)
    (hab : a = b)
    (hbc : b = c) :
    a^2 + 1 = c^2 + 1 := by
  rw [hab, hbc]


theorem week3_rewrite_reverse
    (a b c : ℝ)
    (hab : a = b) :
    b + c = a + c := by
  rw [← hab]


theorem week3_rewrite_hypothesis
    (a b : ℝ)
    (hab : a = b)
    (h : a + 1 = 5) :
    b + 1 = 5 := by
  rw [hab] at h
  exact h

theorem week3_function_equality
    {α β : Type}
    (f : α → β)
    (x y : α)
    (h : x = y) :
    f x = f y := by
  rw[h]

-- Week 3, Day 2: Simplification

-- Worked examples
example (x : ℝ) : x + 0 = x := by
  simp

example (P : Prop) : P ∧ True ↔ P := by
  simp

-- Exercise 1
theorem week3_simp_logic
    (P : Prop) :
    (P ∧ True) ∨ False ↔ P := by
  simp

theorem week3_simp_with_hypothesis
    (x y : ℝ)
    (hxy : x = y) :
    (x + 0) * 1 = y := by
  simp [hxy]

theorem week3_simp_at_hypothesis
    (P Q : Prop)
    (h : P ∧ True)
    (hPQ : P → Q) :
    Q := by
  simp only [and_true] at h
  exact hPQ h

theorem week3_simpa_using
    (a b : ℝ)
    (h : a = b) :
    a + 0 = b := by
  simpa using h

theorem week3_simp_function
    (f : ℝ → ℝ)
    (a b : ℝ)
    (h : a = b) :
    f (a + 0) = f b := by
  simp [h]

-- Week 3, Day 3: Numerical normalization

-- Worked examples
example : (17 : ℕ) + 25 = 42 := by
  norm_num

example : (3 : ℝ)^2 + 4^2 = 25 := by
  norm_num

-- Exercise 1
theorem week3_norm_num_fraction :
    (3 : ℚ) / 4 + 5 / 6 = 19 / 12 := by
  norm_num

theorem week3_norm_num_inequality :
    (7 : ℤ)^2 < 50 := by
  norm_num

theorem week3_norm_num_mixed :
    ((3 : ℝ) / 2)^2 + 7 / 4 = 4 := by
  norm_num

theorem week3_impossible_number
    (h : (3 : ℕ) = 4) :
    False := by
  norm_num at h

-- Week 3, Day 4: Polynomial identities and linear arithmetic

-- Worked example
example (x y : ℝ) :
    (x + y)^2 = x^2 + 2*x*y + y^2 := by
  ring

-- Exercise 1
theorem week3_difference_of_squares
    (x y : ℝ) :
    (x - y) * (x + y) = x^2 - y^2 := by
  ring

example (a b c : ℝ)
    (h₁ : a ≤ b)
    (h₂ : b < c) :
    a < c := by
  linarith

theorem week3_linear_system
    (x y : ℝ)
    (h₁ : 2 * x + y = 7)
    (h₂ : x - y = 2) :
    x = 3 := by
  linarith

theorem week3_linarith_bound
    (x y : ℝ)
    (h₁ : x + 2 * y ≤ 10)
    (h₂ : 3 ≤ y) :
    x ≤ 4 := by
  linarith

-- Week 3, Day 5: Even numbers

example (n : ℕ) : Even (2*n) := by
  refine ⟨n, ?_⟩
  ring

theorem week3_even_square
    (n : ℕ)
    (h : Even n) :
    Even (n^2) := by
  rcases h with ⟨k, hk⟩
  refine ⟨2*k^2, ?_⟩
  rw[hk]
  ring

theorem week3_even_add
    (m n : ℕ)
    (hm : Even m)
    (hn : Even n) :
    Even (m + n) := by
  rcases hm with ⟨k, hme⟩
  rcases hn with ⟨l, hne⟩
  refine ⟨k+l, ?_⟩
  rw[hme,hne]
  ring

theorem week3_square_plus_one_positive
    (x : ℝ) :
    0 < x^2 + 1 := by
  have hsq : 0 ≤ x^2 := sq_nonneg x
  linarith
