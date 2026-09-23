import Mathlib

-- Week 5, Day 1: Algebraic structures

section

variable {G : Type*} [Group G]

-- Worked example
example (x : G) : x * 1 = x := by
  simp

-- Exercise 1
theorem week5_mul_inverse
    (x : G) :
    x * x⁻¹ = 1 := by
  simp

theorem week5_inverse_cancel
    (x y : G) :
    x⁻¹ * (x * y) = y := by
  simp

end

section

variable {M : Type*} [Semigroup M]

theorem week5_reassociate
    (a b c d : M) :
    (a * b) * (c * d) = (a * (b * c)) * d := by
    rw [← mul_assoc a b c]
    rw [mul_assoc (a * b) c d]


end

-- Week 5, Day 2: Subgroups

section

variable {G : Type*} [Group G]

-- Worked examples
example (H : Subgroup G) : (1 : G) ∈ H := by
  exact H.one_mem

example (H : Subgroup G) (x : G) (hx : x ∈ H) :
    x⁻¹ ∈ H := by
  exact H.inv_mem hx

-- Exercise 1
theorem week5_subgroup_mul_inv
    (H : Subgroup G)
    (x y : G)
    (hx : x ∈ H)
    (hy : y ∈ H) :
    x * y⁻¹ ∈ H := by
  exact H.mul_mem hx (H.inv_mem hy)

theorem week5_subgroup_conjugate_expression
    (H : Subgroup G)
    (x y : G)
    (hx : x ∈ H)
    (hy : y ∈ H) :
    x * y * x⁻¹ ∈ H := by
  exact H.mul_mem (H.mul_mem hx hy) (H.inv_mem hx)

theorem week5_subgroup_pow
    (H : Subgroup G)
    (x : G)
    (hx : x ∈ H)
    (n : ℕ) :
    x^n ∈ H := by
  exact H.pow_mem hx n


end

-- Week 5, Day 3: Group homomorphisms and kernels

section

variable {G H : Type*} [Group G] [Group H]

-- Worked examples
example (f : G →* H) :
    f 1 = 1 := by
  exact f.map_one

example (f : G →* H) (x y : G) :
    f (x * y) = f x * f y := by
  exact f.map_mul x y

-- Exercise 1
theorem week5_hom_mul_inv
    (f : G →* H)
    (x y : G) :
    f (x * y⁻¹) = f x * (f y)⁻¹ := by
    rw [← f.map_inv y]
    exact f.map_mul x y⁻¹

theorem week5_ker_mul
    (f : G →* H)
    (x y : G)
    (hx : x ∈ f.ker)
    (hy : y ∈ f.ker) :
    x * y ∈ f.ker := by
  exact f.ker.mul_mem hx hy

theorem week5_ker_comp
    {K : Type*} [Group K]
    (f : G →* H)
    (g : H →* K) :
    f.ker ≤ (g.comp f).ker := by
  intro x h
  change g (f x)=1
  rw [h]
  exact g.map_one


end

-- Week 5, Day 4: Reusable lemmas with minimal assumptions

section

variable {M N : Type*} [Monoid M] [Monoid N]

theorem week5_eq_one_of_map_eq_one
    (f : M →* N)
    (hf : Function.Injective f)
    (x : M)
    (hx : f x = 1) :
    x = 1 := by
  apply hf
  rw [f.map_one]
  exact hx

theorem week5_map_eq_one_iff
    (f : M →* N)
    (hf : Function.Injective f)
    (x : M) :
    f x = 1 ↔ x = 1 := by
  constructor
  · intro hx
    exact week5_eq_one_of_map_eq_one f hf x hx
  · intro h
    rw [← f.map_one, h]


theorem week5_hom_pow
    (f : M →* N)
    (x : M)
    (n : ℕ) :
    f (x^n) = (f x)^n := by
  exact f.map_pow x n


end

-- Week 5, Day 5: Kernel and injectivity

section

variable {G H : Type*} [Group G] [Group H]

theorem week5_ker_eq_bot_of_injective
    (f : G →* H)
    (hf : Function.Injective f) :
    f.ker = ⊥ := by
  ext x
  simpa using week5_map_eq_one_iff f hf x


theorem week5_injective_of_ker_eq_bot
    (f : G →* H)
    (hker : f.ker = ⊥) :
    Function.Injective f := by
  intro x y h
  have hxy : f (x * y⁻¹) = 1 := by
   rw [f.map_mul x y⁻¹, h, ← f.map_mul y y⁻¹]
   simp
  have hm : x * y⁻¹ ∈ f.ker := hxy
  have hprod : x * y⁻¹ = 1 := by
   rw [hker] at hm
   exact hm
  calc
  x = (x * y⁻¹) * y := by simp [mul_assoc]
  _ = (1 : G) * y := by rw [hprod]
  _ = y := by simp


theorem week5_injective_iff_ker_eq_bot
    (f : G →* H) :
    Function.Injective f ↔ f.ker = ⊥ := by
  constructor
  ·  intro h
     exact week5_ker_eq_bot_of_injective f h
  · intro h
    exact week5_injective_of_ker_eq_bot f h




end
