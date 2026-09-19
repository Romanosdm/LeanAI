import Mathlib

open Set Function

-- Week 4, Day 1: Sets and membership

section

variable {α : Type}
variable (s t u : Set α)

-- Worked example
example : s ⊆ s := by
  intro x hx
  exact hx

-- Exercise 1
theorem week4_inter_subset_left :
    s ∩ t ⊆ s := by
  intro x hx
  exact hx.1

theorem week4_subset_trans
    (hst : s ⊆ t)
    (htu : t ⊆ u) :
    s ⊆ u := by
  intro x h
  exact htu (hst h)

theorem week4_setbuilder_subset
    (A B : α → Prop)
    (h : ∀ x, A x → B x) :
    {x | A x} ⊆ {x | B x} := by
  intro x
  exact h x

-- Week 4, Day 2: Set extensionality

example : s ∩ t = t ∩ s := by
  ext x
  simp [and_comm]


theorem week4_union_comm :
    s ∪ t = t ∪ s := by
  ext x
  simp [or_comm]

theorem week4_union_assoc :
    (s ∪ t) ∪ u = s ∪ (t ∪ u) := by
  ext x
  simp [or_assoc]

theorem week4_inter_distrib_union :
    s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) := by
  ext x
  simp [and_or_left]

theorem week4_inter_complement :
    s ∩ sᶜ = ∅ := by
  ext x
  simp

-- Week 4, Day 3: Images and preimages

variable {β : Type}

-- Worked example
example (f : α → β) (v : Set β) :
    f ⁻¹' v = {x | f x ∈ v} := by
  rfl

-- Exercise 1
theorem week4_preimage_inter
    (f : α → β)
    (v w : Set β) :
    f ⁻¹' (v ∩ w) = (f ⁻¹' v) ∩ (f ⁻¹' w) := by
  ext x
  simp

theorem week4_image_inter_subset
    (f : α → β) :
    f '' (s ∩ t) ⊆ (f '' s) ∩ (f '' t) := by
  intro y hy
  rcases hy with ⟨x, hx, hfx⟩
  constructor
  · exact ⟨x, hx.1, hfx⟩
  · exact ⟨x, hx.2, hfx⟩

theorem week4_image_comp
    {γ : Type}
    (f : α → β)
    (g : β → γ) :
    (g ∘ f) '' s = g '' (f '' s) := by
  ext x
  constructor
  · intro h
    rcases h with ⟨y, hy, hgf⟩
    refine ⟨f y, ?_, ?_⟩
    · exact ⟨y, hy, rfl⟩
    · exact hgf
  · intro h
    rcases h with ⟨z, hz, hg⟩
    rcases hz with ⟨y, hy, hf⟩
    refine ⟨y, hy, ?_⟩
    change g (f y) = x
    rw [hf, hg]


-- Week 4, Day 4: Injective and surjective functions

theorem week4_injective_comp
    {β γ : Type}
    (f : α → β)
    (g : β → γ)
    (hf : Function.Injective f)
    (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  intro x y h
  exact hf (hg h)

theorem week4_surjective_comp
    {β γ : Type}
    (f : α → β)
    (g : β → γ)
    (hf : Function.Surjective f)
    (hg : Function.Surjective g) :
    Function.Surjective (g ∘ f) := by
  intro z
  rcases hg z with ⟨y, hy⟩
  rcases hf y with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  rw [← hy,← hx]
  rfl

theorem week4_left_inverse_injective
    {β : Type}
    (f : α → β)
    (g : β → α)
    (h : Function.LeftInverse g f) :
    Function.Injective f := by
  intro x y j
  rw [← (h x), ← (h y), j]

theorem week4_right_inverse_surjective
    {β : Type}
    (f : α → β)
    (g : β → α)
    (h : Function.RightInverse g f) :
    Function.Surjective f := by
  intro y
  refine ⟨g y, ?_⟩
  exact h y

theorem week4_bijective_of_inverse
    {β : Type}
    (f : α → β)
    (g : β → α)
    (hleft : Function.LeftInverse g f)
    (hright : Function.RightInverse g f) :
    Function.Bijective f := by
  constructor
  · exact week4_left_inverse_injective f g hleft
  · exact week4_right_inverse_surjective f g hright

theorem week4_preimage_image_of_injective
    {β : Type}
    (f : α → β)
    (hf : Function.Injective f) :
    f ⁻¹' (f '' s) = s := by
  ext x
  constructor
  · intro h
    rcases h with ⟨y, j, k⟩
    rw [←(hf k)]
    exact j
  · intro h
    exact ⟨x, h, rfl⟩

end
