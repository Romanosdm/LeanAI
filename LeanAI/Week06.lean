import Mathlib

section

variable {K V : Type*}
variable [Field K] [AddCommGroup V] [Module K V]

-- Worked example
example (a : K) (x y : V) :
    a • (x + y) = a • x + a • y := by
  exact smul_add a x y

-- Exercise 1
theorem week6_add_smul
    (a b : K) (x : V) :
    (a + b) • x = a • x + b • x := by
  exact add_smul a b x

theorem week6_one_smul
    (x : V) :
    (1 : K) • x = x := by
  exact one_smul K x

theorem week6_smul_sub
    (a : K) (x y : V) :
    a • (x - y) = a • x - a • y := by
  exact smul_sub a x y


end

-- Week 6, Day 2: Submodules and span

section

variable {K V : Type*}
variable [Field K] [AddCommGroup V] [Module K V]

-- Worked example
example (S : Submodule K V) : (0 : V) ∈ S := by
  exact S.zero_mem

-- Exercise 1
theorem week6_submodule_add
    (S : Submodule K V)
    (x y : V)
    (hx : x ∈ S)
    (hy : y ∈ S) :
    x + y ∈ S := by
  exact S.add_mem hx hy

theorem week6_submodule_smul
    (S : Submodule K V)
    (a : K) (x : V)
    (hx : x ∈ S) :
    a • x ∈ S := by
  exact S.smul_mem a hx

theorem week6_span_mono
    (s t : Set V)
    (hst : s ⊆ t) :
    Submodule.span K s ≤ Submodule.span K t := by
  exact Submodule.span_mono hst

theorem week6_mem_span
    (s : Set V)
    (x : V)
    (hx : x ∈ s) :
    x ∈ Submodule.span K s := by
  exact Submodule.subset_span hx

theorem week6_linear_combination_mem_span
    (s : Set V)
    (x y : V)
    (a b : K)
    (hx : x ∈ s)
    (hy : y ∈ s) :
    a • x + b • y ∈ Submodule.span K s := by
  have hxnew : x ∈ Submodule.span K s := by
    exact  Submodule.subset_span hx
  have hynew : y ∈ Submodule.span K s := by
    exact  Submodule.subset_span hy
  have hax : a • x ∈ Submodule.span K s := by
    exact (Submodule.span K s).smul_mem a hxnew
  have hby : b • y ∈ Submodule.span K s := by
    exact (Submodule.span K s).smul_mem b hynew
  exact (Submodule.span K s).add_mem hax hby

end

-- Week 6, Day 3: Linear maps

section

variable {K V W : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

-- Worked example
example (f : V →ₗ[K] W) (x y : V) :
    f (x + y) = f x + f y := by
  exact f.map_add x y

-- Exercise 1
theorem week6_linear_map_zero
    (f : V →ₗ[K] W) :
    f 0 = 0 := by
  exact f.map_zero

theorem week6_ker_add
    (f : V →ₗ[K] W)
    (x y : V)
    (hx : x ∈ LinearMap.ker f)
    (hy : y ∈ LinearMap.ker f) :
    x + y ∈ LinearMap.ker f := by
  exact (LinearMap.ker f).add_mem hx hy

theorem week6_ker_smul
    (f : V →ₗ[K] W)
    (a : K) (x : V)
    (hx : x ∈ LinearMap.ker f) :
    a • x ∈ LinearMap.ker f := by
  exact week6_submodule_smul (LinearMap.ker f) a x hx

theorem week6_map_mem_range
    (f : V →ₗ[K] W)
    (x : V) :
    f x ∈ LinearMap.range f := by
  refine ⟨x, ?_⟩
  rfl

theorem week6_ker_comp
    {U : Type*}
    [AddCommGroup U] [Module K U]
    (f : V →ₗ[K] W)
    (g : W →ₗ[K] U) :
    LinearMap.ker f ≤ LinearMap.ker (g.comp f) := by
  intro x h
  change g (f x)=0
  rw [h]
  exact g.map_zero

end

-- Week 6, Day 4: Linear independence

section

variable {K V ι : Type*}
variable [Field K] [AddCommGroup V] [Module K V]

theorem week6_independent_injective
    (v : ι → V)
    (hv : LinearIndependent K v) :
    Function.Injective v := by
  exact hv.injective

theorem week6_independent_ne_zero
    (v : ι → V)
    (hv : LinearIndependent K v)
    (i : ι) :
    v i ≠ 0 := by
  exact hv.ne_zero i

theorem week6_independent_distinct
    (v : ι → V)
    (hv : LinearIndependent K v)
    (i j : ι)
    (hij : i ≠ j) :
    v i ≠ v j := by
  intro h
  have heq : i=j := by
    exact hv.injective h
  exact hij heq

theorem week6_independent_subfamily
    {κ : Type*}
    (v : ι → V)
    (hv : LinearIndependent K v)
    (e : κ → ι)
    (he : Function.Injective e) :
    LinearIndependent K (v ∘ e) := by
  exact LinearIndependent.comp hv e he



end

-- Week 6, Day 5: Kernel and injectivity

section

variable {K V W : Type*}
variable [Field K]
variable [AddCommGroup V] [Module K V]
variable [AddCommGroup W] [Module K W]

theorem week6_ker_eq_bot_of_injective
    (f : V →ₗ[K] W)
    (hf : Function.Injective f) :
    LinearMap.ker f = ⊥ := by
  ext x
  constructor
  · intro hx
    change x = 0
    change f x =0  at hx
    apply hf
    simpa only [f.map_zero] using hx
  · intro hx
    change x = 0 at hx
    subst x
    exact (LinearMap.ker f).zero_mem

theorem week6_injective_of_ker_eq_bot
    (f : V →ₗ[K] W)
    (hker : LinearMap.ker f = ⊥) :
    Function.Injective f := by
  intro x y h
  have h1 : f (x - y) = 0 := by
    rw [f.map_sub x y, h, ← f.map_sub y y]
    simp
  have h2 : x-y ∈ f.ker := h1
  have hdiff : x - y = 0 := by
    rw [hker] at h2
    exact h2
  calc
  x = (x - y) + y := by simp
  _ = (0 : V) + y := by rw [hdiff]
  _ = y := by simp


theorem week6_injective_iff_ker_eq_bot
    (f : V →ₗ[K] W) :
    Function.Injective f ↔ LinearMap.ker f = ⊥ := by
  constructor
  · intro h
    exact week6_ker_eq_bot_of_injective f h
  · intro h
    exact week6_injective_of_ker_eq_bot f h


end
