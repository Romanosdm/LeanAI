import Mathlib


theorem week7_continuous_add
    (f g : ℝ → ℝ)
    (hf : Continuous f)
    (hg : Continuous g) :
    Continuous (fun x => f x + g x) := by
  exact Continuous.add hf hg

theorem week7_continuous_comp
    (f g : ℝ → ℝ)
    (hf : Continuous f)
    (hg : Continuous g) :
    Continuous (fun x => g (f x)) := by
  exact Continuous.comp hg hf

theorem week7_continuous_square_sum
    (f g : ℝ → ℝ)
    (hf : Continuous f)
    (hg : Continuous g) :
    Continuous (fun x => f x * f x + g x) := by
  have hf2 : Continuous (fun x => f x * f x) := by
    exact Continuous.mul hf hf
  exact Continuous.add hf2 hg

theorem week7_continuous_quadratic :
    Continuous (fun x : ℝ => x * x + 1) := by
  have h1 : Continuous (fun x : ℝ => (1 : ℝ)) := by
    exact continuous_const
  have h2 : Continuous (fun x : ℝ => x) := by
    exact continuous_id
  have h3 : Continuous (fun x : ℝ => x * x) := by
    exact Continuous.mul h2 h2
  exact Continuous.add h3 h1

open Filter

theorem week7_continuous_gives_limit
    (f : ℝ → ℝ)
    (hf : Continuous f)
    (x : ℝ) :
    Filter.Tendsto f (nhds x) (nhds (f x)) := by
  exact hf.tendsto x

theorem week7_tendsto_comp_continuous
    (f g : ℝ → ℝ)
    (x y : ℝ)
    (hf : Filter.Tendsto f (nhds x) (nhds y))
    (hg : Continuous g) :
    Filter.Tendsto (fun z => g (f z)) (nhds x) (nhds (g y)) := by
  have hgy : Filter.Tendsto g (nhds y) (nhds (g y)) := by
    exact week7_continuous_gives_limit g hg y
  exact Filter.Tendsto.comp hgy hf

theorem week7_tendsto_add
    (f g : ℝ → ℝ)
    (x a b : ℝ)
    (hf : Filter.Tendsto f (nhds x) (nhds a))
    (hg : Filter.Tendsto g (nhds x) (nhds b)) :
    Filter.Tendsto (fun z => f z + g z) (nhds x) (nhds (a + b)) := by
  exact Filter.Tendsto.add hf hg

theorem week7_sequence_continuous_comp
    (u : ℕ → ℝ)
    (g : ℝ → ℝ)
    (a : ℝ)
    (hu : Filter.Tendsto u Filter.atTop (nhds a))
    (hg : Continuous g) :
    Filter.Tendsto (fun n => g (u n)) Filter.atTop (nhds (g a)) := by
  have hgy : Filter.Tendsto g (nhds a) (nhds (g a)) := by
    exact week7_continuous_gives_limit g hg a
  exact Filter.Tendsto.comp hgy hu

theorem week7_sequence_add
    (u v : ℕ → ℝ)
    (a b : ℝ)
    (hu : Filter.Tendsto u Filter.atTop (nhds a))
    (hv : Filter.Tendsto v Filter.atTop (nhds b)) :
    Filter.Tendsto (fun n => u n + v n) Filter.atTop (nhds (a + b)) := by
  exact Filter.Tendsto.add hu hv

theorem week7_sequence_limit_unique
    (u : ℕ → ℝ)
    (a b : ℝ)
    (ha : Filter.Tendsto u Filter.atTop (nhds a))
    (hb : Filter.Tendsto u Filter.atTop (nhds b)) :
    a = b := by
  exact tendsto_nhds_unique ha hb

theorem week7_continuousAt_add
    (f g : ℝ → ℝ)
    (a : ℝ)
    (hf : ContinuousAt f a)
    (hg : ContinuousAt g a) :
    ContinuousAt (fun x => f x + g x) a := by
  exact ContinuousAt.add hf hg

theorem week7_continuousAt_comp
    (f g : ℝ → ℝ)
    (a : ℝ)
    (hf : ContinuousAt f a)
    (hg : ContinuousAt g (f a)) :
    ContinuousAt (fun x => g (f x)) a := by
  exact ContinuousAt.comp hg hf

theorem week7_continuous_of_continuousAt
    (f : ℝ → ℝ)
    (h : ∀ x : ℝ, ContinuousAt f x) :
    Continuous f := by
  apply (continuous_iff_continuousAt).2
  exact h

theorem week7_continuous_add_from_points
    (f g : ℝ → ℝ)
    (hf : ∀ x : ℝ, ContinuousAt f x)
    (hg : ∀ x : ℝ, ContinuousAt g x) :
    Continuous (fun x => f x + g x) := by
  have hf1 : Continuous f := by
    exact (continuous_iff_continuousAt).2 hf
  have hg1 : Continuous g := by
    exact (continuous_iff_continuousAt).2 hg
  exact Continuous.add hf1 hg1

theorem week7_one_div_nat_tendsto_zero :
    Filter.Tendsto
      (fun n : ℕ => (1 : ℝ) / (n : ℝ))
      Filter.atTop
      (nhds (0 : ℝ)) := by
  exact tendsto_one_div_atTop_nhds_zero_nat

theorem week7_const_div_nat_tendsto_zero
    (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => c / (n : ℝ))
      Filter.atTop
      (nhds (0 : ℝ)) := by
  exact tendsto_const_div_atTop_nhds_zero_nat c

theorem week7_three_add_const_div_tendsto
    (c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => (3 : ℝ) + c / (n : ℝ))
      Filter.atTop
      (nhds (3 : ℝ)) := by
  have h : Filter.Tendsto
      (fun n : ℕ => c / (n : ℝ))
      Filter.atTop
      (nhds (0 : ℝ)) := by
    exact week7_const_div_nat_tendsto_zero c
  have g : Filter.Tendsto
      (fun n : ℕ => (3 : ℝ))
      Filter.atTop
      (nhds (3 : ℝ)) := by
    exact tendsto_const_nhds
  simpa only [add_zero] using Filter.Tendsto.add g h

theorem week7_add_const_div_tendsto
    (a c : ℝ) :
    Filter.Tendsto
      (fun n : ℕ => a + c / (n : ℝ))
      Filter.atTop
      (nhds a) := by
  have h : Filter.Tendsto
      (fun n : ℕ => c / (n : ℝ))
      Filter.atTop
      (nhds (0 : ℝ)) := by
    exact week7_const_div_nat_tendsto_zero c
  have g : Filter.Tendsto
      (fun n : ℕ => (a : ℝ))
      Filter.atTop
      (nhds (a : ℝ)) := by
    exact tendsto_const_nhds
  simpa only [add_zero] using Filter.Tendsto.add g h
