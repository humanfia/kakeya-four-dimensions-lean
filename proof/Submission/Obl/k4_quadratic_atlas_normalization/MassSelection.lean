import Mathlib

namespace Submission.Obl.k4_quadratic_atlas_normalization

open Set MeasureTheory Filter

/-- The finite pigeonhole principle in extended nonnegative mass. -/
theorem exists_mass_ge_average {V : Type*} (s : Finset V) (f : V → ENNReal)
    (m : ℝ) (hs : s.Nonempty) (h : ENNReal.ofReal m ≤ ∑ v ∈ s, f v) :
    ∃ v ∈ s, ENNReal.ofReal (m / (s.card : ℝ)) ≤ f v := by
  classical
  by_contra! hn
  have hlt := ENNReal.sum_lt_sum_of_nonempty hs hn
  have heq : (∑ _v ∈ s, ENNReal.ofReal (m / (s.card : ℝ))) = ENNReal.ofReal m := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    congr 1
    exact mul_div_cancel₀ m (Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hs))
  rw [heq] at hlt
  exact (not_lt_of_ge h) hlt

/-- A single common bin retains a logarithmic fraction without duplicating charts. -/
theorem exists_common_bin_mass {X ι V : Type*} [MeasurableSpace X] [Fintype ι]
    (ν : ι → Measure X) (w : ι → ENNReal) (F : ι → Set X)
    (s : Finset V) (G : V → ι → Set X) (m : ℝ) (hs : s.Nonempty)
    (hcover : ∀ b, F b ⊆ ⋃ v ∈ s, G v b)
    (hmass : ENNReal.ofReal m ≤ ∑ b, w b * ν b (F b)) :
    ∃ v ∈ s, ENNReal.ofReal (m / (s.card : ℝ)) ≤ ∑ b, w b * ν b (G v b) := by
  classical
  apply exists_mass_ge_average s (fun v => ∑ b, w b * ν b (G v b)) m hs
  apply hmass.trans
  calc
    _ ≤ ∑ b, w b * ∑ v ∈ s, ν b (G v b) := by
      apply Finset.sum_le_sum
      intro b _
      gcongr
      exact (measure_mono (hcover b)).trans (measure_biUnion_finset_le s (fun v => G v b))
    _ = ∑ v ∈ s, ∑ b, w b * ν b (G v b) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm

/-- A cover by retained and deleted events gives the expected mass inequality. -/
theorem weighted_mass_le_retained_add_deleted {X ι : Type*}
    [MeasurableSpace X] [Fintype ι]
    (ν : ι → Measure X) (w : ι → ENNReal) (F G D : ι → Set X)
    (hcover : ∀ b, F b ⊆ G b ∪ D b) :
    ∑ b, w b * ν b (F b) ≤
      (∑ b, w b * ν b (G b)) + ∑ b, w b * ν b (D b) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  rw [← mul_add]
  gcongr
  exact (measure_mono (hcover b)).trans (measure_union_le _ _)

/-- Removing at most half the original mass leaves the other half. -/
theorem retain_half_mass (mass retained deleted : ENNReal) (m : ℝ)
    (hm : 0 ≤ m) (hlower : ENNReal.ofReal m ≤ mass)
    (hcover : mass ≤ retained + deleted)
    (hdeleted : deleted ≤ ENNReal.ofReal (m / 2)) :
    ENNReal.ofReal (m / 2) ≤ retained := by
  have heq : ENNReal.ofReal (m / 2) + ENNReal.ofReal (m / 2) = ENNReal.ofReal m := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1
    ring
  apply ENNReal.le_of_add_le_add_right ENNReal.ofReal_ne_top
  rw [heq]
  exact hlower.trans (hcover.trans (add_le_add le_rfl hdeleted))

/-- One of two monotone alternatives occurs cofinally at every precision. -/
theorem frequently_binary_choice (P Q : ℝ → ℕ → Prop)
    (hP : ∀ ε ε', 0 < ε → ε ≤ ε' → ∀ k, P ε k → P ε' k)
    (hQ : ∀ ε ε', 0 < ε → ε ≤ ε' → ∀ k, Q ε k → Q ε' k)
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, P ε k ∨ Q ε k) :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, P ε k) ∨
      (∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, Q ε k) := by
  classical
  by_cases hp : ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, P ε k
  · exact Or.inl hp
  right
  push Not at hp
  obtain ⟨ε₀, hε₀, hnot⟩ := hp
  have hnot' : ∀ᶠ k in atTop, ¬ P ε₀ k := by simpa using hnot
  intro ε hε
  have hmin : 0 < min ε ε₀ := lt_min hε hε₀
  apply ((h (min ε ε₀) hmin).and_eventually hnot').mono
  intro k hk
  rcases hk.1 with hp | hq
  · exact False.elim (hk.2 (hP _ _ hmin (min_le_right _ _) k hp))
  · exact hQ _ _ hmin (min_le_left _ _) k hq

end Submission.Obl.k4_quadratic_atlas_normalization
