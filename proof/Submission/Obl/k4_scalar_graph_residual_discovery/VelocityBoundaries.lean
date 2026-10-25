/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file VelocityBoundaries.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set

noncomputable section

def velocityBoundaryBins (ρ β : ℝ) (c : ℤ) : Finset ℤ :=
  {⌊(c : ℝ) * ρ / β⌋, ⌊((c : ℝ) + 1) * ρ / β⌋}

theorem card_velocityBoundaryBins_le_two (ρ β : ℝ) (c : ℤ) :
    (velocityBoundaryBins ρ β c).card ≤ 2 := by
  exact Finset.card_le_two

/-- A fine velocity bin meeting a coarse bin is contained in it unless
it is one of the two endpoint bins. No nesting of the two grids is used. -/
theorem fine_velocity_bin_subset_or_boundary {ρ β : ℝ} (hρ : 0 < ρ) (hβ : 0 < β)
    (c j : ℤ) (hmeet : ∃ v : ℝ, (⌊v / ρ⌋ : ℤ) = c ∧ (⌊v / β⌋ : ℤ) = j) :
    j ∈ velocityBoundaryBins ρ β c ∨
      {v : ℝ | (⌊v / β⌋ : ℤ) = j} ⊆ {v : ℝ | (⌊v / ρ⌋ : ℤ) = c} := by
  classical
  by_cases hj : j ∈ velocityBoundaryBins ρ β c
  · exact Or.inl hj
  right
  obtain ⟨v, hvc, hvj⟩ := hmeet
  have hvc' := Int.floor_eq_iff.mp hvc
  have hvlo : (c : ℝ) * ρ ≤ v := (le_div_iff₀ hρ).mp hvc'.1
  have hvhi : v ≤ ((c : ℝ) + 1) * ρ := ((div_lt_iff₀ hρ).mp hvc'.2).le
  have hlo : ⌊(c : ℝ) * ρ / β⌋ ≤ j := by
    rw [← hvj]
    exact Int.floor_mono (div_le_div_of_nonneg_right hvlo hβ.le)
  have hhi : j ≤ ⌊((c : ℝ) + 1) * ρ / β⌋ := by
    rw [← hvj]
    exact Int.floor_mono (div_le_div_of_nonneg_right hvhi hβ.le)
  have hjlo : j ≠ ⌊(c : ℝ) * ρ / β⌋ := by
    intro he
    exact hj (by simp [velocityBoundaryBins, he])
  have hjhi : j ≠ ⌊((c : ℝ) + 1) * ρ / β⌋ := by
    intro he
    exact hj (by simp [velocityBoundaryBins, he])
  have hloR : (⌊(c : ℝ) * ρ / β⌋ : ℝ) + 1 ≤ (j : ℝ) := by
    exact_mod_cast (by omega : ⌊(c : ℝ) * ρ / β⌋ + 1 ≤ j)
  have hhiR : (j : ℝ) + 1 ≤ (⌊((c : ℝ) + 1) * ρ / β⌋ : ℝ) := by
    exact_mod_cast (by omega : j + 1 ≤ ⌊((c : ℝ) + 1) * ρ / β⌋)
  have hleft := (div_lt_iff₀ hβ).mp (Int.lt_floor_add_one ((c : ℝ) * ρ / β))
  have hright := (le_div_iff₀ hβ).mp (Int.floor_le (((c : ℝ) + 1) * ρ / β))
  intro u hu
  have hu' := Int.floor_eq_iff.mp hu
  have hulo := (le_div_iff₀ hβ).mp hu'.1
  have huhi := (div_lt_iff₀ hβ).mp hu'.2
  apply Int.floor_eq_iff.mpr
  constructor
  · apply (le_div_iff₀ hρ).mpr
    nlinarith
  · apply (div_lt_iff₀ hρ).mpr
    nlinarith

end

end Submission.Obl.k4_scalar_graph_residual_discovery
