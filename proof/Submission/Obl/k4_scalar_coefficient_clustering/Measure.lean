import Mathlib

namespace Submission.Obl.k4_scalar_coefficient_clustering

open MeasureTheory Set

noncomputable section

/-- The prior mass of short labels pays at most their length times the total prior. -/
theorem incidence_mass_le_long_mass_add {α : Type*} [MeasurableSpace α]
    (ν : Measure α) {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) (δ : ENNReal) :
    (ν.prod volume) E ≤ ν {l | δ ≤ volume {t : ℝ | (l, t) ∈ E}} + δ * ν Set.univ := by
  let L : α → ENNReal := fun l => volume {t : ℝ | (l, t) ∈ E}
  let G : Set α := {l | δ ≤ L l}
  have hL : Measurable L := measurable_measure_prodMk_left hE
  have hG : MeasurableSet G := measurableSet_le measurable_const hL
  have hL1 : ∀ l, L l ≤ 1 := by
    intro l
    calc
      L l ≤ volume (Set.Icc (0 : ℝ) 1) := measure_mono fun t ht => (hunit ht).2
      _ = 1 := by simp
  rw [Measure.prod_apply hE]
  change (∫⁻ l, L l ∂ν) ≤ ν G + δ * ν Set.univ
  calc
    (∫⁻ l, L l ∂ν) ≤ ∫⁻ l, G.indicator (fun _ => (1 : ENNReal)) l + δ ∂ν := by
      apply lintegral_mono
      intro l
      by_cases hl : l ∈ G
      · simpa only [Set.indicator_of_mem hl] using (hL1 l).trans (le_self_add)
      · simpa only [Set.indicator_of_notMem hl, zero_add] using
          (le_of_lt (lt_of_not_ge hl))
    _ = ν G + δ * ν Set.univ := by
      rw [lintegral_add_left (measurable_const.indicator hG),
        lintegral_indicator_const hG, one_mul, lintegral_const]

end
end Submission.Obl.k4_scalar_coefficient_clustering
