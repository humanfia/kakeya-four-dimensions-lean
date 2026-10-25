/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarHeavyGroups/CellDuration.lean at aca48c1.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit ccf90c32bd4af25c1ba009c960359aada67a01a5,
Submission/Obl/k4_scalar_mesh_projection/CellDuration.lean.
-/

import Submission.Lib.K4ContinuousKakeya.Incidence

namespace Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Set MeasureTheory
open scoped NNReal ENNReal

/-- Rounding the normalized time coordinate costs only the actual cell
width plus twice the rounding error in the ORIGINAL time measure. -/
theorem rounded_time_cell_prior_cap {α : Type*} [MeasurableSpace α]
    (θ : Measure α) [SFinite θ] (inc : Measure (α × ℝ)) (K B : ℝ≥0)
    (hinc : inc ≤ K • θ.prod volume)
    (S : Set (α × ℝ)) (hS : MeasurableSet S) (Λ : Set α) (hΛ : MeasurableSet Λ)
    (hSΛ : ∀ ω ∈ S, ω.1 ∈ Λ)
    (f : α × ℝ → ℝ) (s h c ξ error : ℝ)
    (hh : 0 < h) (_hξ : 0 ≤ ξ) (_he : 0 ≤ error)
    (hB : h * (ξ + 2 * error) ≤ (B : ℝ))
    (htime : ∀ ω ∈ S, |f ω - (ω.2 - s) / h| ≤ error)
    (hcell : ∀ ω ∈ S, c ≤ f ω ∧ f ω ≤ c + ξ) :
    (inc.restrict S).map Prod.fst ≤ (K * B) • θ.restrict Λ := by
  apply Submission.Lib.K4ContinuousKakeya.map_fst_restrict_le θ inc K B hinc S hS Λ hΛ hSΛ
  intro l hl
  have hsub : {t : ℝ | (l, t) ∈ S} ⊆
      Icc (s + h * (c - error)) (s + h * (c + ξ + error)) := by
    intro t ht
    have ha := abs_le.mp (htime (l, t) ht)
    obtain ⟨hc0, hc1⟩ := hcell (l, t) ht
    have hlo : c - error ≤ (t - s) / h := by linarith
    have hup : (t - s) / h ≤ c + ξ + error := by linarith
    have hlo' := (le_div_iff₀ hh).mp hlo
    have hup' := (div_le_iff₀ hh).mp hup
    constructor <;> nlinarith
  calc
    _ ≤ volume (Icc (s + h * (c - error)) (s + h * (c + ξ + error))) := measure_mono hsub
    _ = ENNReal.ofReal (h * (ξ + 2 * error)) := by
      rw [Real.volume_Icc]
      congr 1
      ring
    _ ≤ (B : ℝ≥0∞) := by
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hB

end Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
