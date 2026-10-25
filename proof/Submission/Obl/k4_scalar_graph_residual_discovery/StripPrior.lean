/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file StripPrior.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.CoefficientZoom
import Submission.Obl.k4_initial_horizon_bound.Duration

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Obl.k4_initial_horizon_bound

/-- A long entry in the earlier law and an original-mass floor in the
final law control the unchanged trajectory prior by the final entry mass. -/
theorem long_entry_prior_cap {α : Type*} [MeasurableSpace α]
    (θ : Measure α) [SFinite θ] {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (Λ : Set α) (hΛ : MeasurableSet Λ) (a δ U old current : ℝ≥0∞)
    (ha₀ : a ≠ 0) (hat : a ≠ ∞) (hδ₀ : δ ≠ 0) (hδt : δ ≠ ∞)
    (hlong : ∀ l ∈ Λ, a ≤ incidenceDuration E l)
    (hinc : (θ.prod volume) E ≤ U * old) (hfloor : δ * old ≤ current) :
    θ Λ ≤ (U / a / δ) * current := by
  have hlong' := retained_duration_prior_bound θ hE hΛ MeasurableSet.univ a
    (fun l hl => hlong l hl.1)
  rw [Measure.restrict_univ, duration_withDensity_apply θ hE hΛ] at hlong'
  have hmass : a * θ Λ ≤ U * old :=
    hlong'.trans ((measure_mono inter_subset_left).trans hinc)
  have hprior : θ Λ ≤ (U / a) * old := by
    calc
      θ Λ = a⁻¹ * (a * θ Λ) := (ENNReal.inv_mul_cancel_left ha₀ hat).symm
      _ ≤ a⁻¹ * (U * old) := mul_le_mul_right hmass _
      _ = _ := by rw [div_eq_mul_inv]; ac_rfl
  exact Zoom.cap_of_palette_floor hδ₀ hδt hprior hfloor

/-- The prior estimate in the real form required by planar strip filling.
The duration floor is a*rho; it refers to the earlier entry, while its
mass floor refers to the final entry. -/
theorem long_strip_prior_bound {α : Type*} [MeasurableSpace α]
    (θ : Measure α) [SFinite θ] {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (Λ : Set α) (hΛ : MeasurableSet Λ) {a ρ δ H K : ℝ}
    (ha : 0 < a) (hρ : 0 < ρ) (hδ : 0 < δ) (hH : 0 ≤ H)
    (old current : ℝ≥0∞) (hcurrent : current ≠ ∞)
    (hlong : ∀ l ∈ Λ, ENNReal.ofReal (a * ρ) ≤ incidenceDuration E l)
    (hinc : (θ.prod volume) E ≤ ENNReal.ofReal H * old)
    (hfloor : ENNReal.ofReal δ * old ≤ current) (hbudget : H / (a * δ) ≤ K) :
    (θ Λ).toReal ≤ K * current.toReal / ρ := by
  have h := long_entry_prior_cap θ hE Λ hΛ (ENNReal.ofReal (a * ρ))
    (ENNReal.ofReal δ) (ENNReal.ofReal H) old current
    (by positivity) ENNReal.ofReal_ne_top (by positivity) ENNReal.ofReal_ne_top hlong hinc hfloor
  have hreal := ENNReal.toReal_mono (by finiteness) h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_ofReal hH, ENNReal.toReal_ofReal (mul_pos ha hρ).le,
    ENNReal.toReal_ofReal hδ.le] at hreal
  calc
    (θ Λ).toReal ≤ (H / (a * ρ) / δ) * current.toReal := hreal
    _ = (H / (a * δ)) * current.toReal / ρ := by field_simp
    _ ≤ K * current.toReal / ρ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbudget ENNReal.toReal_nonneg) hρ.le

end Submission.Obl.k4_scalar_graph_residual_discovery
