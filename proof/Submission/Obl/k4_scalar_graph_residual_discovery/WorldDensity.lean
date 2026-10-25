/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file WorldDensity.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.CoefficientZoom

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

noncomputable section

/-- Normalizing the FULL coefficient-bin prior leaves the original
product incidence measure on every later subset of that bin. -/
theorem prior_prod_apply (θ : Measure ScalarLine) [SFinite θ]
    (ρ : ℝ) (q : Fin 5 → ℤ) {E : Set ScalarIncidence} (hE : MeasurableSet E)
    (hblock : ∀ p ∈ E, cell ρ p.1.2 = q) :
    ((prior θ ρ q).prod volume) E =
      (θ {l | cell ρ l.2 = q})⁻¹ * (θ.prod volume) E := by
  rw [prior, Measure.prod_smul_left, Measure.smul_apply,
    Measure.restrict_prod_eq_prod_univ, Measure.restrict_apply hE]
  have hsub : E ⊆ {l : ScalarLine | cell ρ l.2 = q} ×ˢ (univ : Set ℝ) :=
    fun p hp => ⟨hblock p hp, mem_univ _⟩
  rw [inter_eq_left.mpr hsub]
  rfl

/-- A dense world is measured against its unchanged full-bin prior.
Only the original incidence-density ceiling is used in the conversion. -/
theorem prior_product_dense (θ : Measure ScalarLine) [IsFiniteMeasure θ]
    (μ : Measure ScalarIncidence) {H δ ρ : ℝ} (hH : 0 < H)
    (hμ : μ ≤ ENNReal.ofReal H • θ.prod volume) (q : Fin 5 → ℤ)
    (hpositive : θ {l | cell ρ l.2 = q} ≠ 0)
    {E : Set ScalarIncidence} (hE : MeasurableSet E)
    (hblock : ∀ p ∈ E, cell ρ p.1.2 = q)
    (hmass : ENNReal.ofReal δ * θ {l | cell ρ l.2 = q} ≤ μ E) :
    ENNReal.ofReal (δ / H) ≤ ((prior θ ρ q).prod volume) E := by
  let P := θ {l | cell ρ l.2 = q}
  have hPt : P ≠ ∞ := measure_ne_top θ _
  have hμE : μ E ≤ ENNReal.ofReal H * (θ.prod volume) E := by
    simpa only [Measure.smul_apply, smul_eq_mul] using hμ E
  have hnorm : ENNReal.ofReal δ ≤ ENNReal.ofReal H * (P⁻¹ * (θ.prod volume) E) := by
    calc
      ENNReal.ofReal δ = ENNReal.ofReal δ * (P⁻¹ * P) := by
        rw [ENNReal.inv_mul_cancel hpositive hPt, mul_one]
      _ = P⁻¹ * (ENNReal.ofReal δ * P) := by ring
      _ ≤ P⁻¹ * (ENNReal.ofReal H * (θ.prod volume) E) :=
        mul_le_mul_right (hmass.trans hμE) _
      _ = _ := by ring
  rw [prior_prod_apply θ ρ q hE hblock, ENNReal.ofReal_div_of_pos hH]
  exact (ENNReal.div_le_iff' (by positivity) ENNReal.ofReal_ne_top).mpr hnorm

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
