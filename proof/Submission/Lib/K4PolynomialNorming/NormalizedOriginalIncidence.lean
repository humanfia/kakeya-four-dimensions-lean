/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4ScalarActualSwitching.BoundedIncidence
import Submission.Lib.K4PolynomialNorming.OriginalIncidenceNormalization

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory ENNReal

namespace Submission.Lib.K4PolynomialNorming

/-- Normalize the original incidence law only once. Its genuine line
marginal and normalized time fibers retain the original-prior short-row
budget, with the original mass denominator displayed. -/
theorem normalized_original_incidence_disintegration {L T : Type*}
    [MeasurableSpace L] [MeasurableSpace T]
    (ν₀ : Measure L) [IsFiniteMeasure ν₀] (τ : Measure T) [IsProbabilityMeasure τ]
    (F : L × T → ENNReal) (hF : Measurable F)
    (H : ENNReal) (hH : H ≠ ∞) (hbound : ∀ z, F z ≤ H)
    (hpositive : 0 < ((ν₀.prod τ).withDensity F) univ) :
    let μ := (ν₀.prod τ).withDensity F
    let P := (μ univ)⁻¹ • μ
    IsProbabilityMeasure P ∧
      ∃ ν : Measure L, IsProbabilityMeasure ν ∧
        ∃ κ : Kernel L T, IsMarkovKernel κ ∧ ν ⊗ₘ κ = P ∧
          (∀ q : ENNReal, 0 < q →
            ∀ l ∈ Submission.Lib.K4Homogenization.durationRetained τ F univ q,
              κ l ≤ (H/q) • τ) ∧
          (∀ q : ENNReal,
            P (Prod.fst ⁻¹' (Submission.Lib.K4Homogenization.durationRetained τ F univ q)ᶜ) ≤
              (μ univ)⁻¹*(q*ν₀ univ)) := by
  dsimp only
  let μ := (ν₀.prod τ).withDensity F
  let P := (μ univ)⁻¹ • μ
  obtain ⟨hfinite,κ,hκ,hjoint,hcap,hshort⟩ :=
    Submission.Lib.K4ScalarActualSwitching.bounded_incidence_disintegration
      ν₀ τ F hF H hH hbound
  letI : IsFiniteMeasure μ := hfinite
  letI : IsMarkovKernel κ := hκ
  obtain ⟨hP,hν,hjointP⟩ := original_incidence_normalization μ κ hjoint hpositive
  refine ⟨hP,(μ univ)⁻¹ • μ.fst,hν,κ,hκ,hjointP,hcap,?_⟩
  · intro q
    change (μ univ)⁻¹*μ _ ≤ (μ univ)⁻¹*(q*ν₀ univ)
    exact mul_le_mul' le_rfl (hshort q)

end Submission.Lib.K4PolynomialNorming
