/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Mathlib.MeasureTheory.Measure.Prod

open Set MeasureTheory

namespace Submission.Lib.K4PolynomialNorming

/-- Integrate uniform section bounds under an originally dominated joint
law. The reference law on starts and controls is kept with its exact mass. -/
theorem dominated_product_section_mass_bound {Ω Y : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) [SFinite μ] (ν : Measure Y) [SFinite ν]
    (P : Measure (Ω × Y)) (K c B : ENNReal) (hP : P ≤ K • μ.prod ν)
    (E : Set (Ω × Y)) (hE : MeasurableSet E)
    (hrow : ∀ ω, c * ν (Prod.mk ω ⁻¹' E) ≤ B) :
    c * P E ≤ K * μ univ * B := by
  have hvol : c * μ.prod ν E ≤ μ univ * B := by
    rw [Measure.prod_apply hE, ← lintegral_const_mul _ (measurable_measure_prodMk_left hE)]
    calc
      _ ≤ ∫⁻ _ : Ω, B ∂μ := lintegral_mono hrow
      _ = _ := by simp [mul_comm]
  calc
    _ ≤ c * (K * μ.prod ν E) := mul_le_mul_of_nonneg_left (hP E) bot_le
    _ = K * (c * μ.prod ν E) := by ac_rfl
    _ ≤ K * (μ univ * B) := mul_le_mul_of_nonneg_left hvol bot_le
    _ = _ := (mul_assoc _ _ _).symm

end Submission.Lib.K4PolynomialNorming
