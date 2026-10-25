/- Adapted from this LOT tree, o040, session x0115, commit 9f7e9a910e7de423611a55b624313eab3641558f,
   Submission/Obl/k4_matching_refinement_exponent/RecordMeasurability.lean. -/
import Mathlib

open MeasureTheory

namespace Submission.Obl.k4_matching_cofinal_palette_selection

/-- Lookup at a dyadic time center is measurable even for arbitrary original
functions: the center and the arm index take only countably many values. -/
theorem measurable_dyadic_jet_bin (n h j : ℕ) (f : Fin n → ℝ → ℝ) (scale : ℝ) :
    Measurable (fun p : Fin n × ℝ =>
      Int.floor (scale * iteratedDeriv j (f p.1)
        (((Int.floor (p.2 * (2 : ℝ) ^ h) : ℝ) + 1 / 2) / (2 : ℝ) ^ h))) := by
  let lookup : Fin n × ℤ → ℤ := fun p =>
    Int.floor (scale * iteratedDeriv j (f p.1)
      (((p.2 : ℝ) + 1 / 2) / (2 : ℝ) ^ h))
  have hbin : Measurable (fun p : Fin n × ℝ => (p.1, Int.floor (p.2 * (2 : ℝ) ^ h))) := by
    fun_prop
  exact (measurable_of_countable lookup).comp hbin

/-- The two-arm jet-bin lookup on the matching event space. -/
theorem measurable_two_arm_jet_bins (n₁ n₂ h j : ℕ)
    (f₁ : Fin n₁ → ℝ → ℝ) (f₂ : Fin n₂ → ℝ → ℝ) (scale : ℝ) :
    Measurable (fun p : (Fin n₁ × Fin n₂) × ℝ =>
      (Int.floor (scale * iteratedDeriv j (f₁ p.1.1)
        (((Int.floor (p.2 * (2 : ℝ) ^ h) : ℝ) + 1 / 2) / (2 : ℝ) ^ h)),
       Int.floor (scale * iteratedDeriv j (f₂ p.1.2)
        (((Int.floor (p.2 * (2 : ℝ) ^ h) : ℝ) + 1 / 2) / (2 : ℝ) ^ h)))) := by
  exact ((measurable_dyadic_jet_bin n₁ h j f₁ scale).comp
    (by fun_prop : Measurable (fun p : (Fin n₁ × Fin n₂) × ℝ => (p.1.1, p.2)))).prodMk
    ((measurable_dyadic_jet_bin n₂ h j f₂ scale).comp
      (by fun_prop : Measurable (fun p : (Fin n₁ × Fin n₂) × ℝ => (p.1.2, p.2))))

end Submission.Obl.k4_matching_cofinal_palette_selection
