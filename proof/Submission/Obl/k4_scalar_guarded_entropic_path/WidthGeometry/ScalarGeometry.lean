/-
Adapted from this LOT tree, obligation o134, session x0438, commit 2e990309978b,
Submission/Obl/k4_scalar_guarded_tangent_obstruction/ScalarGeometry.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry.Defs

namespace Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry

noncomputable def neighboringVelocityBins (δ center : ℝ) : Finset ℤ :=
  Finset.Icc (⌊center / δ⌋ - 1) (⌊center / δ⌋ + 1)

theorem mem_neighboringVelocityBins {δ center velocity : ℝ}
    (hδ : 0 < δ) (hclose : |velocity - center| ≤ δ) :
    (⌊velocity / δ⌋ : ℤ) ∈ neighboringVelocityBins δ center := by
  have hlo : center / δ - 1 ≤ velocity / δ := by
    have := (abs_le.mp hclose).1
    apply (le_div_iff₀ hδ).2
    have hcancel : center / δ * δ = center := div_mul_cancel₀ _ hδ.ne'
    nlinarith only [this, hcancel]
  have hhi : velocity / δ ≤ center / δ + 1 := by
    have := (abs_le.mp hclose).2
    apply (div_le_iff₀ hδ).2
    have hcancel : center / δ * δ = center := div_mul_cancel₀ _ hδ.ne'
    nlinarith only [this, hcancel]
  exact Finset.mem_Icc.mpr ⟨by simpa only [Int.floor_sub_one] using Int.floor_mono hlo,
    by simpa only [Int.floor_add_one] using Int.floor_mono hhi⟩

theorem card_neighboringVelocityBins (δ center : ℝ) :
    (neighboringVelocityBins δ center).card = 3 := by
  rw [neighboringVelocityBins, Int.card_Icc]
  have h : (⌊center / δ⌋ + 1 + 1 - (⌊center / δ⌋ - 1) : ℤ) = 3 := by ring
  rw [h]
  rfl

end Submission.Obl.k4_scalar_guarded_entropic_path.WidthGeometry
