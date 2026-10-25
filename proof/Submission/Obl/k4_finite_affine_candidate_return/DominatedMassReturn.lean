-- Adapted from this LOT tree, o232 `k4_finite_positive_prepared_models`, session x0807,
-- branch x0807 at commit 96b53fe05c6301b6463738f96ea23d9c511248b2.
-- Source: Submission/Obl/k4_finite_positive_prepared_models/DominatedMassReturn.lean (namespace renamed to `Submission.Obl.k4_finite_affine_candidate_return`).
import Submission.Obl.k4_finite_affine_candidate_return.MassReturn

namespace Submission.Obl.k4_finite_affine_candidate_return

open MeasureTheory

noncomputable section

/-- An explicitly dominated native law returns its event floor to the
full original prior, paying exactly its domination constant. The parent
mass still cancels and the original time factor is restored. -/
theorem dominated_muE_floor_return_mono
    {α : Type} [MeasurableSpace α]
    (ν : Measure α) (A₀ A : Set α)
    (hA : MeasurableSet A) (hsub : A ⊆ A₀) (h0 : ν A₀ ≠ 0) (hT : ν A₀ ≠ ⊤)
    (t₀ q : ℝ) (hq : 0 < q) (S X Y : Set (α × ℝ)) (hX : MeasurableSet X)
    (hXY : tnorm t₀ q ⁻¹' X ∩ S ⊆ Y)
    (ρ : Measure (α × ℝ)) (J c : ENNReal) (hJ0 : J ≠ 0) (hJT : J ≠ ⊤)
    (hρ : ρ ≤ J • muE ν A₀ t₀ q S)
    (hfloor : c * nuE ν A₀ A ≤ ρ X) :
    ENNReal.ofReal q * (J⁻¹ * c) * ν A ≤ (ν.prod volume) Y := by
  apply muE_floor_return_mono ν A₀ A hA hsub h0 hT t₀ q hq S X Y hX hXY
  calc
    (J⁻¹ * c) * nuE ν A₀ A = J⁻¹ * (c * nuE ν A₀ A) := by ring
    _ ≤ J⁻¹ * ρ X := mul_le_mul' le_rfl hfloor
    _ ≤ J⁻¹ * (J • muE ν A₀ t₀ q S) X := mul_le_mul' le_rfl (hρ X)
    _ = muE ν A₀ t₀ q S X := by
      rw [Measure.smul_apply, smul_eq_mul, ← mul_assoc,
        ENNReal.inv_mul_cancel hJ0 hJT, one_mul]

end

end Submission.Obl.k4_finite_affine_candidate_return
