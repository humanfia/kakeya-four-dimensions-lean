/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, JointCapRecovery.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.JointGrid
import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.ContinuousNormalization

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

open MeasureTheory
open scoped ENNReal

/-- The fourth-power spatial factor is paid for by the original full true
assignment reference, before the retained measure is normalized. -/
theorem cancel_original_reference_factor
    {H A W C K ξ : ℝ} (hW : 0 < W) (hK : 0 < K) (hC : 0 ≤ C)
    (hfloor : H ^ 4 * A / K ^ 2 ≤ W) :
    W⁻¹ * (C * H ^ 4 * A * ξ ^ 2) ≤ C * K ^ 2 * ξ ^ 2 := by
  have hpaid : H ^ 4 * A ≤ W * K ^ 2 := (div_le_iff₀ (sq_pos_of_pos hK)).mp hfloor
  have hm := mul_le_mul_of_nonneg_right hpaid (mul_nonneg hC (sq_nonneg ξ))
  rw [show W⁻¹ * (C * H ^ 4 * A * ξ ^ 2) = (C * H ^ 4 * A * ξ ^ 2) / W by ring]
  apply (div_le_iff₀ hW).mpr
  nlinarith only [hm]

/-- Normalization preserves the original palette factor and cancels against
the original assignment lower bound. -/
theorem original_reference_scaled_cap
    {H A W C K ξ : ℝ} (hW : 0 < W) (hK : 0 < K) (hC : 0 ≤ C)
    (hfloor : H ^ 4 * A / K ^ 2 ≤ W)
    (mass palette : ℝ≥0∞)
    (hcap : mass ≤ ENNReal.ofReal (C * H ^ 4 * A * ξ ^ 2) * palette) :
    ENNReal.ofReal W⁻¹ * mass ≤ ENNReal.ofReal (C * K ^ 2 * ξ ^ 2) * palette := by
  calc
    _ ≤ ENNReal.ofReal W⁻¹ *
        (ENNReal.ofReal (C * H ^ 4 * A * ξ ^ 2) * palette) := by gcongr
    _ = ENNReal.ofReal (W⁻¹ * (C * H ^ 4 * A * ξ ^ 2)) * palette := by
      rw [ENNReal.ofReal_mul (inv_nonneg.mpr hW.le)]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_le_ofReal (cancel_original_reference_factor hW hK hC hfloor))
      (zero_le : 0 ≤ palette)

/-- The actual continuous time-normalized event has the joint cap paid for
by its unchanged original reference weight. -/
theorem original_normalized_event_joint_cap
    {α : Type*} [MeasurableSpace α] (σ : Measure (α × ℝ))
    (E : Set (α × ℝ)) (hE : MeasurableSet E)
    (t₀ H A W C K ξ : ℝ) (palette : ℝ≥0∞)
    (hW : 0 < W) (hK : 0 < K) (hC : 0 ≤ C)
    (hfloor : H ^ 4 * A / K ^ 2 ≤ W)
    (hcap : σ ((unitTimeMap t₀ H) ⁻¹' E) ≤
      ENNReal.ofReal (C * H ^ 4 * A * ξ ^ 2) * palette) :
    (ENNReal.ofReal W⁻¹ • σ.map (unitTimeMap t₀ H)) E ≤
      ENNReal.ofReal (C * K ^ 2 * ξ ^ 2) * palette := by
  rw [original_continuous_normalized_apply σ t₀ H W E hE]
  exact original_reference_scaled_cap hW hK hC hfloor _ palette hcap

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
