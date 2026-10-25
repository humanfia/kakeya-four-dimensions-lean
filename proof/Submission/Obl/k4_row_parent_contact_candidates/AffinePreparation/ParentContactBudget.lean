/- Adapted from: here:o222, session x0774, commit 3c748bb8.
Original file: Submission/Obl/k4_projected_parent_contact_reduction/ParentContactBudget.lean. -/
import Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation.ParentUniformCaps
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth

/-! A single subpower constant for the original-law coarse contact sample. -/

namespace Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation

open Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing
  (subpower_max subpower_polynomial)

noncomputable section

def parentContactBudget (K M : ℝ) : ℝ := 100000000 * max K M ^ 32

theorem parentContactBudget_bounds {K M : ℝ} (hK : 1 ≤ K) (hM : 1 ≤ M) :
    1 ≤ parentContactBudget K M ∧ K ≤ parentContactBudget K M ∧
      2 * M ≤ parentContactBudget K M ∧
      2 * K + M * (2 * K + M + 2 * M * K) ≤ parentContactBudget K M ∧
      recoveredParentBaseConstant K M ≤ parentContactBudget K M := by
  let X := max K M
  have hX : 1 ≤ X := hK.trans (le_max_left _ _)
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hKX : K ≤ X := le_max_left _ _
  have hMX : M ≤ X := le_max_right _ _
  have hpow1 : X ≤ X ^ 32 := by
    simpa using pow_le_pow_right₀ hX (show 1 ≤ (32 : ℕ) by decide)
  have hpow3 : X ^ 3 ≤ X ^ 32 := pow_le_pow_right₀ hX (by decide)
  have hpow17 : X ^ 17 ≤ X ^ 32 := pow_le_pow_right₀ hX (by decide)
  have hXpow : 1 ≤ X ^ 32 := one_le_pow₀ hX
  have hcoef : 2 * K + M * (2 * K + M + 2 * M * K) ≤ 7 * X ^ 3 := by
    have hX2 : X ≤ X ^ 2 := by nlinarith
    have hX3 : X ^ 2 ≤ X ^ 3 := pow_le_pow_right₀ hX (by decide)
    calc
      _ ≤ 2 * X + X * (2 * X + X + 2 * X * X) := by gcongr
      _ = 2 * X + 3 * X ^ 2 + 2 * X ^ 3 := by ring
      _ ≤ _ := by nlinarith
  have hcap : recoveredParentBaseConstant K M ≤ 3539160 * X ^ 17 := by
    have hsmall : X ^ 3 ≤ X ^ 17 := pow_le_pow_right₀ hX (by decide)
    calc
      _ ≤ recoveredParentBaseConstant X X := by
        unfold recoveredParentBaseConstant
        gcongr
      _ = 3538944 * X ^ 17 + 216 * X ^ 3 := by
        unfold recoveredParentBaseConstant
        ring
      _ ≤ _ := by nlinarith
  change 1 ≤ 100000000 * X ^ 32 ∧ K ≤ 100000000 * X ^ 32 ∧
    2 * M ≤ 100000000 * X ^ 32 ∧
    2 * K + M * (2 * K + M + 2 * M * K) ≤ 100000000 * X ^ 32 ∧
    recoveredParentBaseConstant K M ≤ 100000000 * X ^ 32
  refine ⟨by nlinarith, by nlinarith, by nlinarith, ?_, ?_⟩
  · exact hcoef.trans (by nlinarith)
  · exact hcap.trans (by nlinarith)

theorem parentContactBudget_subpower {N K M : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : Submission.Obl.k4_scalar_marked_coefficient_smoothing.Subpower N K) (hM : Submission.Obl.k4_scalar_marked_coefficient_smoothing.Subpower N M) :
    Submission.Obl.k4_scalar_marked_coefficient_smoothing.Subpower N (fun k => parentContactBudget (K k) (M k)) := by
  exact subpower_polynomial hN hNt (subpower_max hK hM) (by norm_num) 32

end

end Submission.Obl.k4_row_parent_contact_candidates.AffinePreparation
