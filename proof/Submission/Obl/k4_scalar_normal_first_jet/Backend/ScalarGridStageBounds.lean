/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarGridStageBounds.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarGridStageBounds.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A polynomial common bound for one original affine hierarchy stage. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

def scalarGridStageBound (K Q : ℝ) : ℝ := 10000 * K ^ 2 * Q

theorem scalarGridStageBound_bounds {K Q : ℝ} (hK : 1 ≤ K) (hQ : 1 ≤ Q) :
    1 ≤ scalarGridStageBound K Q ∧ K ≤ scalarGridStageBound K Q ∧
    5120 * K ^ 2 ≤ scalarGridStageBound K Q ∧ 8 * K ≤ scalarGridStageBound K Q := by
  have hKsq : K ≤ K ^ 2 := by nlinarith
  have hK1 : 1 ≤ K ^ 2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hQ (show 0 ≤ 10000 * K ^ 2 by positivity)
  dsimp [scalarGridStageBound]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem scalarGridStageBound_mass {K Q : ℝ} (hK : 1 ≤ K) (hQ : 1 ≤ Q) :
    (scalarGridStageBound K Q)⁻¹ ≤ Q⁻¹ / (16 * K ^ 2) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hQpos : 0 < Q := zero_lt_one.trans_le hQ
  have he : Q⁻¹ / (16 * K ^ 2) = (16 * K ^ 2 * Q)⁻¹ := by field_simp
  rw [he]
  apply inv_anti₀ (by positivity)
  dsimp [scalarGridStageBound]
  nlinarith [mul_pos (sq_pos_of_pos hKpos) hQpos]

theorem scalarGridStageBound_floor {K Q : ℝ} (hK : 1 ≤ K) (hQ : 1 ≤ Q) :
    (scalarGridStageBound K Q)⁻¹ ≤ 1 / (8 * K) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  simpa only [one_div] using inv_anti₀ (show 0 < 8 * K by positivity)
    (scalarGridStageBound_bounds hK hQ).2.2.2

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
