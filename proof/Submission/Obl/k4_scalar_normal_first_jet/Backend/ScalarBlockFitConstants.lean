/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarBlockFitConstants.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarBlockFitConstants.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! One polynomial bound for all actual normalized block inputs. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

def scalarBlockFitBound (K : ℝ) : ℝ := 100000 * K ^ 10

theorem scalarBlockFitBound_bounds {K : ℝ} (hK : 1 ≤ K) :
    1 ≤ scalarBlockFitBound K ∧ K ≤ scalarBlockFitBound K ∧
    10000 * K ^ 4 ≤ scalarBlockFitBound K ∧
    10000 * K ^ 6 ≤ scalarBlockFitBound K ∧
    400 * K ^ 3 ≤ scalarBlockFitBound K ∧
    18 * K ^ 2 ≤ scalarBlockFitBound K ∧
    16 * K ^ 2 ≤ scalarBlockFitBound K ∧
    13 * K ^ 2 ≤ scalarBlockFitBound K ∧
    12 * K ^ 3 ≤ scalarBlockFitBound K := by
  have h1 : 1 ≤ K ^ 10 := one_le_pow₀ hK
  have h01 : K ^ 1 ≤ K ^ 10 := pow_le_pow_right₀ hK (by norm_num)
  have h2 : K ^ 2 ≤ K ^ 10 := pow_le_pow_right₀ hK (by norm_num)
  have h3 : K ^ 3 ≤ K ^ 10 := pow_le_pow_right₀ hK (by norm_num)
  have h4 : K ^ 4 ≤ K ^ 10 := pow_le_pow_right₀ hK (by norm_num)
  have h6 : K ^ 6 ≤ K ^ 10 := pow_le_pow_right₀ hK (by norm_num)
  simp only [pow_one] at h01
  dsimp [scalarBlockFitBound]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem scalarBlockFitBound_inverse {K : ℝ} (hK : 1 ≤ K) :
    (scalarBlockFitBound K)⁻¹ ≤ (K⁻¹) ^ 2 / (10000 * K ^ 4) := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have he : (K⁻¹) ^ 2 / (10000 * K ^ 4) = (10000 * K ^ 6)⁻¹ := by
    field_simp
  rw [he]
  exact inv_anti₀ (by positivity) (scalarBlockFitBound_bounds hK).2.2.2.1

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
