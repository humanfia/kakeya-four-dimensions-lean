/-
Adapted from this LOT tree, obligation o168, session x0567, branch x0567 (commit 6f572b8d),
Submission/Obl/k4_scalar_guarded_tangent_preparation/InformationExponent.lean,
renamed into namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info.
-/
import Mathlib

namespace Submission.Obl.k4_scalar_guarded_entropic_path.Info

open Filter

noncomputable section

/-- A positive likelihood exponent absorbing twice the information
budget and one absolute unit. -/
def informationExponent (N T : ℝ) : ℝ := (2 * T + 1) / Real.log N

theorem informationExponent_spec {N T : ℝ} (hN : 2 ≤ N) (hT : 0 ≤ T) :
    0 < informationExponent N T ∧ 2 ≤ N ^ informationExponent N T ∧
      T ≤ (1 / 2 : ℝ) * Real.log (N ^ informationExponent N T) := by
  have hNpos : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hpos : 0 < informationExponent N T := div_pos (by linarith) hlog
  have hid : Real.log (N ^ informationExponent N T) = 2 * T + 1 := by
    rw [Real.log_rpow hNpos]
    unfold informationExponent
    field_simp
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hexp : (2 : ℝ) ≤ Real.exp (Real.log (N ^ informationExponent N T)) :=
    htwo.trans (Real.exp_le_exp.mpr (by rw [hid]; linarith))
  rw [Real.exp_log (Real.rpow_pos_of_pos hNpos _)] at hexp
  exact ⟨hpos, hexp, by rw [hid]; linarith⟩

/-- Sublogarithmic information gives a vanishing likelihood exponent. -/
theorem informationExponent_tendsto (N T : ℕ → ℝ)
    (hN : Tendsto N atTop atTop)
    (hT : Tendsto (fun k => T k / Real.log (N k)) atTop (nhds 0)) :
    Tendsto (fun k => informationExponent (N k) (T k)) atTop (nhds 0) := by
  have hlog := Real.tendsto_log_atTop.comp hN
  have hinv : Tendsto (fun k => (Real.log (N k))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hlog
  convert (hT.const_mul 2).add hinv using 1
  · ext k
    unfold informationExponent
    ring
  · norm_num

/-- A score bound relative to the original weighted mass has the exact
half-logarithm budget used by `ReferenceLaws`. -/
theorem informationExponent_weighted_budget {N T mass score : ℝ}
    (hN : 2 ≤ N) (hT : 0 ≤ T) (hmass : 0 ≤ mass) (hscore : score ≤ mass * T) :
    score ≤ (mass / 2) * Real.log (N ^ informationExponent N T) := by
  have h := mul_le_mul_of_nonneg_left (informationExponent_spec hN hT).2.2 hmass
  exact hscore.trans (by nlinarith)

end

end Submission.Obl.k4_scalar_guarded_entropic_path.Info
