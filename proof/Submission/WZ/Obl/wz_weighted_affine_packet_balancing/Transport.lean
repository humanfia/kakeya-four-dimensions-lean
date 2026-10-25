-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_weighted_affine_packet_balancing.Transport.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_weighted_affine_packet_balancing.Basic

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_weighted_affine_packet_balancing

open MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- The local retained fraction converts the averaged cost bound to the selected population. -/
theorem selected_budget {h h₀ n c C mass P : ℝ} (hh : 0 ≤ h) (hh₀ : 0 < h₀)
    (hC : 0 ≤ C) (hgood : h₀ * n * c ≤ C * mass)
    (hlocal : h * mass ≤ h₀ * P) : h * n * c ≤ C * P := by
  apply (mul_le_mul_iff_right₀ hh₀).mp
  calc
    h₀ * (h * n * c) = h * (h₀ * n * c) := by ring
    _ ≤ h * (C * mass) := mul_le_mul_of_nonneg_left hgood hh
    _ = C * (h * mass) := by ring
    _ ≤ C * (h₀ * P) := mul_le_mul_of_nonneg_left hlocal hC
    _ = h₀ * (C * P) := by ring

/-- Rounding the incidence target costs at most two total budgets. -/
theorem repeated_cost {h H P c C : ℝ} {k : ℕ}
    (hP : 0 < P) (hc : 0 ≤ c) (hC : 0 ≤ C) (hcC : c ≤ C)
    (hbudget : H * c ≤ C * P) (hround : (k : ℝ) * P ≤ H + P)
    (hsmall : 2 * h ^ 2 ≤ 1) : h * h * (k : ℝ) * c ≤ C := by
  have htwo : (k : ℝ) * c ≤ 2 * C := by
    apply (mul_le_mul_iff_left₀ hP).mp
    calc
      (k : ℝ) * c * P = (k : ℝ) * P * c := by ring
      _ ≤ (H + P) * c := mul_le_mul_of_nonneg_right hround hc
      _ ≤ 2 * C * P := by nlinarith [mul_le_mul_of_nonneg_right hcC hP.le]
  calc
    h * h * (k : ℝ) * c = h ^ 2 * ((k : ℝ) * c) := by ring
    _ ≤ h ^ 2 * (2 * C) := mul_le_mul_of_nonneg_left htwo (sq_nonneg h)
    _ = (2 * h ^ 2) * C := by ring
    _ ≤ C := by simpa using mul_le_mul_of_nonneg_right hsmall hC

/-- The affine volume budget pays for repetitions of a restricted packet. -/
theorem transport_repetitions {h D c C : ℝ} {k : ℕ} (hh : 0 ≤ h)
    {U U' : Set Space} (hsub : U' ⊆ U)
    (hcost : ENNReal.ofReal c = ENNReal.ofReal D * volume U)
    (hbudget : h * h * (k : ℝ) * c ≤ C) :
    ENNReal.ofReal (h * (h * D)) * (∑ _j : Fin k, volume U') ≤ ENNReal.ofReal C := by
  calc
    _ ≤ ENNReal.ofReal (h * (h * D)) * (∑ _j : Fin k, volume U) :=
      mul_le_mul' le_rfl (Finset.sum_le_sum fun _ _ => measure_mono hsub)
    _ = ENNReal.ofReal (h * h * (k : ℝ)) * (ENNReal.ofReal D * volume U) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul hh, ENNReal.ofReal_mul hh,
        ENNReal.ofReal_mul (mul_nonneg hh hh), ENNReal.ofReal_mul hh,
        ENNReal.ofReal_natCast]
      ring
    _ = ENNReal.ofReal (h * h * (k : ℝ) * c) := by
      rw [← hcost, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hbudget

end WangZahlLot.Obl.wz_weighted_affine_packet_balancing
