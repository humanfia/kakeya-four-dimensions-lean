-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_half.ParameterTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.ExponentStability
import Submission.WZ.Obl.wz_furstenberg_katz_tao_half.SeparatedFurstenberg

/-!
# Perturbing the exponent in the separated-point estimate

A fixed-exponent Furstenberg estimate remains valid for nearby exponents,
with some of its error allowance and some of its gain spent on the change.
-/

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_half

lemma separated_furstenberg_exponent_transfer {r σ s ε₀ ε₁ η₀ η₁ : ℝ}
    (hr : 0 < r) (hrhalf : r ≤ 1 / 2) (hs : 0 ≤ s)
    (hη : η₁ + 2 * |σ - s| ≤ η₀)
    (hε : ε₁ + 2 * |σ - s| ≤ ε₀)
    (h : SeparatedFurstenbergAt r s ε₀ η₀) :
    SeparatedFurstenbergAt r σ ε₁ η₁ := by
  have hrone : r ≤ 1 := by linarith
  have hηle : η₁ ≤ η₀ := by linarith [abs_nonneg (σ - s)]
  have hF : r ^ (-η₁) ≤ r ^ (-η₀) :=
    Real.rpow_le_rpow_of_exponent_ge hr hrone (by linarith)
  intro P D hPf hPne hDf hPnorm hPsep hFrost hDunit hlarge hDsep hKT
  obtain ⟨J, hJD, hJsep, hJcard⟩ := h P D hPf hPne hDf hPnorm hPsep
    (fun x ρ hρ => (hFrost x ρ hρ).trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hF (hr.le.trans hρ)) (Nat.cast_nonneg _)))
    hDunit
    (fun p hp => (Real.rpow_le_rpow_of_exponent_ge hr hrone
      (show η₁ - σ ≤ η₀ - s by
        linarith [neg_abs_le (σ - s), abs_nonneg (σ - s)])).trans (hlarge p hp))
    hDsep
    (fun p hp => unit_bush_exponent_transfer hr hrhalf hs hη
      (fun q hq => (hDunit q hq).2) p (hKT p hp))
  refine ⟨J, hJD, hJsep, ?_⟩
  apply le_trans _ hJcard
  exact Real.rpow_le_rpow_of_exponent_ge hr hrone (by
    linarith [le_abs_self (σ - s)])

end WangZahlLot.Obl.wz_furstenberg_katz_tao_half
