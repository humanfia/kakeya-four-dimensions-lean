-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_nonflat_factored_improvement.ProductLoss.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_nonflat_factored_improvement.ScaleAlgebra

namespace WangZahlLot.Obl.wz_nonflat_factored_improvement

/-- All refinement, nonflatness and density losses fit in the requested power of delta. -/
theorem product_loss_bound {δ a b ν β τ σ ω u ε e A K W V : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (ha : 0 < a) (hb : 0 < b) (hb1 : b ≤ 1)
    (hνβ : 0 ≤ ν + β) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (he : 0 ≤ e)
    (hA : 0 < A) (hK : 0 < K) (hW : 0 ≤ W)
    (hflat : δ ^ β * b ≤ a) (hWV : δ ^ ν * W ≤ V)
    (hloss : ε + 5 * ν + 2 * β + τ ≤ e) :
    (A * coarseFraction / K) * δ ^ (u + e) * b ^ (ω - u + e) * W ≤
      A * δ ^ ν * δ ^ τ / K * (δ ^ (-ν) * b / a) ^ (-σ) *
        coarseMassFraction a b (δ ^ (-ν)) * δ ^ (u + ε) * b ^ (ω - u) * V := by
  have hcf := coarseFraction_pos
  have hex := excess_power_lower hδ hδ1 ha hb hνβ hσ0 hσ1 hflat
  have hmass := coarse_mass_power_lower (ν := ν) hδ ha hb hflat
  have hV : 0 ≤ V := (mul_nonneg (Real.rpow_nonneg hδ.le _) hW).trans hWV
  have hpow : δ ^ (u + e) ≤ δ ^ (u + ε + 5 * ν + 2 * β + τ) :=
    Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (by linarith)
  have hbpow : b ^ (ω - u + e) ≤ b ^ (ω - u) := by
    rw [Real.rpow_add hb]
    exact mul_le_of_le_one_right (Real.rpow_nonneg hb.le _) (Real.rpow_le_one hb.le hb1 he)
  have heq : δ ^ (u + ε + 5 * ν + 2 * β + τ) =
      δ ^ ν * δ ^ τ * δ ^ (ν + β) * δ ^ (β + 2 * ν) * δ ^ (u + ε) * δ ^ ν := by
    rw [← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ,
      ← Real.rpow_add hδ, ← Real.rpow_add hδ]
    congr 1
    ring
  calc
    _ ≤ (A * coarseFraction / K) * δ ^ (u + ε + 5 * ν + 2 * β + τ) * b ^ (ω - u) * W := by gcongr
    _ = A * δ ^ ν * δ ^ τ / K * δ ^ (ν + β) * (coarseFraction * δ ^ (β + 2 * ν)) *
        δ ^ (u + ε) * b ^ (ω - u) * (δ ^ ν * W) := by rw [heq]; ring
    _ ≤ _ := by gcongr

end WangZahlLot.Obl.wz_nonflat_factored_improvement
