-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.SelectedGain.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.SelectedInput

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent

open MeasureTheory LeanEval.Analysis.WangZahlKakeya

/-- Separating the count and radius in the normalized target expression. -/
theorem count_weight_as_power {δ n : ℝ} (hδ : 0 < δ) (hn : 0 < n) (σ : ℝ) :
    (n * δ ^ 2) * (n * δ) ^ (-σ) = n ^ (1 - σ) * (δ ^ 2 * δ ^ (-σ)) := by
  rw [Real.mul_rpow hn.le hδ.le,
    show (1 : ℝ) - σ = 1 + -σ by ring, Real.rpow_add hn, Real.rpow_one]
  ring

/-- Retaining a share of the fine tubes loses only that share to the power
`1-σ` in the target volume bound. -/
theorem count_weight_of_retention {δ n k τ σ : ℝ}
    (hδ : 0 < δ) (hn : 0 < n) (hk : 0 < k) (hτ : 0 ≤ τ) (hσ : σ ≤ 1)
    (hkeep : τ * n ≤ k) :
    τ ^ (1 - σ) * ((n * δ ^ 2) * (n * δ) ^ (-σ)) ≤
      (k * δ ^ 2) * (k * δ) ^ (-σ) := by
  rw [count_weight_as_power hδ hn, count_weight_as_power hδ hk, ← mul_assoc,
    ← Real.mul_rpow hτ hn.le]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (mul_nonneg hτ hn.le) hkeep (by linarith)) (by positivity)

/-- Transferring a volume estimate for a selected fine family to the original
normalization, with the exact constant and power loss from its cardinality. -/
theorem gain_of_selected_count {δ n k e β σ κ C : ℝ} {U : Set Space}
    (hδ : 0 < δ) (hn : 0 < n) (hk : 0 < k) (hσ : σ ≤ 1)
    (hκ : 0 ≤ κ) (hC : 0 < C) (hkeep : δ ^ e * n ≤ C * k)
    (hvolume : ENNReal.ofReal (κ * δ ^ β * (k * δ ^ 2) * (k * δ) ^ (-σ)) ≤ volume U) :
    ENNReal.ofReal ((κ * C ^ (σ - 1)) * δ ^ (β + e * (1 - σ)) *
      (n * δ ^ 2) * (n * δ) ^ (-σ)) ≤ volume U := by
  have hkeep' : (δ ^ e / C) * n ≤ k := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hC).mpr
    simpa only [mul_comm C] using hkeep
  have hcount := count_weight_of_retention hδ hn hk (by positivity : 0 ≤ δ ^ e / C) hσ hkeep'
  have hscale : (δ ^ e / C) ^ (1 - σ) = C ^ (σ - 1) * δ ^ (e * (1 - σ)) := by
    rw [Real.div_rpow (Real.rpow_nonneg hδ.le _) hC.le, ← Real.rpow_mul hδ.le,
      div_eq_mul_inv, ← Real.rpow_neg hC.le]
    rw [show -(1 - σ) = σ - 1 by ring]
    ring
  have hbound := mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ κ * δ ^ β)
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hvolume
  calc
    _ = (κ * δ ^ β) * ((δ ^ e / C) ^ (1 - σ) *
        ((n * δ ^ 2) * (n * δ) ^ (-σ))) := by
      rw [hscale, Real.rpow_add hδ]
      ring
    _ ≤ _ := by simpa only [mul_assoc] using hbound

end WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent
