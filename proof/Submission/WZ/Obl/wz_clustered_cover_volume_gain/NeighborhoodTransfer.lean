-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.NeighborhoodTransfer.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.BallDensity

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set Metric MeasureTheory
open scoped ENNReal
open WangZahlLot.Obl.wz_flat_factored_improvement (Space)

lemma lower_union_of_neighborhood {U Z : Set Space} {r lam : ℝ} {M : ℝ≥0∞}
    (hr : 0 < r) (hZ : Bornology.IsBounded Z) (hU : MeasurableSet U)
    (hmass : M ≤ volume (thickening r Z))
    (hdensity : ∀ p ∈ Z, ENNReal.ofReal (lam * r ^ 3) ≤ volume (U ∩ ball p r)) :
    ENNReal.ofReal (lam / 512) * M ≤ volume U := by
  have hh := (mul_le_mul' (le_refl (ENNReal.ofReal lam)) hmass).trans
    (thickening_volume_of_ball_density hr hZ hU hdensity)
  have hm := mul_le_mul' (le_refl (ENNReal.ofReal (1 / 512 : ℝ))) hh
  convert hm using 1
  · rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 512)]
    congr 2
    ring
  · rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 512)]
    norm_num

lemma neighborhood_factor_baseline {d r n σ ω : ℝ} (hd : 0 < d) (hr : 0 < r) (hn : 0 < n) :
    r ^ ω * n ^ (1 - σ) * d ^ (2 - σ) * (r / d) ^ σ =
      d ^ ω * (n * d ^ 2) * (n * d) ^ (-σ) * (r / d) ^ (ω + σ) := by
  apply Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity)
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_pow]
  ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
