-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.MediumScalar.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

/-- Errors in the body width, volume weight, and convex count only add to the
fine-scale exponent. The middle radius retains the exponent `-ω-σ`. -/
theorem medium_body_factor_bound {δ r B w m C σ ω ε b v h : ℝ}
    (hδ : 0 < δ) (hr : 0 < r) (hC : 0 < C) (hm : 0 ≤ m)
    (hσ : 0 ≤ σ) (hω : 0 ≤ ω)
    (hB : δ ^ b * r ≤ B) (hw : δ ^ v * r ^ 2 ≤ w)
    (hmUpper : m ≤ δ ^ (-h)) :
    C * δ ^ (-ε) * B ^ (-ω) * m ^ (1 + σ / 2) * w ^ (-σ / 2) ≤
      C * δ ^ (-(ε + b * ω + h * (1 + σ / 2) + v * σ / 2)) * r ^ (-ω - σ) := by
  have hBpow : B ^ (-ω) ≤ (δ ^ b * r) ^ (-ω) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hB (neg_nonpos.mpr hω)
  have hwPow : w ^ (-σ / 2) ≤ (δ ^ v * r ^ 2) ^ (-σ / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hw (by linarith)
  have hmPow : m ^ (1 + σ / 2) ≤ (δ ^ (-h)) ^ (1 + σ / 2) :=
    Real.rpow_le_rpow hm hmUpper (by linarith)
  have hBp : 0 < B := (by positivity : 0 < δ ^ b * r).trans_le hB
  have hwp : 0 < w := (by positivity : 0 < δ ^ v * r ^ 2).trans_le hw
  calc
    _ ≤ C * δ ^ (-ε) * (δ ^ b * r) ^ (-ω) *
        (δ ^ (-h)) ^ (1 + σ / 2) * (δ ^ v * r ^ 2) ^ (-σ / 2) := by
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hBpow (by positivity))
        hmPow (by positivity) (by positivity)) hwPow (by positivity) (by positivity)
    _ = _ := by
      apply Real.log_injOn_pos (by simp only [Set.mem_Ioi]; positivity)
        (by simp only [Set.mem_Ioi]; positivity)
      simp (disch := positivity) only [Real.log_mul, Real.log_rpow, Real.log_pow]
      ring

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
