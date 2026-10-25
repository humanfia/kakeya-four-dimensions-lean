-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.LogLoss.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.Scales

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

/-- A logarithm can be bounded by any negative power with an explicit coefficient. -/
theorem one_add_abs_log_le_rpow {d t : ℝ} (hd : 0 < d) (hd1 : d ≤ 1) (ht : 0 < t) :
    1 + |Real.log d| ≤ (1 + 1 / t) * d ^ (-t) := by
  have hlog : Real.log d ≤ 0 := Real.log_nonpos hd.le hd1
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hd (-t))
  rw [Real.log_rpow hd] at h
  have hp : 1 ≤ d ^ (-t) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd hd1 (by linarith)
  rw [abs_of_nonpos hlog]
  have hsmall : -Real.log d ≤ d ^ (-t) / t := by
    apply (le_div_iff₀ ht).mpr
    nlinarith
  calc
    1 + -Real.log d ≤ d ^ (-t) + d ^ (-t) / t := add_le_add hp hsmall
    _ = _ := by ring

/-- Every fixed power of a logarithmic loss is absorbed by a positive power of the scale. -/
theorem exists_log_loss_cutoff (C ε D : ℝ) (k : ℕ) (hε : 0 < ε) (hD : 0 < D) :
    ∃ d₀ : ℝ, 0 < d₀ ∧ d₀ ≤ D ∧ ∀ d : ℝ, 0 < d → d ≤ d₀ →
      C * (1 + |Real.log d|) ^ k * d ^ ε ≤ 1 := by
  let t : ℝ := ε / (2 * (k + 1))
  have ht : 0 < t := by dsimp [t]; positivity
  let A : ℝ := (max 1 C) * (1 + 1 / t) ^ k
  have hA : 0 < A := by
    apply mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    exact pow_pos (by positivity) _
  obtain ⟨d₀, hd₀, hd₀D, hsmall⟩ := exists_scale_cutoff A⁻¹ (ε / 2) (min D 1)
    (inv_pos.mpr hA) (by linarith) (lt_min hD zero_lt_one)
  refine ⟨d₀, hd₀, hd₀D.trans (min_le_left _ _), ?_⟩
  intro d hd hdd
  have hd1 : d ≤ 1 := hdd.trans (hd₀D.trans (min_le_right _ _))
  have hlog := one_add_abs_log_le_rpow hd hd1 ht
  have hpk : (1 + |Real.log d|) ^ k ≤ (1 + 1 / t) ^ k * d ^ (-t * k) := by
    calc
      _ ≤ ((1 + 1 / t) * d ^ (-t)) ^ k := pow_le_pow_left₀ (by positivity) hlog k
      _ = _ := by rw [mul_pow, ← Real.rpow_natCast (d ^ (-t)) k, ← Real.rpow_mul hd.le]
  have hmargin : ε / 2 ≤ ε - t * k := by
    have htk : t * (2 * ((k : ℝ) + 1)) = ε := by
      dsimp [t]
      field_simp
    have ht0 : 0 ≤ t := ht.le
    nlinarith
  have hpower : d ^ (ε - t * k) ≤ d ^ (ε / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hd hd1 hmargin
  calc
    C * (1 + |Real.log d|) ^ k * d ^ ε ≤
        (max 1 C) * ((1 + 1 / t) ^ k * d ^ (-t * k)) * d ^ ε := by
          gcongr
          exact le_max_right _ _
    _ = A * (d ^ (-t * k) * d ^ ε) := by dsimp [A]; ring
    _ = A * d ^ (ε - t * k) := by
      rw [← Real.rpow_add hd]
      congr 2
      ring
    _ ≤ A * d ^ (ε / 2) := mul_le_mul_of_nonneg_left hpower hA.le
    _ ≤ A * A⁻¹ := mul_le_mul_of_nonneg_left (hsmall d hd hdd) hA.le
    _ = 1 := mul_inv_cancel₀ hA.ne'

end WangZahlLot.Obl.wz_multiscale_finite_tower
