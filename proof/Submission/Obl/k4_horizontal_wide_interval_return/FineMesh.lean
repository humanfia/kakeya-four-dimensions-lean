import Submission.Obl.k4_horizontal_wide_interval_return.FrameBounds

namespace Submission.Obl.k4_horizontal_wide_interval_return

/-- Fixed power bounds on the native affine predictor affect only how fine the
auxiliary native mesh must be. Its depth is fixed before the scalar loss. -/
theorem fine_mesh_of_power_bounds {N H J Q s m v q g a : ℝ}
    (hN : 2 ≤ N) (hH : 0 ≤ H) (hHN : H ≤ N)
    (hJ : 0 ≤ J) (hQ : 0 ≤ Q) (hs : 0 ≤ s) (hm : 0 ≤ m) (hv : 0 ≤ v)
    (hq : 0 < q) (hg : 0 < g) (hg1 : g ≤ 1)
    (ha : a = N ^ (-s)) (hinv : (q * g)⁻¹ ≤ N ^ Q) :
    let B := J + s + Q + m + v + 20
    let δ := N ^ (-B)
    4 * H ^ 2 * δ ≤ q * N ^ (-m) ∧
    4 * H ^ 2 * δ ≤ q * g ∧
    (3 * N ^ J * (q * g) + 40 * a * H ^ 3) * δ ≤
      a * N ^ (-v) * (q * g) := by
  let B := J + s + Q + m + v + 20
  let δ := N ^ (-B)
  change 4 * H ^ 2 * δ ≤ q * N ^ (-m) ∧
    4 * H ^ 2 * δ ≤ q * g ∧
    (3 * N ^ J * (q * g) + 40 * a * H ^ 3) * δ ≤ a * N ^ (-v) * (q * g)
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hqg : 0 < q * g := mul_pos hq hg
  have hδ : 0 < δ := Real.rpow_pos_of_pos hNpos _
  have hσ : 0 < N ^ (-m) := Real.rpow_pos_of_pos hNpos _
  have hσ1 : N ^ (-m) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)
  have h4 : (4 : ℝ) ≤ N ^ (2 : ℝ) := by
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 2
    norm_num only [OfNat.ofNat, Real.rpow_ofNat] at hp ⊢
    norm_num at hp ⊢
    exact hp
  have h43 : (43 : ℝ) ≤ N ^ (6 : ℝ) := by
    exact (show (43 : ℝ) ≤ (2 : ℝ) ^ (6 : ℕ) by norm_num).trans
      (by simpa only [Real.rpow_ofNat] using pow_le_pow_left₀ (by norm_num) hN 6)
  have hbase : 4 * H ^ 2 * (q * g)⁻¹ * δ ≤ N ^ (-m) := by
    calc 4 * H ^ 2 * (q * g)⁻¹ * δ
        ≤ N ^ (2 : ℝ) * (N ^ (2 : ℝ)) * N ^ Q * N ^ (-B) := by
          dsimp [δ]
          gcongr
          simpa only [Real.rpow_ofNat] using pow_le_pow_left₀ hH hHN 2
      _ = N ^ (4 + Q - B) := by
        rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
        congr 1
        ring
      _ ≤ N ^ (-m) := Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [B]; linarith)
  have hsmall : 4 * H ^ 2 * δ ≤ q * g * N ^ (-m) := by
    have h := mul_le_mul_of_nonneg_right hbase hqg.le
    field_simp at h
    nlinarith
  have hE1 : N ^ J * N ^ s ≤ N ^ (J + s + Q + 3) := by
    rw [← Real.rpow_add hNpos]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    linarith
  have hE2 : H ^ 3 * (q * g)⁻¹ ≤ N ^ (J + s + Q + 3) := by
    calc H ^ 3 * (q * g)⁻¹ ≤ N ^ (3 : ℝ) * N ^ Q := by
          gcongr
          simpa only [Real.rpow_ofNat] using pow_le_pow_left₀ hH hHN 3
      _ = N ^ (3 + Q) := (Real.rpow_add hNpos _ _).symm
      _ ≤ N ^ (J + s + Q + 3) := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hcore : (3 * N ^ J * N ^ s + 40 * H ^ 3 * (q * g)⁻¹) * δ ≤ N ^ (-v) := by
    calc (3 * N ^ J * N ^ s + 40 * H ^ 3 * (q * g)⁻¹) * δ
        ≤ (43 * N ^ (J + s + Q + 3)) * δ := by nlinarith
      _ ≤ (N ^ (6 : ℝ) * N ^ (J + s + Q + 3)) * N ^ (-B) := by
          dsimp [δ]
          gcongr
      _ = N ^ (J + s + Q + 9 - B) := by
          rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
          congr 1
          ring
      _ ≤ N ^ (-v) := Real.rpow_le_rpow_of_exponent_le hN1 (by dsimp [B]; linarith)
  have ha0 : 0 < a := by rw [ha]; exact Real.rpow_pos_of_pos hNpos _
  have has : N ^ s * a = 1 := by
    rw [ha, ← Real.rpow_add hNpos]
    simp
  refine ⟨hsmall.trans ?_, hsmall.trans (mul_le_of_le_one_right hqg.le hσ1), ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hq.le hg1) hσ.le
  have h := mul_le_mul_of_nonneg_right hcore (mul_nonneg ha0.le hqg.le)
  have heq : (3 * N ^ J * (q * g) + 40 * a * H ^ 3) * δ =
      (3 * N ^ J * N ^ s + 40 * H ^ 3 * (q * g)⁻¹) * δ * (a * (q * g)) := by
    field_simp
    linear_combination -(3 * N ^ J * q * g) * has
  rw [heq]
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

end Submission.Obl.k4_horizontal_wide_interval_return
