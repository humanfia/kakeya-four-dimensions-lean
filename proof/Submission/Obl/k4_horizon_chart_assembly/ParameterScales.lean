import Submission.Obl.k4_horizon_chart_assembly.NativeGeometry

namespace Submission.Obl.k4_horizon_chart_assembly

open Set

noncomputable section

/-- The exact dyadic time partition has block length `delta(N,L)/8`. -/
theorem initial_dyadic_partition {N L : ℝ} (hN : 1 ≤ N) (hL : 0 ≤ L) :
    ∃ T : ℕ, (8 : ℝ) ≤ 2 ^ T ∧ (2 : ℝ) ^ T ≤ 8 * N ^ L ∧
      dl N L = 8 * ((2 : ℝ) ^ T)⁻¹ ∧ dl N L ≤ 1 := by
  obtain ⟨T₀, hT₀, ha⟩ := exists_time_partition hN hL
  have ha' : dl N L = ((2 : ℝ) ^ T₀)⁻¹ := ha
  let T := T₀ + 3
  have hp : (2 : ℝ) ^ T = 8 * (2 : ℝ) ^ T₀ := by
    dsimp [T]
    rw [pow_add]
    norm_num
    ring
  have hbase : (1 : ℝ) ≤ 2 ^ T₀ := one_le_pow₀ (by norm_num)
  refine ⟨T, by rw [hp]; linarith, ?_, ?_, ?_⟩
  · rw [hp]
    exact mul_le_mul_of_nonneg_left hT₀ (by norm_num)
  · rw [ha', hp]
    ring
  · rw [ha']
    exact (inv_le_one₀ (by positivity)).mpr hbase

/-- The block length is bounded below by the corresponding ordinary power. -/
theorem dyadic_block_length_lower {N L : ℝ} (hN : 0 < N) {T : ℕ}
    (hscale : dl N L = 8 * ((2 : ℝ) ^ T)⁻¹) :
    N ^ (-L) / 8 ≤ ((2 : ℝ) ^ T)⁻¹ := by
  have h : N ^ (-L) ≤ dl N L := (resolution_bounds hN L).1
  rw [hscale] at h
  linarith

def meshIndex (N : ℝ) (J : ℕ) : ℕ := Nat.ceil (N ^ J)

/-- Rounding a fixed power up to an integer costs one fixed power at most. -/
theorem meshIndex_bounds {N : ℝ} (hN : 2 ≤ N) {J : ℕ} (hJ : 1 ≤ J) :
    2 ≤ meshIndex N J ∧ N ^ J ≤ (meshIndex N J : ℝ) ∧
      (meshIndex N J : ℝ) ≤ N ^ (J + 1) := by
  have hN₀ : 0 ≤ N := by linarith
  have hN₁ : 1 ≤ N := by linarith
  have hlower : N ^ J ≤ (meshIndex N J : ℝ) := Nat.le_ceil _
  have hupper : (meshIndex N J : ℝ) ≤ N ^ J + 1 :=
    (Nat.ceil_lt_add_one (pow_nonneg hN₀ J)).le
  have hJN : N ≤ N ^ J := by simpa using pow_le_pow_right₀ hN₁ hJ
  have hJ₁ : 1 ≤ N ^ J := one_le_pow₀ hN₁
  refine ⟨by exact_mod_cast (hN.trans hJN).trans hlower, hlower, ?_⟩
  rw [pow_succ]
  nlinarith [mul_le_mul_of_nonneg_left hN (pow_nonneg hN₀ J)]

/-- A sufficiently fine fixed polynomial mesh meets the original light-cell
scale cutoff, uniformly over all later tolerance exponents. -/
theorem fine_mesh_scale_le {N q H₀ : ℝ} {D J : ℕ}
    (hN : 1 ≤ N) (hq : q ≤ 1) (hD : N ^ J ≤ (D : ℝ)) (hJ : H₀ ≤ (J : ℝ)) :
    q / (D : ℝ) ≤ N ^ (-H₀) := by
  have hN₀ : 0 < N := zero_lt_one.trans_le hN
  have hpow : 0 < N ^ J := pow_pos hN₀ J
  have hD₀ : 0 < (D : ℝ) := hpow.trans_le hD
  calc
    _ ≤ 1 / (D : ℝ) := div_le_div_of_nonneg_right hq hD₀.le
    _ ≤ 1 / N ^ J := one_div_le_one_div_of_le hpow hD
    _ = N ^ (-(J : ℝ)) := by simp only [Real.rpow_neg hN₀.le, Real.rpow_natCast, one_div]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN (by linarith)

/-- Closed blocks have the required whole-time support, and their start is a
valid native grouping time. -/
theorem dyadic_block_geometry (T : ℕ) (j : Fin (2 ^ T)) :
    let q : ℝ := ((2 : ℝ) ^ T)⁻¹
    let s : ℝ := (j : ℝ) * q
    s ∈ Icc (0 : ℝ) 1 ∧ Icc s (s + q) ⊆ Icc (0 : ℝ) 1 ∧
      ∀ t ∈ Icc s (s + q), |t - s| ≤ q := by
  dsimp only
  let q : ℝ := ((2 : ℝ) ^ T)⁻¹
  have hq : 0 < q := by dsimp [q]; positivity
  have hj : (j : ℝ) + 1 ≤ (2 : ℝ) ^ T := by exact_mod_cast Nat.succ_le_of_lt j.isLt
  have hprod : (2 : ℝ) ^ T * q = 1 := mul_inv_cancel₀ (by positivity)
  have hstart : 0 ≤ (j : ℝ) * q := mul_nonneg (Nat.cast_nonneg j.val) hq.le
  have hend : (j : ℝ) * q + q ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hj hq.le
    nlinarith
  refine ⟨⟨hstart, by linarith⟩, ?_, ?_⟩
  · intro t ht
    exact ⟨hstart.trans ht.1, ht.2.trans hend⟩
  · intro t ht
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    linarith [ht.2]

end
end Submission.Obl.k4_horizon_chart_assembly
