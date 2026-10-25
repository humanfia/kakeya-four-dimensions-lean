import Submission.Obl.k4_dk4_smoothed_problem.BadScales
import Submission.Obl.k4_dk4_smoothed_problem.NativePrior

namespace Submission.Obl.k4_dk4_smoothed_problem

noncomputable def scale (k : ℕ) : ℝ := (2 : ℝ) ^ k
noncomputable def radius (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℤ))
noncomputable def smoothingRadius (k : ℕ) : ℝ := radius k / 12

noncomputable def normalizationFactor (c R : ℝ) : ℝ :=
  6 * (R + 3) + 1 + c⁻¹

noncomputable def nativeFactor (c R : ℝ) (k : ℕ) : ℝ :=
  normalizationFactor c R * ((k : ℝ) + 1) ^ 2

noncomputable def slopeFactor (c : ℝ) (k : ℕ) : ℝ :=
  (46656 / c) * ((k : ℝ) + 1) ^ 2

theorem normalizationFactor_pos {c R : ℝ} (hc : 0 < c) (hR : 1 ≤ R) :
    0 < normalizationFactor c R := by
  unfold normalizationFactor
  positivity

theorem nativeFactor_ge {c R : ℝ} (hc : 0 < c) (hR : 1 ≤ R) (k : ℕ) :
    1 ≤ nativeFactor c R k ∧ 6 * (R + 3) ≤ nativeFactor c R k := by
  have hc0 : 0 ≤ c⁻¹ := by positivity
  have hA0 := normalizationFactor_pos hc hR
  have hq : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by
    nlinarith [sq_nonneg (k : ℝ), Nat.cast_nonneg (α := ℝ) k]
  have hA : normalizationFactor c R ≤ nativeFactor c R k := by
    exact le_mul_of_one_le_right hA0.le hq
  have hA1 : 1 ≤ normalizationFactor c R := by unfold normalizationFactor; linarith
  have hAR : 6 * (R + 3) ≤ normalizationFactor c R := by unfold normalizationFactor; linarith
  exact ⟨hA1.trans hA, hAR.trans hA⟩

theorem nativeFactor_inv_le {c R : ℝ} (hc : 0 < c) (hR : 1 ≤ R) (k : ℕ) :
    (nativeFactor c R k)⁻¹ ≤ c / ((k : ℝ) + 1) ^ 2 := by
  have hc0 : 0 < c⁻¹ := by positivity
  have hA0 := normalizationFactor_pos hc hR
  have hA : c⁻¹ ≤ normalizationFactor c R := by unfold normalizationFactor; linarith
  have hq : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  unfold nativeFactor
  calc
    (normalizationFactor c R * ((k : ℝ) + 1) ^ 2)⁻¹ ≤
        (c⁻¹ * ((k : ℝ) + 1) ^ 2)⁻¹ := by
      gcongr
    _ = c / ((k : ℝ) + 1) ^ 2 := by field_simp

theorem scale_pos (k : ℕ) : 0 < scale k := by unfold scale; positivity

theorem one_le_scale (k : ℕ) : 1 ≤ scale k := one_le_pow₀ (by norm_num)

theorem radius_eq_inv (k : ℕ) : radius k = (scale k)⁻¹ := by
  simp [radius, scale, zpow_neg]

theorem smoothingRadius_pos (k : ℕ) : 0 < smoothingRadius k := by
  rw [smoothingRadius, radius_eq_inv]
  exact div_pos (inv_pos.mpr (scale_pos k)) (by norm_num)

theorem smoothingRadius_le_one (k : ℕ) : smoothingRadius k ≤ 1 := by
  have h := one_le_scale k
  rw [smoothingRadius, radius_eq_inv]
  have : (scale k)⁻¹ ≤ 1 := (inv_le_one₀ (scale_pos k)).mpr h
  linarith

theorem lineCountFloor_eq (c : ℝ) (k : ℕ) :
    lineCountFloor c k = c * scale k ^ 3 / ((k : ℝ) + 1) ^ 2 := by
  unfold lineCountFloor scale
  rw [← pow_mul, Nat.mul_comm k 3]

theorem slope_height_le {c : ℝ} (hc : 0 < c) {k n : ℕ}
    (hcount : lineCountFloor c k ≤ (n : ℝ)) :
    (n : ℝ)⁻¹ * ((2 * smoothingRadius k) ^ 3)⁻¹ ≤
      (216 / c) * ((k : ℝ) + 1) ^ 2 := by
  have hn : (0 : ℝ) < n := (lineCountFloor_pos hc k).trans_le hcount
  have hN := scale_pos k
  have hq : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  rw [lineCountFloor_eq, div_le_iff₀ hq] at hcount
  have hscaled := mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ 216 / c)
  have hnum : (216 : ℝ) * scale k ^ 3 ≤
      (216 / c * ((k : ℝ) + 1) ^ 2) * n := by
    calc
      216 * scale k ^ 3 = (216 / c) * (c * scale k ^ 3) := by field_simp
      _ ≤ (216 / c) * ((n : ℝ) * ((k : ℝ) + 1) ^ 2) := hscaled
      _ = _ := by ring
  have heq : (n : ℝ)⁻¹ * ((2 * smoothingRadius k) ^ 3)⁻¹ =
      216 * scale k ^ 3 / n := by
    rw [smoothingRadius, radius_eq_inv]
    field_simp
    <;> ring
  rw [heq]
  exact (div_le_iff₀ hn).mpr hnum

theorem planar_height_eq (k : ℕ) :
    ((2 * smoothingRadius k) ^ 2)⁻¹ = 36 * scale k ^ 2 := by
  have hN := scale_pos k
  rw [smoothingRadius, radius_eq_inv]
  field_simp
  <;> ring

theorem joint_height_le {c : ℝ} (hc : 0 < c) {k n : ℕ}
    (hcount : lineCountFloor c k ≤ (n : ℝ)) :
    (n : ℝ)⁻¹ * ((2 * smoothingRadius k) ^ 3)⁻¹ *
        ((2 * smoothingRadius k) ^ 2)⁻¹ * 6 ≤
      ((46656 / c) * ((k : ℝ) + 1) ^ 2) * scale k ^ 2 := by
  calc
    (n : ℝ)⁻¹ * ((2 * smoothingRadius k) ^ 3)⁻¹ *
        ((2 * smoothingRadius k) ^ 2)⁻¹ * 6 ≤
        ((216 / c) * ((k : ℝ) + 1) ^ 2) *
          ((2 * smoothingRadius k) ^ 2)⁻¹ * 6 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (slope_height_le hc hcount) (by positivity))
        (by norm_num)
    _ = _ := by rw [planar_height_eq]; ring

theorem ofReal_box_height {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r) (d : ℕ) :
    ENNReal.ofReal ((n : ℝ)⁻¹ * ((2 * r) ^ d)⁻¹) =
      (n : ENNReal)⁻¹ * (ENNReal.ofReal (2 * r) ^ d)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hnR,
    ENNReal.ofReal_natCast, ENNReal.ofReal_inv_of_pos (by positivity),
    ENNReal.ofReal_pow (by positivity)]

theorem componentHeight_le {k n : ℕ} (hn : 0 < n) (hN : 2 ≤ scale k) :
    Framework.componentHeight n (smoothingRadius k) ≤ scale k ^ 32 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hni : (n : ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (by positivity)).mpr hnR
  have hN0 := scale_pos k
  have heq : ((2 * smoothingRadius k) ^ 6)⁻¹ = 46656 * scale k ^ 6 := by
    rw [smoothingRadius, radius_eq_inv]
    field_simp
    <;> ring
  have hconst : (46656 : ℝ) ≤ scale k ^ 16 := by
    calc
      (46656 : ℝ) ≤ (2 : ℝ) ^ 16 := by norm_num
      _ ≤ scale k ^ 16 := pow_le_pow_left₀ (by norm_num) hN 16
  calc
    Framework.componentHeight n (smoothingRadius k) ≤
        ((2 * smoothingRadius k) ^ 6)⁻¹ := by
      unfold Framework.componentHeight
      exact mul_le_of_le_one_left (by positivity) hni
    _ = 46656 * scale k ^ 6 := heq
    _ ≤ scale k ^ 16 * scale k ^ 6 :=
      mul_le_mul_of_nonneg_right hconst (by positivity)
    _ = scale k ^ 22 := by rw [← pow_add]
    _ ≤ scale k ^ 32 := pow_le_pow_right₀ (by linarith) (by omega)

theorem cover_count_le {σ : ℝ} (hσ : 0 < σ) (k : ℕ) :
    (2 : ℝ) ^ (((k : ℝ) + 1) * (4 - σ)) ≤ 16 * scale k ^ (4 - σ) := by
  have hbase : (0 : ℝ) < 2 := by norm_num
  calc
    (2 : ℝ) ^ (((k : ℝ) + 1) * (4 - σ)) =
        (2 : ℝ) ^ (4 - σ) * scale k ^ (4 - σ) := by
      rw [add_mul, Real.rpow_add hbase, Real.rpow_natCast_mul hbase.le]
      unfold scale
      simp only [one_mul]
      ring
    _ ≤ 16 * scale k ^ (4 - σ) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (scale_pos k).le _)
      calc
        (2 : ℝ) ^ (4 - σ) ≤ (2 : ℝ) ^ (4 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 16 := by norm_num

theorem count_bounds {c R σ : ℝ} {k : ℕ} (hσ : 0 < σ)
    (hN : 2 ≤ scale k) (hc : c + 1 ≤ scale k) (A : BadConfiguration c R σ k) :
    (A.n : ℝ) ≤ scale k ^ 32 ∧ (A.m : ℝ) ≤ scale k ^ 8 := by
  have hN1 : 1 ≤ scale k := by linarith
  have hn : (A.n : ℝ) ≤ scale k ^ 4 := by
    calc
      (A.n : ℝ) ≤ (c + 1) * scale k ^ 3 := by
        simpa [scale, ← pow_mul, Nat.mul_comm k 3] using A.count_upper
      _ ≤ scale k * scale k ^ 3 := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = scale k ^ 4 := by ring
  have hpow : scale k ^ (4 - σ) ≤ scale k ^ (4 : ℕ) := by
    calc
      scale k ^ (4 - σ) ≤ scale k ^ (4 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hN1 (sub_le_self _ hσ.le)
      _ = scale k ^ (4 : ℕ) := Real.rpow_natCast _ _
  refine ⟨hn.trans (pow_le_pow_right₀ hN1 (by omega)), ?_⟩
  calc
    (A.m : ℝ) ≤ 16 * scale k ^ (4 - σ) :=
      A.cover_count.trans (cover_count_le hσ k)
    _ ≤ scale k ^ 4 * scale k ^ 4 := by
      apply mul_le_mul _ hpow (Real.rpow_nonneg (scale_pos k).le _) (by positivity)
      calc
          (16 : ℝ) = (2 : ℝ) ^ 4 := by norm_num
          _ ≤ scale k ^ 4 := pow_le_pow_left₀ (by norm_num) hN 4
    _ = scale k ^ 8 := by rw [← pow_add]

theorem atom_count_le {N : ℝ} (hN : 2 ≤ N) {m : ℕ} (hm : (m : ℝ) ≤ N ^ 8) :
    (14 + m : ℝ) ≤ N ^ 32 := by
  have hN1 : 1 ≤ N := by linarith
  have hsmall : (14 : ℝ) ≤ N ^ 8 := by
    calc
      (14 : ℝ) ≤ (2 : ℝ) ^ 8 := by norm_num
      _ ≤ N ^ 8 := pow_le_pow_left₀ (by norm_num) hN 8
  calc
    (14 + m : ℝ) ≤ 2 * N ^ 8 := by linarith
    _ ≤ N * N ^ 8 := mul_le_mul_of_nonneg_right hN (by positivity)
    _ = N ^ 9 := by ring
    _ ≤ N ^ 32 := pow_le_pow_right₀ hN1 (by omega)

end Submission.Obl.k4_dk4_smoothed_problem
