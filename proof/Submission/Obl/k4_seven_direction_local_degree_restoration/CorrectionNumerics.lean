import Mathlib

namespace Submission.Obl.k4_seven_direction_local_degree_restoration

lemma scalar_replacement_bound {M h q H ell lam : ℝ} (hM : 1 ≤ M) (hh : 0 ≤ h)
    (hq : |q| ≤ M) (hH : |H| ≤ 3 * M) (hell : |ell| ≤ M) (hlam : |lam| ≤ M)
    (hclose : |H - q| ≤ 2 * M * h) :
    |q * ell + lam * q ^ 2 - (H * ell + lam * H ^ 2)| ≤ 10 * M ^ 3 * h := by
  have hM0 : 0 ≤ M := by linarith
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hfactor : q * ell + lam * q ^ 2 - (H * ell + lam * H ^ 2) =
      (q - H) * (ell + lam * (q + H)) := by ring
  rw [hfactor, abs_mul]
  have hright : |ell + lam * (q + H)| ≤ M + M * (M + 3 * M) := by
    calc |ell + lam * (q + H)| ≤ |ell| + |lam * (q + H)| := abs_add_le _ _
         _ = |ell| + |lam| * |q + H| := by rw [abs_mul]
         _ ≤ |ell| + |lam| * (|q| + |H|) := by gcongr; exact abs_add_le _ _
         _ ≤ M + M * (M + 3 * M) := by gcongr
  calc |q - H| * |ell + lam * (q + H)| ≤ (2 * M * h) * (M + M * (M + 3 * M)) :=
         mul_le_mul (by simpa [abs_sub_comm] using hclose) hright (abs_nonneg _) (by positivity)
       _ ≤ (2 * M * h) * (5 * M ^ 2) :=
         mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
       _ = 10 * M ^ 3 * h := by ring

lemma scalar_first_correction_bound {M a s H ell lam : ℝ} (hM : 1 ≤ M)
    (ha : 0 ≤ a) (hs : 0 < s) (hH : |H| ≤ 3 * M)
    (hell : |ell| ≤ M) (hlam : |lam| ≤ M) :
    |a / s * (ell + 2 * lam * H)| ≤ 7 * M ^ 2 * (a / s) := by
  have hM0 : 0 ≤ M := by linarith
  have hM2 : M ≤ M ^ 2 := by nlinarith
  have hbnd : |ell + 2 * lam * H| ≤ 7 * M ^ 2 := by
    calc |ell + 2 * lam * H| ≤ |ell| + |2 * lam * H| := abs_add_le _ _
         _ = |ell| + 2 * |lam| * |H| := by rw [abs_mul, abs_mul]; norm_num
         _ ≤ M + 2 * M * (3 * M) := by gcongr
         _ ≤ 7 * M ^ 2 := by nlinarith
  rw [abs_mul, abs_of_nonneg (div_nonneg ha hs.le)]
  exact (mul_le_mul_of_nonneg_left hbnd (div_nonneg ha hs.le)).trans_eq (by ring)

lemma scalar_curvature_bound {A M a b s old lam : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hb : 0 < b) (hba : b ≤ a) (has : a ≤ s)
    (hold : |old| ≤ A / a) (hlam : |lam| ≤ M) :
    |old - 2 * a * lam / s ^ 2| ≤ (A + 2 * M) / b := by
  have ha : 0 < a := hb.trans_le hba
  have hs : 0 < s := ha.trans_le has
  have hratio : a / s ^ 2 ≤ 1 / b := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hs) hb).2
    calc a * b ≤ s * s := mul_le_mul has (hba.trans has) hb.le hs.le
         _ = 1 * s ^ 2 := by ring
  have hc : |2 * a * lam / s ^ 2| ≤ 2 * M / b := by
    rw [abs_div, abs_mul, abs_mul, abs_of_pos ha, abs_of_nonneg (sq_nonneg s)]
    norm_num only [show |(2 : ℝ)| = 2 by norm_num]
    calc 2 * a * |lam| / s ^ 2 ≤ 2 * a * M / s ^ 2 := by gcongr
         _ = (2 * M) * (a / s ^ 2) := by ring
         _ ≤ (2 * M) * (1 / b) := mul_le_mul_of_nonneg_left hratio (by positivity)
         _ = 2 * M / b := by ring
  calc |old - 2 * a * lam / s ^ 2| ≤ |old| + |2 * a * lam / s ^ 2| := abs_sub _ _
       _ ≤ A / a + 2 * M / b := add_le_add hold hc
       _ ≤ A / b + 2 * M / b := add_le_add (div_le_div_of_nonneg_left hA hb hba) le_rfl
       _ = (A + 2 * M) / b := by ring

lemma scalar_corrected_value_bound {M a b h Sw Sf R T q H ell lam : ℝ}
    (hM : 1 ≤ M) (ha : 0 < a) (hb : 0 ≤ b) (hh : 0 ≤ h) (hah : a * h ≤ b)
    (hrel : a * R = Sf) (htransfer : |Sw - Sf| ≤ 2 * M ^ 3 * b)
    (happrox : |R - (T + q * ell + lam * q ^ 2)| ≤ M * b / a)
    (hq : |q| ≤ M) (hH : |H| ≤ 3 * M) (hell : |ell| ≤ M) (hlam : |lam| ≤ M)
    (hclose : |H - q| ≤ 2 * M * h) :
    |Sw - a * (T + H * ell + lam * H ^ 2)| ≤ 13 * M ^ 3 * b := by
  have hM0 : 0 ≤ M := by linarith
  have hM3 : M ≤ M ^ 3 := by
    calc M ≤ M * M ^ 2 := by simpa using mul_le_mul_of_nonneg_left (one_le_pow₀ hM : 1 ≤ M ^ 2) hM0
         _ = M ^ 3 := by ring
  have hdecomp : Sw - a * (T + H * ell + lam * H ^ 2) =
      (Sw - Sf) + a * (R - (T + q * ell + lam * q ^ 2)) +
        a * (q * ell + lam * q ^ 2 - (H * ell + lam * H ^ 2)) := by
    rw [← hrel]
    ring
  have hR : |a * (R - (T + q * ell + lam * q ^ 2))| ≤ M * b := by
    rw [abs_mul, abs_of_pos ha]
    refine (mul_le_mul_of_nonneg_left happrox ha.le).trans_eq ?_
    field_simp
  have hpert : |a * (q * ell + lam * q ^ 2 - (H * ell + lam * H ^ 2))| ≤ 10 * M ^ 3 * b := by
    rw [abs_mul, abs_of_pos ha]
    refine (mul_le_mul_of_nonneg_left (scalar_replacement_bound hM hh hq hH hell hlam hclose) ha.le).trans ?_
    calc a * (10 * M ^ 3 * h) = 10 * M ^ 3 * (a * h) := by ring
         _ ≤ 10 * M ^ 3 * b := mul_le_mul_of_nonneg_left hah (by positivity)
  rw [hdecomp]
  have hsum := abs_add_le ((Sw - Sf) + a * (R - (T + q * ell + lam * q ^ 2)))
    (a * (q * ell + lam * q ^ 2 - (H * ell + lam * H ^ 2)))
  have hsum' := abs_add_le (Sw - Sf) (a * (R - (T + q * ell + lam * q ^ 2)))
  have hMb := mul_le_mul_of_nonneg_right hM3 hb
  linarith

lemma quadratic_transfer_le_cube {A M a b : ℝ} (hA : 0 ≤ A) (hM : 1 ≤ M) (hAM : A ≤ M)
    (hb : 0 < b) (hba : b ≤ a) :
    A * (A * b) + A / a * (A * b) ^ 2 / 2 ≤ 2 * M ^ 3 * b := by
  have ha : 0 < a := hb.trans_le hba
  have hratio : b / a ≤ 1 := (div_le_one₀ ha).2 hba
  have hM0 : 0 ≤ M := by linarith
  have hM23 : M ^ 2 ≤ M ^ 3 := pow_le_pow_right₀ hM (by norm_num)
  have hA2 : A ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ hA hAM 2
  have hA3 : A ^ 3 ≤ M ^ 3 := pow_le_pow_left₀ hA hAM 3
  have he : A * (A * b) + A / a * (A * b) ^ 2 / 2 =
      (A ^ 2 + A ^ 3 / 2 * (b / a)) * b := by ring
  rw [he]
  apply mul_le_mul_of_nonneg_right _ hb.le
  have hterm : A ^ 3 / 2 * (b / a) ≤ A ^ 3 / 2 := by
    simpa using mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ A ^ 3 / 2)
  nlinarith [pow_nonneg hM0 3]

end Submission.Obl.k4_seven_direction_local_degree_restoration
