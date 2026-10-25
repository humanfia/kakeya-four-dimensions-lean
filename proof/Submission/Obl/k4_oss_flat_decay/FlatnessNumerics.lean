import Submission.Obl.k4_oss_flat_decay.Energy

namespace Submission.Obl.k4_oss_flat_decay

theorem flatness_coefficient_identity {r : ℝ} (hr : 0 < r) (a s : ℝ) :
    (r ^ (-a) * r ^ s / (2 * r ^ (1 + a))) * r *
        (4 * Real.pi / (r / 10000)) * r ^ (1 - a) =
      (20000 * Real.pi) * r ^ (s - 3 * a) := by
  have hη : r ^ (1 + a) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  calc
    _ = (20000 * Real.pi) *
        (r ^ (-a) * r ^ s * r ^ (1 - a) / r ^ (1 + a)) := by
      field_simp [hr.ne', hη]
      <;> ring
    _ = _ := by
      rw [← Real.rpow_add hr, ← Real.rpow_add hr, ← Real.rpow_sub hr]
      congr 2
      ring

theorem flatness_noise_identity {r : ℝ} (hr : 0 < r) (a : ℝ) :
    2 * (100 * r⁻¹) * r ^ (1 + a) = 200 * r ^ a := by
  have hpow : r⁻¹ * r ^ (1 + a) = r ^ a := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hr]
    congr 1
    ring
  calc _ = 200 * (r⁻¹ * r ^ (1 + a)) := by ring
    _ = _ := by rw [hpow]

theorem flatness_scale_budget {r q : ℝ} (hr : 0 < r) (hq : |q| ≤ 100 * r⁻¹) :
    r / 10000 * (|q| * 3) ≤ 1 / 2 := by
  calc r / 10000 * (|q| * 3) ≤ r / 10000 * ((100 * r⁻¹) * 3) := by gcongr
    _ = 3 / 100 := by field_simp; ring
    _ ≤ 1 / 2 := by norm_num

end Submission.Obl.k4_oss_flat_decay
