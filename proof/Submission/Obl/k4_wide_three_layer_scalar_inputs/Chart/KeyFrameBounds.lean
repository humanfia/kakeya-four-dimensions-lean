/- Adapted from this LOT tree o218, branch x0950, commit 5227dd4c,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/KeyFrameBounds.lean. Original attribution, when present, is preserved below. -/

import Submission.Obl.k4_wide_three_layer_scalar_inputs.Chart.KeyFrameCoordinates

namespace Submission.Obl.k4_wide_three_layer_scalar_inputs
namespace KeyFrame

open Set

/-- One occupied true-block/key sample bounds the key slice coordinate of the
original cell graph at the beginning of its time block. -/
theorem chartBeta_zero_bound (F : CellFrame) (b : Fin 6 → ℝ)
    {K χ Zk Vk Yk : ℝ} (hK : 1 ≤ K) (hq : 0 < F.q) (hg : 0 < F.g)
    (hχ : 0 ≤ χ) (hχm : χ ≤ F.q * F.g) (ht₀ : |F.t₀| ≤ 1)
    (hc₄ : |F.c 4| ≤ K)
    (hZ : |b 0 - Zk| ≤ χ) (hV : |b 3 - Vk| ≤ χ)
    (hY : |b 1 + F.t₀ * b 4 - Yk| ≤ F.q * F.g)
    (hQ : |b 1 + F.t₀ * b 4 - baseY F F.t₀ (b 0 + F.t₀ * b 3)| ≤
      K * (F.q * F.g)) :
    |chartBeta F Zk Vk Yk 0| ≤ 3 * K := by
  have hm : 0 < F.q * F.g := mul_pos hq hg
  have hK0 : 0 ≤ K := by linarith
  have hZ' : |Zk - b 0| ≤ χ := by simpa only [abs_sub_comm] using hZ
  have hV' : |Vk - b 3| ≤ χ := by simpa only [abs_sub_comm] using hV
  have hZ₀ : |keyZ Zk Vk F.t₀ - (b 0 + F.t₀ * b 3)| ≤ 2 * χ := by
    have hid : keyZ Zk Vk F.t₀ - (b 0 + F.t₀ * b 3) =
        (Zk - b 0) + F.t₀ * (Vk - b 3) := by unfold keyZ; ring
    rw [hid]
    calc
      _ ≤ |Zk - b 0| + |F.t₀| * |Vk - b 3| := by
        rw [← abs_mul]
        exact abs_add_le _ _
      _ ≤ χ + 1 * χ := by gcongr
      _ = _ := by ring
  have hbase : |baseY F F.t₀ (keyZ Zk Vk F.t₀) - Yk| ≤
      (1 + 3 * K) * (F.q * F.g) := by
    have hid : baseY F F.t₀ (keyZ Zk Vk F.t₀) - Yk =
        F.c 4 * (keyZ Zk Vk F.t₀ - (b 0 + F.t₀ * b 3)) -
        (b 1 + F.t₀ * b 4 - baseY F F.t₀ (b 0 + F.t₀ * b 3)) +
        (b 1 + F.t₀ * b 4 - Yk) := by unfold baseY; ring
    rw [hid]
    calc
      _ ≤ |F.c 4| * |keyZ Zk Vk F.t₀ - (b 0 + F.t₀ * b 3)| +
          |b 1 + F.t₀ * b 4 - baseY F F.t₀ (b 0 + F.t₀ * b 3)| +
          |b 1 + F.t₀ * b 4 - Yk| := by
        rw [← abs_mul]
        exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ K * (2 * χ) + K * (F.q * F.g) + F.q * F.g := by gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hχm hK0]
  change |1 / 4 + (baseY F F.t₀ (keyZ Zk Vk F.t₀) - Yk) / (2 * F.q * F.g)| ≤ _
  calc
    _ ≤ 1 / 4 + |baseY F F.t₀ (keyZ Zk Vk F.t₀) - Yk| / (2 * F.q * F.g) := by
      simpa only [abs_div, abs_of_pos (by positivity : 0 < 2 * F.q * F.g),
        show |(1 : ℝ) / 4| = 1 / 4 by norm_num] using abs_add_le (1 / 4 : ℝ) ((baseY F F.t₀ (keyZ Zk Vk F.t₀) - Yk) / (2 * F.q * F.g))
    _ ≤ 1 / 4 + ((1 + 3 * K) * (F.q * F.g)) / (2 * F.q * F.g) := by gcongr
    _ = 1 / 4 + (1 + 3 * K) / 2 := by field_simp [ne_of_gt hq, ne_of_gt hg]
    _ ≤ _ := by linarith

/-- The horizontal center relations and an occupied midpoint sample bound the
key-motion slope uniformly by a fixed polynomial of the original loss. -/
theorem chartBeta_one_bound (F : CellFrame) (b : Fin 6 → ℝ)
    {K χ Zk Vk Yk : ℝ} (hK : 1 ≤ K) (hq : 0 < F.q) (hg : 0 < F.g)
    (hg₁ : F.g ≤ 1) (hqg : F.q ≤ K * F.g) (hχ : 0 ≤ χ) (hχm : χ ≤ F.q * F.g)
    (hc₄ : |F.c 4| ≤ K) (hb₃ : |b 3| ≤ K)
    (hZ : |b 0 - Zk| ≤ χ) (hV : |b 3 - Vk| ≤ χ)
    (hcenter : |F.c 3 + F.c 0 + (F.t₀ + F.q / 2) * F.c 1| ≤ K * F.q)
    (htilt : |F.c 4 - (F.t₀ + F.q / 2)| ≤ K * F.q)
    (hQ : |b 0 + (F.t₀ + F.q / 2) * b 3 - F.c 0 -
      (F.t₀ + F.q / 2) * F.c 1| ≤ K * F.q) :
    |chartBeta F Zk Vk Yk 1| ≤ 3 * K ^ 3 := by
  have hK0 : 0 ≤ K := by linarith
  have hZ' : |Zk - b 0| ≤ χ := by simpa only [abs_sub_comm] using hZ
  have hV' : |Vk - b 3| ≤ χ := by simpa only [abs_sub_comm] using hV
  have hχq : χ ≤ F.q := hχm.trans
    ((mul_le_mul_of_nonneg_left hg₁ hq.le).trans_eq (mul_one _))
  have hS : |F.c 3 + F.c 4 * Vk + Zk| ≤ 5 * K ^ 2 * F.q := by
    have hid : F.c 3 + F.c 4 * Vk + Zk =
        (F.c 3 + F.c 0 + (F.t₀ + F.q / 2) * F.c 1) +
        (b 0 + (F.t₀ + F.q / 2) * b 3 - F.c 0 - (F.t₀ + F.q / 2) * F.c 1) +
        (F.c 4 - (F.t₀ + F.q / 2)) * b 3 + (Zk - b 0) + F.c 4 * (Vk - b 3) := by ring
    rw [hid]
    have htri := abs_add_le (F.c 3 + F.c 0 + (F.t₀ + F.q / 2) * F.c 1)
      (b 0 + (F.t₀ + F.q / 2) * b 3 - F.c 0 - (F.t₀ + F.q / 2) * F.c 1)
    calc
      _ ≤ |F.c 3 + F.c 0 + (F.t₀ + F.q / 2) * F.c 1| +
          |b 0 + (F.t₀ + F.q / 2) * b 3 - F.c 0 - (F.t₀ + F.q / 2) * F.c 1| +
          |F.c 4 - (F.t₀ + F.q / 2)| * |b 3| + |Zk - b 0| + |F.c 4| * |Vk - b 3| := by
        simp only [← abs_mul]
        calc
          _ ≤ |(F.c 3 + F.c 0 + (F.t₀ + F.q / 2) * F.c 1) +
              (b 0 + (F.t₀ + F.q / 2) * b 3 - F.c 0 - (F.t₀ + F.q / 2) * F.c 1) +
              (F.c 4 - (F.t₀ + F.q / 2)) * b 3 + (Zk - b 0)| + |F.c 4 * (Vk - b 3)| := abs_add_le _ _
          _ ≤ _ := by
            have h1 := abs_add_le ((F.c 3 + F.c 0 + (F.t₀ + F.q / 2) * F.c 1) +
              (b 0 + (F.t₀ + F.q / 2) * b 3 - F.c 0 - (F.t₀ + F.q / 2) * F.c 1) +
              (F.c 4 - (F.t₀ + F.q / 2)) * b 3) (Zk - b 0)
            have h2 := abs_add_le ((F.c 3 + F.c 0 + (F.t₀ + F.q / 2) * F.c 1) +
              (b 0 + (F.t₀ + F.q / 2) * b 3 - F.c 0 - (F.t₀ + F.q / 2) * F.c 1))
              ((F.c 4 - (F.t₀ + F.q / 2)) * b 3)
            linarith
      _ ≤ K * F.q + K * F.q + (K * F.q) * K + χ + K * χ := by
        gcongr
      _ ≤ _ := by
        have hKq : K * F.q ≤ K ^ 2 * F.q :=
          mul_le_mul_of_nonneg_right (by nlinarith : K ≤ K ^ 2) hq.le
        have hqK : F.q ≤ K * F.q := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hK hq.le
        linarith [mul_le_mul_of_nonneg_left hχq hK0]
  change |(F.c 3 + F.c 4 * Vk + Zk) / (2 * F.g)| ≤ _
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * F.g)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * F.g)).mpr
  have hmul := mul_le_mul_of_nonneg_left hqg (by positivity : 0 ≤ 5 * K ^ 2)
  nlinarith [show 0 ≤ K ^ 3 * F.g by positivity]

/-- Combine the two occupied-sample bounds in the uniform fourth-power form
used by the original common-field menu. -/
theorem chartBeta_total_bound (F : CellFrame) {K Zk Vk Yk : ℝ} (hK : 1 ≤ K)
    (hzero : |chartBeta F Zk Vk Yk 0| ≤ 3 * K)
    (hone : |chartBeta F Zk Vk Yk 1| ≤ 3 * K ^ 3) :
    |chartBeta F Zk Vk Yk 0| + |chartBeta F Zk Vk Yk 1| ≤ 8 * K ^ 4 := by
  have hK0 : 0 ≤ K := by linarith
  have hK₂ : 1 ≤ K ^ 2 := by nlinarith
  have hK₃ : K ≤ K ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hK₂ hK0
    nlinarith
  have hK₄ : K ^ 3 ≤ K ^ 4 := by
    have h := mul_le_mul_of_nonneg_left hK (pow_nonneg hK0 3)
    nlinarith
  linarith [hK₃.trans hK₄, pow_nonneg hK0 4]

end KeyFrame
end Submission.Obl.k4_wide_three_layer_scalar_inputs
