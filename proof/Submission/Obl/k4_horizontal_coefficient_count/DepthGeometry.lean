import Submission.Obl.k4_horizontal_coefficient_count.DepthBasics

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set

noncomputable section
namespace DepthData

variable {α : Type} [MeasurableSpace α] {D : DepthData α} (h : D.Hyp)
include h

theorem Hyp.enlarged_true_bounds (i : Fin D.n) {l : α} (hl : l ∈ D.B i)
    {t : ℝ} (ht : t ∈ tblock D.q (D.j i)) :
    |t - D.midpoint (D.j i)| ≤ D.K * D.q / 2 ∧
    |X1 (D.b l) t - D.c i 0 - t * D.c i 1| ≤ (8 * D.K ^ 2) * (D.K * D.q) ∧
    |X2 (D.b l) t - D.c i 2 - t * D.c i 3 - D.c i 4 * X1 (D.b l) t| ≤
      (8 * D.K ^ 2) * (D.K * D.q) ^ 2 := by
  have hK0 : 0 ≤ D.K := by linarith [h.hK]
  have hq := h.q_pos
  have hG : 1 ≤ 8 * D.K ^ 2 := by nlinarith [h.hK]
  have hqH : D.q ≤ D.K * D.q := by nlinarith [h.hK]
  refine ⟨(h.block_time_gap _ ht).trans (by linarith), ?_, ?_⟩
  · exact (h.h1 i l (h.hBA i hl) t ht).trans (le_mul_of_one_le_left (by positivity) hG)
  · calc
      _ ≤ D.K * D.q * D.g := h.h2 i l (h.hBA i hl) t ht
      _ ≤ (D.K * D.q) ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left h.hgq (mul_nonneg hK0 hq.le)]
      _ ≤ _ := le_mul_of_one_le_left (sq_nonneg _) hG

theorem Hyp.enlarged_center_tilt (i : Fin D.n) :
    |D.c i 3 + D.c i 0 + D.midpoint (D.j i) * D.c i 1| ≤
      (8 * D.K ^ 2) * (D.K * D.q) ∧
    |D.c i 4 - D.midpoint (D.j i)| ≤ (8 * D.K ^ 2) * (D.K * D.q) := by
  have hG : 1 ≤ 8 * D.K ^ 2 := by nlinarith [h.hK]
  have hH : 0 ≤ D.K * D.q := mul_nonneg (by linarith [h.hK]) h.q_pos.le
  have hh := h.h3 i
  change |D.c i 3 + D.c i 0 + D.midpoint (D.j i) * D.c i 1| +
    |D.c i 4 - D.midpoint (D.j i)| ≤ D.K * D.q at hh
  have hu : D.K * D.q ≤ (8 * D.K ^ 2) * (D.K * D.q) := le_mul_of_one_le_left hH hG
  constructor
  · exact (le_trans (by linarith [abs_nonneg (D.c i 4 - D.midpoint (D.j i))]) hh).trans hu
  · exact (le_trans (by linarith [abs_nonneg (D.c i 3 + D.c i 0 + D.midpoint (D.j i) * D.c i 1)]) hh).trans hu

theorem Hyp.a_le_enlarged_square : D.a ≤ (D.K * D.q) ^ 2 := by
  calc
    _ ≤ D.q ^ 2 := h.haq
    _ ≤ _ := pow_le_pow_left₀ h.q_pos.le (by nlinarith [h.hK, h.q_pos]) 2

theorem Hyp.reference_midpoint_bounds (g : ℤ × ℤ × ℤ) {l : α}
    (hg : l ∈ groupSet D.b D.χ D.a g) (hl : l ∈ goodSet D.b D.K D.χ)
    (j : Fin (2 ^ D.T)) :
    |D.groupReference g 2| ≤ 8 * D.K ^ 2 ∧
    |D.groupReference g 0 + D.midpoint j * D.groupReference g 2| ≤ 8 * D.K ^ 2 := by
  obtain ⟨hp, hv⟩ := h.reference_coefficient_bounds g hg hl
  have hm := h.midpoint_abs_le_one j
  refine ⟨hv.trans (by nlinarith [h.hK]), ?_⟩
  calc
    _ ≤ |D.groupReference g 0| + |D.midpoint j| * |D.groupReference g 2| := by
      simpa only [abs_mul] using abs_add_le (D.groupReference g 0) (D.midpoint j * D.groupReference g 2)
    _ ≤ 2 * D.K + 1 * (2 * D.K) := by gcongr
    _ ≤ _ := by nlinarith [h.hK]

theorem Hyp.large_block_mass_bound (hlong : 1 < D.K * D.q) :
    D.K ≤ (33554432 * D.K ^ 12) * D.q ^ 4 := by
  have hK : 0 < D.K := by linarith [h.hK]
  have hlong' : 1 ≤ (D.K * D.q) ^ 4 := one_le_pow₀ hlong.le
  have hKpow : D.K ≤ D.K ^ 8 := le_self_pow₀ h.hK (by norm_num)
  calc
    D.K ≤ D.K ^ 8 * (D.K * D.q) ^ 4 := hKpow.trans (by simpa using mul_le_mul_of_nonneg_left hlong' (pow_nonneg hK.le 8))
    _ = D.K ^ 12 * D.q ^ 4 := by ring
    _ ≤ (33554432 * D.K ^ 12) * D.q ^ 4 := by
      have hp : 0 ≤ D.K ^ 12 * D.q ^ 4 := mul_nonneg (pow_nonneg hK.le 12) (pow_nonneg h.q_pos.le 4)
      nlinarith only [hp]

end DepthData
end
end Submission.Obl.k4_horizontal_coefficient_count
