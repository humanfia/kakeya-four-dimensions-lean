import Submission.Obl.k4_horizontal_coefficient_count.DepthBasics

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set

noncomputable section

namespace DepthData

variable {α : Type} [MeasurableSpace α] {D : DepthData α} (h : D.Hyp)

include h

theorem Hyp.affine_entry_coefficients (i : Fin D.n) {l : α} (hlB : l ∈ D.B i)
    (hl : l ∈ goodSet D.b D.K D.χ) {t : ℝ} (ht : t ∈ tblock D.q (D.j i)) :
    |D.L i 1| ≤ 4 * D.K ^ 2 ∧ |D.L i 2| ≤ 4 * D.K ∧ |D.L i 3| ≤ 2 * D.K := by
  have hK0 : 0 ≤ D.K := by linarith [h.hK]
  have hq := h.q_pos
  have hunit := h.block_subset_unit (D.j i) ht
  have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg hunit.1] using hunit.2
  have hpos := (h.good_position_bounds hl hunit).1
  have hL3 : |D.L i 3| ≤ 2 * D.K := by
    have hratio : D.a / D.q ^ 2 ≤ 1 := (div_le_iff₀ (sq_pos_of_pos hq)).mpr (by simpa using h.haq)
    have hh := h.hL3 i
    nlinarith [mul_le_mul_of_nonneg_left hratio hK0]
  have hgrad : |D.L i 1 - X1 (D.b l) t * D.L i 3| + |D.L i 2 + t * D.L i 3| ≤ 2 * D.K := by
    have hratio : D.a / D.q ≤ 1 := (div_le_iff₀ hq).mpr (by simpa using h.a_le_q)
    have hh := h.hL12 i l hlB t ht
    nlinarith [mul_le_mul_of_nonneg_left hratio hK0]
  have hL1 : |D.L i 1| ≤ 4 * D.K ^ 2 := by
    calc
      _ = |(D.L i 1 - X1 (D.b l) t * D.L i 3) + X1 (D.b l) t * D.L i 3| := by congr 1; ring
      _ ≤ |D.L i 1 - X1 (D.b l) t * D.L i 3| + |X1 (D.b l) t| * |D.L i 3| := by
        simpa only [abs_mul] using abs_add_le (D.L i 1 - X1 (D.b l) t * D.L i 3) (X1 (D.b l) t * D.L i 3)
      _ ≤ 2 * D.K + D.K * (2 * D.K) := by
        apply add_le_add
        · linarith [abs_nonneg (D.L i 2 + t * D.L i 3)]
        · exact mul_le_mul hpos hL3 (abs_nonneg _) hK0
      _ ≤ 4 * D.K ^ 2 := by nlinarith [h.hK]
  refine ⟨hL1, ?_, hL3⟩
  calc
    |D.L i 2| = |(D.L i 2 + t * D.L i 3) - t * D.L i 3| := by congr 1; ring
    _ ≤ |D.L i 2 + t * D.L i 3| + |t| * |D.L i 3| := by simpa only [abs_mul] using abs_sub (D.L i 2 + t * D.L i 3) (t * D.L i 3)
    _ ≤ 2 * D.K + 1 * (2 * D.K) := by
      apply add_le_add
      · linarith [abs_nonneg (D.L i 1 - X1 (D.b l) t * D.L i 3)]
      · exact mul_le_mul ht' hL3 (abs_nonneg _) zero_le_one
    _ = 4 * D.K := by ring

omit h in
def labelSignal (D : DepthData α) (g : ℤ × ℤ × ℤ) (i : Fin D.n) (τ : ℤ) : ℝ :=
  D.L i 0 + D.L i 1 * ((τ : ℝ) * D.a) +
    D.L i 2 * (D.groupReference g 0 + ((τ : ℝ) * D.a) * D.groupReference g 2) +
    D.L i 3 * (D.groupReference g 1 - ((τ : ℝ) * D.a) * D.groupReference g 0)

/-- In one scalar time bin, each true affine entry gives one bounded
list of hidden bins for the whole parameter group. -/
theorem Hyp.scalar_near_label_signal (g : ℤ × ℤ × ℤ) (i : Fin D.n) {l : α}
    (hlB : l ∈ D.B i) (hg : l ∈ groupSet D.b D.χ D.a g)
    (hl : l ∈ goodSet D.b D.K D.χ) {t : ℝ} (ht : t ∈ tblock D.q (D.j i)) :
    |X3 (D.b l) t - D.labelSignal g i ⌊t / D.a⌋| ≤ 31 * D.K ^ 2 * D.a := by
  have hK0 : 0 ≤ D.K := by linarith [h.hK]
  have hunit := h.block_subset_unit (D.j i) ht
  obtain ⟨hL1, hL2, hL3⟩ := h.affine_entry_coefficients i hlB hl ht
  obtain ⟨hZ, hY⟩ := h.group_reference_errors g hg hl hunit
  obtain ⟨hp, hv⟩ := h.reference_coefficient_bounds g hg hl
  let τ : ℝ := (⌊t / D.a⌋ : ℝ) * D.a
  have hdt : |t - τ| ≤ D.a := by
    have hlo := (le_div_iff₀ h.ha0).mp (Int.floor_le (t / D.a))
    have hhi := (div_lt_iff₀ h.ha0).mp (Int.lt_floor_add_one (t / D.a))
    rw [abs_of_nonneg (by dsimp [τ]; linarith)]
    dsimp [τ]
    linarith
  let E : ℝ := D.L i 0 + D.L i 1 * t + D.L i 2 * X1 (D.b l) t + D.L i 3 * X2 (D.b l) t
  let Eref : ℝ := D.L i 0 + D.L i 1 * t +
    D.L i 2 * (D.groupReference g 0 + t * D.groupReference g 2) +
    D.L i 3 * (D.groupReference g 1 - t * D.groupReference g 0)
  have hfit : |X3 (D.b l) t - E| ≤ D.K * D.a := h.hfit i l hlB t ht
  have hspace : |E - Eref| ≤ 14 * D.K * D.a := by
    calc
      _ = |D.L i 2 * (X1 (D.b l) t - (D.groupReference g 0 + t * D.groupReference g 2)) +
          D.L i 3 * (X2 (D.b l) t - (D.groupReference g 1 - t * D.groupReference g 0))| := by
        dsimp [E, Eref]; congr 1; ring
      _ ≤ |D.L i 2| * |X1 (D.b l) t - (D.groupReference g 0 + t * D.groupReference g 2)| +
          |D.L i 3| * |X2 (D.b l) t - (D.groupReference g 1 - t * D.groupReference g 0)| := by
        simpa only [abs_mul] using abs_add_le (D.L i 2 * (X1 (D.b l) t - (D.groupReference g 0 + t * D.groupReference g 2))) (D.L i 3 * (X2 (D.b l) t - (D.groupReference g 1 - t * D.groupReference g 0)))
      _ ≤ (4 * D.K) * (2 * D.a) + (2 * D.K) * (3 * D.a) := by gcongr
      _ = 14 * D.K * D.a := by ring
  have hder : |D.L i 1 + D.L i 2 * D.groupReference g 2 - D.L i 3 * D.groupReference g 0| ≤ 16 * D.K ^ 2 := by
    calc
      _ ≤ |D.L i 1| + |D.L i 2| * |D.groupReference g 2| + |D.L i 3| * |D.groupReference g 0| := by
        simpa only [sub_eq_add_neg, abs_neg, abs_mul] using
          abs_add_three (D.L i 1) (D.L i 2 * D.groupReference g 2) (-(D.L i 3 * D.groupReference g 0))
      _ ≤ 4 * D.K ^ 2 + (4 * D.K) * (2 * D.K) + (2 * D.K) * (2 * D.K) := by gcongr
      _ = 16 * D.K ^ 2 := by ring
  have htime : |Eref - D.labelSignal g i ⌊t / D.a⌋| ≤ 16 * D.K ^ 2 * D.a := by
    calc
      _ = |(t - τ) * (D.L i 1 + D.L i 2 * D.groupReference g 2 - D.L i 3 * D.groupReference g 0)| := by
        dsimp [Eref, labelSignal, τ]; congr 1; ring
      _ = |t - τ| * |D.L i 1 + D.L i 2 * D.groupReference g 2 - D.L i 3 * D.groupReference g 0| := abs_mul _ _
      _ ≤ D.a * (16 * D.K ^ 2) := mul_le_mul hdt hder (abs_nonneg _) h.ha0.le
      _ = 16 * D.K ^ 2 * D.a := by ring
  have hsum := abs_add_three (X3 (D.b l) t - E) (E - Eref) (Eref - D.labelSignal g i ⌊t / D.a⌋)
  have heq : X3 (D.b l) t - E + (E - Eref) + (Eref - D.labelSignal g i ⌊t / D.a⌋) =
      X3 (D.b l) t - D.labelSignal g i ⌊t / D.a⌋ := by ring
  rw [heq] at hsum
  have hKsq : D.K ≤ D.K ^ 2 := by nlinarith [h.hK]
  nlinarith [mul_le_mul_of_nonneg_right hKsq h.ha0.le]

end DepthData
end
end Submission.Obl.k4_horizontal_coefficient_count
