import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.NumFacts

/-!
# Sample numerics, continued

Deep-label scale, ancestor slope at the Scalar cell, cap numerics, and the cell spreads of a
candidate label.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Candidate-label scales. -/
theorem fc_scales (D : CoreData α) (H : CoreHyp D) :
    D.fc.q ≤ D.K * D.N ^ (-D.κ * D.sc) ∧ D.N ^ (-D.κ * D.sc) ≤ D.K * D.fc.q :=
  fam_q_bounds H.fcgood (by linarith [H.N2]) (by linarith [H.K1])

/-- Deep labels are small against Scalar cells. -/
theorem num_qe (D : CoreData α) (H : CoreHyp D) {η m : ℝ} (hKη : D.K ≤ D.N ^ η)
    (hbig : 3 * D.N ^ (3 * η - D.κ * D.se + D.κ * D.sc + m) ≤ 1) :
    D.fe.q / D.fc.q ≤ D.N ^ (-m) ∧ 3 * D.K * D.fe.q / D.fc.q ≤ D.N ^ (-m) := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  obtain ⟨he1, -⟩ := fam_q_bounds H.fegood hN0 hK0
  obtain ⟨-, hc2⟩ := fc_scales D H
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hqe : 0 < D.fe.q := by unfold Fam.q; positivity
  have hgc : 0 < D.N ^ (-D.κ * D.sc) := Real.rpow_pos_of_pos hN0 _
  have hK3 : D.K ^ 3 ≤ D.N ^ (3 * η) := by
    have := pow_le_rpow_mul hK1 hKη hN0 3; simpa using this
  -- 3 K qe / qc ≤ 3 K^3 ge / gc
  have hmain : 3 * D.K * D.fe.q / D.fc.q ≤ 3 * D.K ^ 3 * (D.N ^ (-D.κ * D.se) / D.N ^ (-D.κ * D.sc)) := by
    rw [div_le_iff₀ hqc]
    have h1 : 3 * D.K * D.fe.q ≤ 3 * D.K * (D.K * D.N ^ (-D.κ * D.se)) :=
      mul_le_mul_of_nonneg_left he1 (by positivity)
    have h2 : D.N ^ (-D.κ * D.sc) / D.fc.q ≤ D.K := by rw [div_le_iff₀ hqc]; linarith
    calc 3 * D.K * D.fe.q ≤ 3 * D.K * (D.K * D.N ^ (-D.κ * D.se)) := h1
      _ = 3 * D.K ^ 2 * D.N ^ (-D.κ * D.se) / D.N ^ (-D.κ * D.sc) * D.N ^ (-D.κ * D.sc) := by
          field_simp
      _ ≤ 3 * D.K ^ 2 * D.N ^ (-D.κ * D.se) / D.N ^ (-D.κ * D.sc) * (D.K * D.fc.q) := by
          gcongr
      _ = 3 * D.K ^ 3 * (D.N ^ (-D.κ * D.se) / D.N ^ (-D.κ * D.sc)) * D.fc.q := by ring
  have hratio : D.N ^ (-D.κ * D.se) / D.N ^ (-D.κ * D.sc) = D.N ^ (-D.κ * D.se + D.κ * D.sc) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hN0.le, rpow_mul_rpow hN0]; congr 1; ring
  have hb := le_rpow_of_big hN0 (C := 3) (x := 3 * η + (-D.κ * D.se + D.κ * D.sc)) (y := -m) (by
    have e : 3 * η + (-D.κ * D.se + D.κ * D.sc) - -m = 3 * η - D.κ * D.se + D.κ * D.sc + m := by
      ring
    rw [e]; exact hbig)
  rw [← rpow_mul_rpow hN0] at hb
  have h3 : 3 * D.K * D.fe.q / D.fc.q ≤ D.N ^ (-m) := by
    refine hmain.trans ?_
    rw [hratio]
    calc 3 * D.K ^ 3 * D.N ^ (-D.κ * D.se + D.κ * D.sc)
        ≤ 3 * D.N ^ (3 * η) * D.N ^ (-D.κ * D.se + D.κ * D.sc) := by gcongr
      _ ≤ D.N ^ (-m) := by rw [mul_assoc]; exact hb
  refine ⟨le_trans ?_ h3, h3⟩
  rw [mul_div_assoc]
  exact le_mul_of_one_le_left (by positivity) (by linarith)

/-- A Scalar cell is small against the ancestor's slope. -/
theorem num_Λ (D : CoreData α) (H : CoreHyp D) {η m s : ℝ} (hKη : D.K ≤ D.N ^ η)
    (hDa : D.Dw ≤ D.a₀) (hq0 : D.N ^ (-D.κ * D.s₀) ≤ D.K * D.f₀.q) (hgc1 : D.N ^ (-D.κ * D.sc) ≤ 1)
    (hbig : 24 * D.N ^ (5 * η - m + 2 * D.κ * D.s₀ + s) ≤ 1) :
    6 * D.Λa * (D.N ^ (-m) * D.fc.q) ≤ D.a₀ * D.N ^ (-s) := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hDw0 : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hΛ := Λa_le D H hDa hq0
  have hΛ0 : 0 ≤ D.Λa := by unfold CoreData.Λa; have := f₀_q_pos D; positivity
  obtain ⟨hc1, -⟩ := fc_scales D H
  have hσ0 : 0 < D.N ^ (-m) := Real.rpow_pos_of_pos hN0 _
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hqcK : D.fc.q ≤ D.K := hc1.trans (mul_le_of_le_one_right hK0.le hgc1)
  have hK5 : D.K ^ 5 ≤ D.N ^ (5 * η) := by
    have := pow_le_rpow_mul hK1 hKη hN0 5; simpa using this
  have hDinv : 1 / D.Dw = D.N ^ (2 * D.κ * D.s₀) := by
    unfold CoreData.Dw; rw [one_div, ← Real.rpow_neg hN0.le]; congr 1; ring
  have hb := le_rpow_of_big hN0 (C := 24) (x := 5 * η + (-m) + 2 * D.κ * D.s₀) (y := -s) (by
    have e : 5 * η + -m + 2 * D.κ * D.s₀ - -s = 5 * η - m + 2 * D.κ * D.s₀ + s := by ring
    rw [e]; exact hbig)
  rw [← rpow_mul_rpow hN0, ← rpow_mul_rpow hN0] at hb
  calc 6 * D.Λa * (D.N ^ (-m) * D.fc.q) ≤ 6 * (4 * D.K ^ 4 * (D.a₀ / D.Dw)) * (D.N ^ (-m) * D.K) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hΛ (by norm_num))
          (mul_le_mul_of_nonneg_left hqcK hσ0.le) (by positivity) (by positivity)
    _ = 24 * D.K ^ 5 * D.N ^ (-m) * (1 / D.Dw) * D.a₀ := by ring
    _ ≤ 24 * D.N ^ (5 * η) * D.N ^ (-m) * D.N ^ (2 * D.κ * D.s₀) * D.a₀ := by
        rw [hDinv]; gcongr
    _ ≤ D.N ^ (-s) * D.a₀ := by
        apply mul_le_mul_of_nonneg_right _ ha0.le
        calc 24 * D.N ^ (5 * η) * D.N ^ (-m) * D.N ^ (2 * D.κ * D.s₀)
            = 24 * (D.N ^ (5 * η) * D.N ^ (-m) * D.N ^ (2 * D.κ * D.s₀)) := by ring
          _ ≤ D.N ^ (-s) := hb
    _ = D.a₀ * D.N ^ (-s) := mul_comm _ _

/-- The cell's second-position spread. -/
theorem cellδ2_le (D : CoreData α) (H : CoreHyp D) {m : ℝ} (hσgc : D.N ^ (-m) ≤ D.N ^ (-D.κ * D.sc)) :
    D.cellδ2 (D.N ^ (-m)) ≤ 4 * D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2 := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  obtain ⟨hc1, -⟩ := fc_scales D H
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hσ0 : 0 < D.N ^ (-m) := Real.rpow_pos_of_pos hN0 _
  have hgc0 : 0 < D.N ^ (-D.κ * D.sc) := Real.rpow_pos_of_pos hN0 _
  unfold CoreData.cellδ2
  have h1 : D.K * (D.N ^ (-m) * D.fc.q) ≤ D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2 := by
    calc D.K * (D.N ^ (-m) * D.fc.q) ≤ D.K * (D.N ^ (-D.κ * D.sc) * (D.K * D.N ^ (-D.κ * D.sc))) := by
          gcongr
      _ = D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2 := by ring
  have h2 : 2 * (D.K * D.fc.q * D.N ^ (-D.κ * D.sc)) ≤ 2 * (D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2) := by
    have : D.K * D.fc.q * D.N ^ (-D.κ * D.sc) ≤ D.K * (D.K * D.N ^ (-D.κ * D.sc)) * D.N ^ (-D.κ * D.sc) := by
      gcongr
    nlinarith
  linarith

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
