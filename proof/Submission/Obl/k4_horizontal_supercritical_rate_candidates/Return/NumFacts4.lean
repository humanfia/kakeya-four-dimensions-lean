import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.NumFacts3

/-!
# Sample numerics: hidden widths of the third pruning and of Scalar values

The hidden spread `cellW0 ≤ 18 K⁵ a_c` of a candidate label in a Scalar cell, the hidden cell
width `W3 ≤ 22 K⁵ E a_c` of the third pruning, and the value spread of one slice in one Scalar
cell, `binSpread ≤ (2E + 3) N^(-s)`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The hidden spread of a candidate label in one Scalar cell. -/
theorem num_W0 (D : CoreData α) (H : CoreHyp D) {m : ℝ}
    (hσgc : D.N ^ (-m) ≤ D.N ^ (-D.κ * D.sc)) (hσ1 : D.N ^ (-m) ≤ 1)
    (hacgc : D.N ^ (-D.sc) ≤ D.N ^ (-D.κ * D.sc))
    (hgcac : (D.N ^ (-D.κ * D.sc)) ^ 2 ≤ D.N ^ (-D.sc)) :
    D.cellW0 (D.N ^ (-m)) ≤ 18 * D.K ^ 5 * D.N ^ (-D.sc) := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  obtain ⟨hc1, hc2⟩ := fc_scales D H
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hσ0 : 0 < D.N ^ (-m) := Real.rpow_pos_of_pos hN0 _
  have hgc0 : 0 < D.N ^ (-D.κ * D.sc) := Real.rpow_pos_of_pos hN0 _
  have hac0 : 0 < D.N ^ (-D.sc) := Real.rpow_pos_of_pos hN0 _
  set σ := D.N ^ (-m) with hσ
  set gc := D.N ^ (-D.κ * D.sc) with hgc
  set ac := D.N ^ (-D.sc) with hac
  set qc := D.fc.q with hqcdef
  clear_value σ gc ac qc
  have hKgc : gc ≤ D.K * gc := le_mul_of_one_le_left hgc0.le hK1
  have hK2 : D.K ≤ D.K ^ 2 := le_self_pow₀ hK1 (by norm_num)
  have hK5 : D.K ^ 2 ≤ D.K ^ 5 := pow_le_pow_right₀ hK1 (by norm_num)
  have hK15 : D.K ≤ D.K ^ 5 := le_self_pow₀ hK1 (by norm_num)
  unfold CoreData.cellW0
  simp only [← hgc, ← hac, ← hqcdef]
  -- second term
  have T2 : D.K * (1 + ac / qc) * (σ * qc + σ * qc) ≤ 4 * D.K ^ 2 * ac := by
    have e : D.K * (1 + ac / qc) * (σ * qc + σ * qc) = 2 * D.K * σ * (qc + ac) := by
      field_simp; ring
    rw [e]
    have h1 : qc + ac ≤ 2 * D.K * gc := by linarith only [hc1, hacgc, hKgc]
    have h2 : σ * (qc + ac) ≤ σ * (2 * D.K * gc) := mul_le_mul_of_nonneg_left h1 hσ0.le
    have h3 : σ * gc ≤ gc * gc := mul_le_mul_of_nonneg_right hσgc hgc0.le
    have h4 : gc * gc ≤ ac := by nlinarith only [hgcac]
    calc 2 * D.K * σ * (qc + ac) = 2 * D.K * (σ * (qc + ac)) := by ring
      _ ≤ 2 * D.K * (σ * (2 * D.K * gc)) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 4 * D.K ^ 2 * (σ * gc) := by ring
      _ ≤ 4 * D.K ^ 2 * ac := mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
  -- third term
  have T3 : D.K * (1 + ac / qc ^ 2) * (5 / 2 * D.K * qc * (σ * qc) + 3 / 2 * D.K * qc * (σ * qc) +
      2 * (D.K * qc * gc)) ≤ 12 * D.K ^ 5 * ac := by
    have hb : 5 / 2 * D.K * qc * (σ * qc) + 3 / 2 * D.K * qc * (σ * qc) + 2 * (D.K * qc * gc) ≤
        6 * D.K ^ 2 * qc ^ 2 := by
      have h1 : D.K * qc * (σ * qc) ≤ D.K * qc ^ 2 := by
        have : σ * qc ≤ qc := mul_le_of_le_one_left hqc.le hσ1
        have := mul_le_mul_of_nonneg_left this (show 0 ≤ D.K * qc by positivity)
        calc D.K * qc * (σ * qc) ≤ D.K * qc * qc := this
          _ = D.K * qc ^ 2 := by ring
      have h2 : D.K * qc * gc ≤ D.K ^ 2 * qc ^ 2 := by
        have := mul_le_mul_of_nonneg_left hc2 (show 0 ≤ D.K * qc by positivity)
        calc D.K * qc * gc ≤ D.K * qc * (D.K * qc) := this
          _ = D.K ^ 2 * qc ^ 2 := by ring
      have h3 : D.K * qc ^ 2 ≤ D.K ^ 2 * qc ^ 2 := mul_le_mul_of_nonneg_right hK2 (sq_nonneg _)
      have e1 : 5 / 2 * D.K * qc * (σ * qc) + 3 / 2 * D.K * qc * (σ * qc) =
          4 * (D.K * qc * (σ * qc)) := by ring
      rw [e1]; linarith only [h1, h2, h3]
    have hA : 0 ≤ D.K * (1 + ac / qc ^ 2) := by positivity
    have e : D.K * (1 + ac / qc ^ 2) * (6 * D.K ^ 2 * qc ^ 2) = 6 * D.K ^ 3 * (qc ^ 2 + ac) := by
      field_simp
    have hq2 : qc ^ 2 ≤ D.K ^ 2 * ac := by
      have h1 : qc ^ 2 ≤ (D.K * gc) ^ 2 := pow_le_pow_left₀ hqc.le hc1 2
      have h2 : (D.K * gc) ^ 2 = D.K ^ 2 * gc ^ 2 := by ring
      have h3 := mul_le_mul_of_nonneg_left hgcac (sq_nonneg D.K)
      linarith only [h1, h2, h3]
    have hac2 : ac ≤ D.K ^ 2 * ac := le_mul_of_one_le_left hac0.le (one_le_pow₀ hK1)
    calc _ ≤ D.K * (1 + ac / qc ^ 2) * (6 * D.K ^ 2 * qc ^ 2) := mul_le_mul_of_nonneg_left hb hA
      _ = 6 * D.K ^ 3 * (qc ^ 2 + ac) := e
      _ ≤ 6 * D.K ^ 3 * (D.K ^ 2 * ac + D.K ^ 2 * ac) :=
          mul_le_mul_of_nonneg_left (add_le_add hq2 hac2) (by positivity)
      _ = 12 * D.K ^ 5 * ac := by ring
  have T1 : 2 * (D.K * ac) ≤ 2 * (D.K ^ 5 * ac) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK15 hac0.le) (by norm_num)
  have T2' : 4 * D.K ^ 2 * ac ≤ 4 * (D.K ^ 5 * ac) := by
    have := mul_le_mul_of_nonneg_right hK5 hac0.le; linarith only [this]
  linarith only [T1, T2, T2', T3]

theorem cellδ2_nonneg (D : CoreData α) (H : CoreHyp D) (σ : ℝ) (hσ : 0 ≤ σ) :
    0 ≤ D.cellδ2 σ := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hg : 0 ≤ D.N ^ (-D.κ * D.sc) := Real.rpow_nonneg hN0.le _
  unfold CoreData.cellδ2
  have h1 : 0 ≤ D.K * (σ * D.fc.q) := mul_nonneg hK0 (mul_nonneg hσ hqc.le)
  have h2 : 0 ≤ D.K * D.fc.q * D.N ^ (-D.κ * D.sc) := mul_nonneg (mul_nonneg hK0 hqc.le) hg
  linarith only [h1, h2]

theorem crossLip_nonneg' (D : CoreData α) (H : CoreHyp D) {K₁ B : ℝ} (hB : 0 ≤ B) :
    0 ≤ D.crossLip D.M D.Dw K₁ B := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hDw0 : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hχ0 : 0 < D.N ^ (-D.M) := Real.rpow_pos_of_pos hN0 _
  unfold CoreData.crossLip
  have hc := crossB_pos D.d ((D.crossEa D.M D.Dw + D.crossEb D.M B + D.crossG D.M D.Dw B *
    D.N ^ (-D.M)) / D.a₀) (D.crossCs D.M D.Dw K₁) (D.crossTheta D.M D.Dw K₁ B)
  have h1 : 0 ≤ 14 * crossB D.d ((D.crossEa D.M D.Dw + D.crossEb D.M B + D.crossG D.M D.Dw B *
      D.N ^ (-D.M)) / D.a₀) (D.crossCs D.M D.Dw K₁) (D.crossTheta D.M D.Dw K₁ B) * D.a₀ /
      (D.Dw + 2 * D.N ^ (-D.M)) := by
    apply div_nonneg _ (by linarith only [hDw0, hχ0])
    exact mul_nonneg (mul_nonneg (by norm_num) hc.le) ha0.le
  have h2 : 0 ≤ 9 * B * (2 * D.N ^ (-D.M)) := by
    exact mul_nonneg (mul_nonneg (by norm_num) hB) (by linarith only [hχ0])
  linarith only [h1, h2]

/-- The ancestor slope over a Scalar cell is below one terminal width. -/
theorem num_Λδ (D : CoreData α) (H : CoreHyp D) {η m : ℝ} (hKη : D.K ≤ D.N ^ η)
    (hDa : D.Dw ≤ D.a₀) (hq0 : D.N ^ (-D.κ * D.s₀) ≤ D.K * D.f₀.q)
    (hσgc : D.N ^ (-m) ≤ D.N ^ (-D.κ * D.sc))
    (hbig : 24 * D.N ^ (6 * η - D.s₀ + 2 * D.κ * D.s₀ - 2 * D.κ * D.sc + D.s₁) ≤ 1) :
    D.Λa * (D.N ^ (-m) * D.fc.q + D.N ^ (-m) * D.fc.q + D.cellδ2 (D.N ^ (-m))) ≤ D.a₁ := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  obtain ⟨hc1, -⟩ := fc_scales D H
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hσ0 : 0 < D.N ^ (-m) := Real.rpow_pos_of_pos hN0 _
  have hgc0 : 0 < D.N ^ (-D.κ * D.sc) := Real.rpow_pos_of_pos hN0 _
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hDw0 : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hΛ := Λa_le D H hDa hq0
  have hΛ0 : 0 ≤ D.Λa := by unfold CoreData.Λa; have := f₀_q_pos D; positivity
  have hδ := cellδ2_le D H hσgc
  have hσq : D.N ^ (-m) * D.fc.q ≤ D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2 := by
    calc D.N ^ (-m) * D.fc.q ≤ D.N ^ (-D.κ * D.sc) * (D.K * D.N ^ (-D.κ * D.sc)) :=
          mul_le_mul hσgc hc1 hqc.le hgc0.le
      _ = D.K * (D.N ^ (-D.κ * D.sc)) ^ 2 := by ring
      _ ≤ D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2 :=
          mul_le_mul_of_nonneg_right (le_self_pow₀ hK1 (by norm_num)) (sq_nonneg _)
  have hsum : D.N ^ (-m) * D.fc.q + D.N ^ (-m) * D.fc.q + D.cellδ2 (D.N ^ (-m)) ≤
      6 * D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2 := by linarith only [hσq, hδ]
  have hK6 : D.K ^ 6 ≤ D.N ^ (6 * η) := by
    have := pow_le_rpow_mul hK1 hKη hN0 6; simpa using this
  have hgc2 : (D.N ^ (-D.κ * D.sc)) ^ 2 = D.N ^ (-2 * D.κ * D.sc) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hDinv : D.a₀ / D.Dw = D.N ^ (-D.s₀ + 2 * D.κ * D.s₀) := by
    unfold CoreData.a₀ CoreData.Dw
    rw [div_eq_mul_inv, ← Real.rpow_neg hN0.le, rpow_mul_rpow hN0]; congr 1; ring
  have hb := le_rpow_of_big hN0 (C := 24) (x := 6 * η + (-D.s₀ + 2 * D.κ * D.s₀) +
    (-2 * D.κ * D.sc)) (y := -D.s₁) (by
      have e : 6 * η + (-D.s₀ + 2 * D.κ * D.s₀) + (-2 * D.κ * D.sc) - -D.s₁ =
          6 * η - D.s₀ + 2 * D.κ * D.s₀ - 2 * D.κ * D.sc + D.s₁ := by ring
      rw [e]; exact hbig)
  rw [← rpow_mul_rpow hN0, ← rpow_mul_rpow hN0] at hb
  calc D.Λa * (D.N ^ (-m) * D.fc.q + D.N ^ (-m) * D.fc.q + D.cellδ2 (D.N ^ (-m)))
      ≤ (4 * D.K ^ 4 * (D.a₀ / D.Dw)) * (6 * D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2) :=
        mul_le_mul hΛ hsum (by
          have h1 : 0 ≤ D.cellδ2 (D.N ^ (-m)) := cellδ2_nonneg D H _ hσ0.le
          have h2 : 0 ≤ D.N ^ (-m) * D.fc.q := mul_nonneg hσ0.le hqc.le
          linarith only [h1, h2]) (by positivity)
    _ = 24 * D.K ^ 6 * (D.N ^ (-D.s₀ + 2 * D.κ * D.s₀) * D.N ^ (-2 * D.κ * D.sc)) := by
        rw [hDinv, hgc2]; ring
    _ ≤ 24 * D.N ^ (6 * η) * (D.N ^ (-D.s₀ + 2 * D.κ * D.s₀) * D.N ^ (-2 * D.κ * D.sc)) := by
        gcongr
    _ ≤ D.N ^ (-D.s₁) := by
        calc 24 * D.N ^ (6 * η) * (D.N ^ (-D.s₀ + 2 * D.κ * D.s₀) * D.N ^ (-2 * D.κ * D.sc))
            = 24 * (D.N ^ (6 * η) * D.N ^ (-D.s₀ + 2 * D.κ * D.s₀) * D.N ^ (-2 * D.κ * D.sc)) := by
              ring
          _ ≤ D.N ^ (-D.s₁) := hb
    _ = D.a₁ := rfl

/-- The hidden cell width of the third pruning. -/
theorem num_W3 (D : CoreData α) (H : CoreHyp D) {K₁ C₀ m : ℝ} (hεL0 : 0 ≤ D.εL)
    (hW0 : D.cellW0 (D.N ^ (-m)) ≤ 18 * D.K ^ 5 * D.N ^ (-D.sc))
    (hlip : D.crossLip D.M D.Dw K₁ (D.Bnat C₀) * D.cellδ2 (D.N ^ (-m)) ≤ D.a₁)
    (hF1 : 18 * D.Bnat C₀ * D.N ^ (-D.M) * (1 + D.K + D.K ^ 2) ≤ D.a₁)
    (hr3 : D.N ^ (-D.r3 (D.N ^ (-m))) ≤ D.N ^ (-D.M)) (ha1c : D.a₁ ≤ D.N ^ (-D.sc))
    (hC₀ : 0 < C₀) :
    2 * D.N ^ D.εL * D.a₁ ≤ D.W3 K₁ C₀ (D.N ^ (-m)) ∧
    D.W3 K₁ C₀ (D.N ^ (-m)) ≤ 22 * D.K ^ 5 * D.N ^ D.εL * D.N ^ (-D.sc) := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  have hE1 : 1 ≤ D.N ^ D.εL := Real.one_le_rpow hN1 hεL0
  have hB0 : 0 ≤ D.Bnat C₀ := by unfold CoreData.Bnat; positivity
  have hP : 0 ≤ 1 + D.K + D.K ^ 2 := by positivity
  have h9 : 9 * D.Bnat C₀ * (2 * D.N ^ (-D.r3 (D.N ^ (-m)))) * (1 + D.K + D.K ^ 2) ≤ D.a₁ := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hr3 (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity : 0 ≤ 9 * D.Bnat C₀)) hP
    linarith only [this, hF1]
  have hW00 : 0 ≤ D.cellW0 (D.N ^ (-m)) := by
    unfold CoreData.cellW0; have : 0 < D.fc.q := by unfold Fam.q; positivity
    positivity
  have h90 : 0 ≤ 9 * D.Bnat C₀ * (2 * D.N ^ (-D.r3 (D.N ^ (-m)))) * (1 + D.K + D.K ^ 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hB0)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg hN0.le _))) hP
  have hlip0 : 0 ≤ D.crossLip D.M D.Dw K₁ (D.Bnat C₀) * D.cellδ2 (D.N ^ (-m)) :=
    mul_nonneg (crossLip_nonneg' D H hB0) (cellδ2_nonneg D H _ (Real.rpow_nonneg hN0.le _))
  unfold CoreData.W3
  constructor
  · linarith only [hW00, hlip0, h90]
  · have hE : D.N ^ D.εL * D.a₁ ≤ D.N ^ D.εL * D.N ^ (-D.sc) :=
      mul_le_mul_of_nonneg_left ha1c (by positivity)
    have h1 : D.a₁ ≤ D.N ^ D.εL * D.N ^ (-D.sc) :=
      ha1c.trans (le_mul_of_one_le_left (by positivity) hE1)
    have h2 : 18 * D.K ^ 5 * D.N ^ (-D.sc) ≤ 18 * D.K ^ 5 * D.N ^ D.εL * D.N ^ (-D.sc) := by
      have := mul_le_mul_of_nonneg_left hE1 (show 0 ≤ 18 * D.K ^ 5 * D.N ^ (-D.sc) by positivity)
      linarith only [this]
    have h3 : D.N ^ D.εL * D.N ^ (-D.sc) ≤ D.K ^ 5 * D.N ^ D.εL * D.N ^ (-D.sc) := by
      have := mul_le_mul_of_nonneg_right (one_le_pow₀ (n := 5) hK1)
        (show 0 ≤ D.N ^ D.εL * D.N ^ (-D.sc) by positivity)
      linarith only [this]
    linarith only [hW0, hlip, h9, hE, h1, h2, h3]

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
