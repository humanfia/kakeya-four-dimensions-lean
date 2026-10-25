import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.NumFacts4

/-!
# Sample numerics: value spread and the support count

The value spread of one slice in one Scalar cell is at most `(2E + 3)` terminal bins, and the
support count of Scalar holds with room `N^ηS`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- The value spread of one slice in one Scalar cell. -/
theorem num_bs (D : CoreData α) (H : CoreHyp D) {K₁ C₀ m s : ℝ} (hεL0 : 0 ≤ D.εL)
    (hs : s = D.s₁ - D.s₀)
    (hlip : D.crossLip D.M D.Dw K₁ (D.Bnat C₀) * D.cellδ2 (D.N ^ (-m)) ≤ D.a₁)
    (hF1 : 18 * D.Bnat C₀ * D.N ^ (-D.M) * (1 + D.K + D.K ^ 2) ≤ D.a₁)
    (hσM : D.N ^ (-m) * D.fc.q ≤ D.N ^ (-D.M))
    (hΛδ : D.Λa * (D.N ^ (-m) * D.fc.q + D.N ^ (-m) * D.fc.q + D.cellδ2 (D.N ^ (-m))) ≤ D.a₁)
    (hC₀ : 0 < C₀) :
    D.binSpread D.M D.Dw K₁ (D.Bnat C₀) (D.N ^ (-m)) / D.N ^ (-s) ≤ 2 * D.N ^ D.εL + 3 := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hK0 : 0 ≤ D.K := by linarith [H.K1]
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have ha1 : 0 < D.a₁ := Real.rpow_pos_of_pos hN0 _
  have hat : 0 < D.N ^ (-s) := Real.rpow_pos_of_pos hN0 _
  have hB0 : 0 ≤ D.Bnat C₀ := by unfold CoreData.Bnat; positivity
  have hP : 0 ≤ 1 + D.K + D.K ^ 2 := by positivity
  have h9 : 9 * D.Bnat C₀ * (2 * (D.N ^ (-m) * D.fc.q)) * (1 + D.K + D.K ^ 2) ≤ D.a₁ := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hσM (by norm_num : (0 : ℝ) ≤ 2))
      (by positivity : 0 ≤ 9 * D.Bnat C₀)) hP
    linarith only [this, hF1]
  have hat_eq : D.N ^ (-s) = D.a₁ / D.a₀ := by
    unfold CoreData.a₀ CoreData.a₁
    rw [hs, div_eq_mul_inv, ← Real.rpow_neg hN0.le, rpow_mul_rpow hN0]; congr 1; ring
  unfold CoreData.binSpread
  rw [hat_eq, div_div_div_cancel_right₀ ha0.ne', div_le_iff₀ ha1]
  linarith only [hlip, h9, hΛδ]

/-- Scalar's support numerics. -/
theorem num_supp (D : CoreData α) (H : CoreHyp D) {η η₁ ηS C₀ m s : ℝ}
    (hs : s = D.s₁ - D.s₀) (hεL0 : 0 ≤ D.εL) (hεLη : D.εL ≤ η) (hKη : D.K ≤ D.N ^ η)
    (hη₁ : 0 ≤ η₁) (hd0 : 0 ≤ D.d) (hd1 : D.d < 1) (hσ1 : D.N ^ (-m) ≤ 1)
    (hr3eq : D.N ^ (-D.r3 (D.N ^ (-m))) = D.N ^ (-m) * D.fc.q)
    (hW3 : D.W3 (D.N ^ η₁) C₀ (D.N ^ (-m)) ≤ 22 * D.K ^ 5 * D.N ^ D.εL * D.N ^ (-D.sc))
    (hW3lo : 0 < D.W3 (D.N ^ η₁) C₀ (D.N ^ (-m)))
    (hbs : D.binSpread D.M D.Dw (D.N ^ η₁) (D.Bnat C₀) (D.N ^ (-m)) / D.N ^ (-s) ≤
      2 * D.N ^ D.εL + 3)
    (hbig : 11258676 * D.N ^ (11 * η + 2 * η₁ - ηS) ≤ 1) (hC₀ : 0 < C₀) :
    (2 * ((⌊(2 * D.K + 1) / D.N ^ (-m)⌋₊ : ℝ) + 1) + 1) ^ 2 *
        (D.K * D.N ^ η₁ * (D.nmax D.M D.Dw (D.N ^ η₁) (D.Bnat C₀) (D.r3 (D.N ^ (-m)))
          (D.cellδ2 (D.N ^ (-m))) (D.W3 (D.N ^ η₁) C₀ (D.N ^ (-m))) (D.N ^ (-m)) (D.N ^ (-s)) : ℝ)) *
          (D.N ^ (-m)) ^ 2 ≤
      D.N ^ ηS * ((D.a₀ / D.ac) ^ D.d)⁻¹ * (D.N ^ (-s)) ^ (-D.d) := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  have hE1 : 1 ≤ D.N ^ D.εL := Real.one_le_rpow hN1 hεL0
  have hK₁1 : 1 ≤ D.N ^ η₁ := Real.one_le_rpow hN1 hη₁
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hσ0 : 0 < D.N ^ (-m) := Real.rpow_pos_of_pos hN0 _
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have ha1 : 0 < D.a₁ := Real.rpow_pos_of_pos hN0 _
  have hac : 0 < D.ac := Real.rpow_pos_of_pos hN0 _
  have hat : 0 < D.N ^ (-s) := Real.rpow_pos_of_pos hN0 _
  set σ := D.N ^ (-m) with hσdef
  set E := D.N ^ D.εL with hEdef
  set K₁ := D.N ^ η₁ with hK₁def
  set h₃ := D.N ^ (-D.r3 σ) with hh₃
  set b₃ := D.cellδ2 σ with hb₃
  set W := D.W3 K₁ C₀ σ with hWdef
  have hh₃0 : 0 < h₃ := by rw [hr3eq]; positivity
  have hh₃e : h₃ = σ * D.fc.q := by rw [hh₃]; exact hr3eq
  have hb₃h : h₃ ≤ b₃ := by
    rw [hh₃e, hb₃]; unfold CoreData.cellδ2
    have : 0 ≤ D.K * D.fc.q * D.N ^ (-D.κ * D.sc) := by positivity
    have h2 : σ * D.fc.q ≤ D.K * (σ * D.fc.q) := le_mul_of_one_le_left (by positivity) hK1
    have h3 : 0 ≤ D.K * (σ * D.fc.q) := by positivity
    linarith only [this, h2, h3]
  have hb₃0 : 0 < b₃ := lt_of_lt_of_le hh₃0 hb₃h
  -- the count bound of the third pruning
  have ha1d : 0 < D.a₁ ^ D.d := Real.rpow_pos_of_pos ha1 _
  have hacd : 0 < D.ac ^ D.d := Real.rpow_pos_of_pos hac _
  have hWd : W ^ D.d ≤ 22 * D.K ^ 5 * E * D.ac ^ D.d := by
    have hX1 : 1 ≤ 22 * D.K ^ 5 * E := by
      have : 1 ≤ D.K ^ 5 * E := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK1) hE1
      nlinarith only [this]
    calc W ^ D.d ≤ (22 * D.K ^ 5 * E * D.ac) ^ D.d := Real.rpow_le_rpow hW3lo.le hW3 hd0
      _ = (22 * D.K ^ 5 * E) ^ D.d * D.ac ^ D.d := Real.mul_rpow (by positivity) hac.le
      _ ≤ 22 * D.K ^ 5 * E * D.ac ^ D.d :=
          mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_one_le hX1 hd1.le) hacd.le
  have hcb : D.cb3 (D.r3 σ) b₃ W K₁ ≤ 132 * D.K ^ 6 * K₁ * E * (D.ac ^ D.d / D.a₁ ^ D.d) := by
    unfold CoreData.cb3
    rw [← hh₃]
    have e : (b₃ / h₃ + 2) * (2 * (D.K * (h₃ ^ 3 * W ^ D.d))) / (h₃ ^ 2 * b₃ * D.a₁ ^ D.d / K₁) =
        2 * D.K * K₁ * ((b₃ + 2 * h₃) / b₃) * (W ^ D.d / D.a₁ ^ D.d) := by
      field_simp
    rw [e]
    have h1 : (b₃ + 2 * h₃) / b₃ ≤ 3 := by rw [div_le_iff₀ hb₃0]; linarith only [hb₃h]
    have h2 : W ^ D.d / D.a₁ ^ D.d ≤ 22 * D.K ^ 5 * E * (D.ac ^ D.d / D.a₁ ^ D.d) := by
      rw [div_le_iff₀ ha1d]
      calc W ^ D.d ≤ 22 * D.K ^ 5 * E * D.ac ^ D.d := hWd
        _ = 22 * D.K ^ 5 * E * (D.ac ^ D.d / D.a₁ ^ D.d) * D.a₁ ^ D.d := by field_simp
    have hK₁0 : 0 < K₁ := by linarith only [hK₁1]
    calc 2 * D.K * K₁ * ((b₃ + 2 * h₃) / b₃) * (W ^ D.d / D.a₁ ^ D.d)
        ≤ 2 * D.K * K₁ * 3 * (22 * D.K ^ 5 * E * (D.ac ^ D.d / D.a₁ ^ D.d)) := by
          gcongr
      _ = 132 * D.K ^ 6 * K₁ * E * (D.ac ^ D.d / D.a₁ ^ D.d) := by ring
  have hcb0 : 0 ≤ D.cb3 (D.r3 σ) b₃ W K₁ := by
    unfold CoreData.cb3; rw [← hh₃]; positivity
  -- the bins bound
  have hbs0 : 0 ≤ D.binSpread D.M D.Dw K₁ (D.Bnat C₀) σ / D.N ^ (-s) := by
    have hB0 : 0 ≤ D.Bnat C₀ := by unfold CoreData.Bnat; positivity
    have hL := crossLip_nonneg' D H (K₁ := K₁) hB0
    have hδ := cellδ2_nonneg D H σ hσ0.le
    have hΛ0 : 0 ≤ D.Λa := by unfold CoreData.Λa; have := f₀_q_pos D; positivity
    unfold CoreData.binSpread
    have h1 : 0 ≤ D.crossLip D.M D.Dw K₁ (D.Bnat C₀) * D.cellδ2 σ := mul_nonneg hL hδ
    have h2 : 0 ≤ 9 * D.Bnat C₀ * (2 * (σ * D.fc.q)) * (1 + D.K + D.K ^ 2) := by positivity
    have h3 : 0 ≤ D.Λa * (σ * D.fc.q + σ * D.fc.q + D.cellδ2 σ) := by
      apply mul_nonneg hΛ0; have : 0 ≤ σ * D.fc.q := by positivity
      linarith only [this, hδ]
    have h4 : 0 ≤ 2 * (E * D.a₁) := by positivity
    apply div_nonneg (div_nonneg (by linarith only [h1, h2, h3, h4]) ha0.le) hat.le
  have hnmax : (D.nmax D.M D.Dw K₁ (D.Bnat C₀) (D.r3 σ) b₃ W σ (D.N ^ (-s)) : ℝ) ≤
      81 * (132 * D.K ^ 6 * K₁ * E * (D.ac ^ D.d / D.a₁ ^ D.d)) * (13 * E) := by
    unfold CoreData.nmax
    push_cast
    have f1 : (⌊D.cb3 (D.r3 σ) b₃ W K₁⌋₊ : ℝ) ≤ D.cb3 (D.r3 σ) b₃ W K₁ := Nat.floor_le hcb0
    have f2 : (⌊D.binSpread D.M D.Dw K₁ (D.Bnat C₀) σ / D.N ^ (-s)⌋₊ : ℝ) ≤ 2 * E + 3 :=
      (Nat.floor_le hbs0).trans hbs
    have f3 : 2 * ((⌊D.binSpread D.M D.Dw K₁ (D.Bnat C₀) σ / D.N ^ (-s)⌋₊ : ℝ) + 1) + 1 ≤ 13 * E := by
      linarith only [f2, hE1]
    have f30 : 0 ≤ 2 * ((⌊D.binSpread D.M D.Dw K₁ (D.Bnat C₀) σ / D.N ^ (-s)⌋₊ : ℝ) + 1) + 1 := by
      positivity
    have hpos : 0 ≤ 81 * (132 * D.K ^ 6 * K₁ * E * (D.ac ^ D.d / D.a₁ ^ D.d)) := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left (f1.trans hcb) (by norm_num)) f3 f30 hpos
  -- the box
  have hF : (⌊(2 * D.K + 1) / σ⌋₊ : ℝ) ≤ (2 * D.K + 1) / σ := Nat.floor_le (by positivity)
  have hbox : (2 * ((⌊(2 * D.K + 1) / σ⌋₊ : ℝ) + 1) + 1) * σ ≤ 9 * D.K := by
    have e : (2 * ((2 * D.K + 1) / σ + 1) + 1) * σ = 2 * (2 * D.K + 1) + 3 * σ := by
      field_simp; ring
    have h1 : (2 * ((⌊(2 * D.K + 1) / σ⌋₊ : ℝ) + 1) + 1) * σ ≤
        (2 * ((2 * D.K + 1) / σ + 1) + 1) * σ := by gcongr
    linarith only [h1, e, hσ1, hK1]
  have hbox0 : 0 ≤ (2 * ((⌊(2 * D.K + 1) / σ⌋₊ : ℝ) + 1) + 1) * σ := by positivity
  have hbox2 : ((2 * ((⌊(2 * D.K + 1) / σ⌋₊ : ℝ) + 1) + 1) * σ) ^ 2 ≤ (9 * D.K) ^ 2 :=
    pow_le_pow_left₀ hbox0 hbox 2
  -- the right side
  have hR : D.N ^ ηS * ((D.a₀ / D.ac) ^ D.d)⁻¹ * (D.N ^ (-s)) ^ (-D.d) =
      D.N ^ ηS * (D.ac ^ D.d / D.a₁ ^ D.d) := by
    have hat_eq : D.N ^ (-s) = D.a₁ / D.a₀ := by
      unfold CoreData.a₀ CoreData.a₁
      rw [hs, div_eq_mul_inv, ← Real.rpow_neg hN0.le, rpow_mul_rpow hN0]; congr 1; ring
    rw [hat_eq, Real.div_rpow ha0.le hac.le, Real.rpow_neg (by positivity),
      Real.div_rpow ha1.le ha0.le]
    have : D.a₀ ^ D.d ≠ 0 := (Real.rpow_pos_of_pos ha0 _).ne'
    field_simp
  rw [hR]
  -- powers of K, E, K₁
  have hK9 : D.K ^ 9 ≤ D.N ^ (9 * η) := by
    have := pow_le_rpow_mul hK1 hKη hN0 9; simpa using this
  have hE2 : E ^ 2 ≤ D.N ^ (2 * η) := by
    have hE : E ≤ D.N ^ η := rpow_le_rpow_exp hN1 hεLη
    calc E ^ 2 ≤ (D.N ^ η) ^ 2 := pow_le_pow_left₀ (by positivity) hE 2
      _ = D.N ^ (2 * η) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hK₁2 : K₁ ^ 2 = D.N ^ (2 * η₁) := by
    rw [hK₁def, ← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hb := le_rpow_of_big hN0 (C := 11258676) (x := 9 * η + 2 * η + 2 * η₁) (y := ηS) (by
    have e : 9 * η + 2 * η + 2 * η₁ - ηS = 11 * η + 2 * η₁ - ηS := by ring
    rw [e]; exact hbig)
  rw [← rpow_mul_rpow hN0, ← rpow_mul_rpow hN0] at hb
  have hQ : 0 ≤ D.ac ^ D.d / D.a₁ ^ D.d := by positivity
  have hnm0 : 0 ≤ (D.nmax D.M D.Dw K₁ (D.Bnat C₀) (D.r3 σ) b₃ W σ (D.N ^ (-s)) : ℝ) := by positivity
  calc (2 * ((⌊(2 * D.K + 1) / σ⌋₊ : ℝ) + 1) + 1) ^ 2 *
        (D.K * K₁ * (D.nmax D.M D.Dw K₁ (D.Bnat C₀) (D.r3 σ) b₃ W σ (D.N ^ (-s)) : ℝ)) * σ ^ 2
      = ((2 * ((⌊(2 * D.K + 1) / σ⌋₊ : ℝ) + 1) + 1) * σ) ^ 2 *
        (D.K * K₁ * (D.nmax D.M D.Dw K₁ (D.Bnat C₀) (D.r3 σ) b₃ W σ (D.N ^ (-s)) : ℝ)) := by ring
    _ ≤ (9 * D.K) ^ 2 * (D.K * K₁ * (81 * (132 * D.K ^ 6 * K₁ * E * (D.ac ^ D.d / D.a₁ ^ D.d)) *
          (13 * E))) := by
        apply mul_le_mul hbox2 (mul_le_mul_of_nonneg_left hnmax (by positivity))
          (by positivity) (by positivity)
    _ = 11258676 * (D.K ^ 9 * E ^ 2 * K₁ ^ 2) * (D.ac ^ D.d / D.a₁ ^ D.d) := by ring
    _ ≤ 11258676 * (D.N ^ (9 * η) * D.N ^ (2 * η) * D.N ^ (2 * η₁)) * (D.ac ^ D.d / D.a₁ ^ D.d) := by
        rw [hK₁2]; gcongr
    _ ≤ D.N ^ ηS * (D.ac ^ D.d / D.a₁ ^ D.d) := by
        apply mul_le_mul_of_nonneg_right _ hQ
        calc 11258676 * (D.N ^ (9 * η) * D.N ^ (2 * η) * D.N ^ (2 * η₁))
            = 11258676 * (D.N ^ (9 * η) * D.N ^ (2 * η) * D.N ^ (2 * η₁)) := rfl
          _ ≤ D.N ^ ηS := hb

/-- The candidate's coefficient bound. -/
theorem num_coef (D : CoreData α) (H : CoreHyp D) {η C₀ εS Rout : ℝ} (hKη : D.K ≤ D.N ^ η)
    (hη : 0 ≤ η) (hC₀ : 0 < C₀) (hεS : 0 ≤ εS) (hDa : D.Dw ≤ D.a₀)
    (hq0 : D.N ^ (-D.κ * D.s₀) ≤ D.K * D.f₀.q) (hκsc : 0 ≤ D.κ * D.sc)
    (hc1 : 21 * D.N ^ (η - Rout) ≤ 1)
    (hc2 : 72 * D.N ^ (5 * η + 2 * D.κ * D.s₀ - D.s₀ - Rout) ≤ 1)
    (hc3 : 675 * C₀ * D.N ^ (4 * η + 5 * εS + 2 * D.κ * D.sc - D.s₀ - Rout) ≤ 1) :
    1 + (6 * D.K + 3 * D.K * D.Λa + 3 * D.Λa) + D.a₀ *
      (9 * (C₀ * D.N ^ εS * (D.N ^ εS) ^ 2 * (D.N ^ εS) ^ 2) *
        (1 + D.K * D.N ^ (D.κ * D.sc) * (1 + 1 + 2 * D.K)) ^ 2) ≤ D.N ^ Rout := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hDw0 : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hΛ := Λa_le D H hDa hq0
  have hΛ0 : 0 ≤ D.Λa := by unfold CoreData.Λa; have := f₀_q_pos D; positivity
  have hDinv : D.a₀ / D.Dw = D.N ^ (2 * D.κ * D.s₀ - D.s₀) := by
    unfold CoreData.a₀ CoreData.Dw
    rw [div_eq_mul_inv, ← Real.rpow_neg hN0.le, rpow_mul_rpow hN0]; congr 1; ring
  have hK4 : D.K ^ 4 ≤ D.N ^ (4 * η) := by
    have := pow_le_rpow_mul hK1 hKη hN0 4; simpa using this
  have hK5 : D.K ^ 5 ≤ D.N ^ (5 * η) := by
    have := pow_le_rpow_mul hK1 hKη hN0 5; simpa using this
  have hNk : 1 ≤ D.N ^ (D.κ * D.sc) := Real.one_le_rpow hN1 hκsc
  -- the three pieces
  have P1 : 1 + 6 * D.K ≤ 7 * D.N ^ η := by
    have : 1 ≤ D.K := hK1; linarith only [this, hKη]
  have P2 : 3 * D.K * D.Λa + 3 * D.Λa ≤ 24 * D.N ^ (5 * η + 2 * D.κ * D.s₀ - D.s₀) := by
    have h1 : 3 * D.K * D.Λa + 3 * D.Λa ≤ 6 * D.K * D.Λa := by nlinarith only [hK1, hΛ0]
    have h2 : 6 * D.K * D.Λa ≤ 6 * D.K * (4 * D.K ^ 4 * D.N ^ (2 * D.κ * D.s₀ - D.s₀)) := by
      rw [← hDinv]; exact mul_le_mul_of_nonneg_left hΛ (by positivity)
    have h3 : 6 * D.K * (4 * D.K ^ 4 * D.N ^ (2 * D.κ * D.s₀ - D.s₀)) =
        24 * D.K ^ 5 * D.N ^ (2 * D.κ * D.s₀ - D.s₀) := by ring
    have h5 : D.N ^ (5 * η) * D.N ^ (2 * D.κ * D.s₀ - D.s₀) =
        D.N ^ (5 * η + 2 * D.κ * D.s₀ - D.s₀) := by rw [rpow_mul_rpow hN0]; congr 1; ring
    have h4 : 24 * D.K ^ 5 * D.N ^ (2 * D.κ * D.s₀ - D.s₀) ≤
        24 * D.N ^ (5 * η + 2 * D.κ * D.s₀ - D.s₀) := by
      calc 24 * D.K ^ 5 * D.N ^ (2 * D.κ * D.s₀ - D.s₀)
          ≤ 24 * D.N ^ (5 * η) * D.N ^ (2 * D.κ * D.s₀ - D.s₀) := by gcongr
        _ = 24 * (D.N ^ (5 * η) * D.N ^ (2 * D.κ * D.s₀ - D.s₀)) := by ring
        _ = 24 * D.N ^ (5 * η + 2 * D.κ * D.s₀ - D.s₀) := by rw [h5]
    linarith only [h1, h2, h3, h4]
  have P3 : D.a₀ * (9 * (C₀ * D.N ^ εS * (D.N ^ εS) ^ 2 * (D.N ^ εS) ^ 2) *
      (1 + D.K * D.N ^ (D.κ * D.sc) * (1 + 1 + 2 * D.K)) ^ 2) ≤
      225 * C₀ * D.N ^ (4 * η + 5 * εS + 2 * D.κ * D.sc - D.s₀) := by
    have h1 : 1 + D.K * D.N ^ (D.κ * D.sc) * (1 + 1 + 2 * D.K) ≤ 5 * D.K ^ 2 * D.N ^ (D.κ * D.sc) := by
      have : 1 ≤ D.K ^ 2 * D.N ^ (D.κ * D.sc) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK1) hNk
      nlinarith only [this, hK1, hNk]
    have h2 : (1 + D.K * D.N ^ (D.κ * D.sc) * (1 + 1 + 2 * D.K)) ^ 2 ≤
        25 * D.K ^ 4 * D.N ^ (2 * (D.κ * D.sc)) := by
      have h0 : 0 ≤ 1 + D.K * D.N ^ (D.κ * D.sc) * (1 + 1 + 2 * D.K) := by positivity
      have := pow_le_pow_left₀ h0 h1 2
      have e : (5 * D.K ^ 2 * D.N ^ (D.κ * D.sc)) ^ 2 = 25 * D.K ^ 4 * D.N ^ (2 * (D.κ * D.sc)) := by
        rw [show (2 : ℝ) * (D.κ * D.sc) = (D.κ * D.sc) * ((2 : ℕ) : ℝ) by push_cast; ring,
          Real.rpow_mul_natCast hN0.le]; ring
      linarith only [this, e]
    have h3 : C₀ * D.N ^ εS * (D.N ^ εS) ^ 2 * (D.N ^ εS) ^ 2 = C₀ * D.N ^ (5 * εS) := by
      rw [show (5 : ℝ) * εS = εS * ((5 : ℕ) : ℝ) by push_cast; ring, Real.rpow_mul_natCast hN0.le]
      ring
    rw [h3]
    calc D.a₀ * (9 * (C₀ * D.N ^ (5 * εS)) * (1 + D.K * D.N ^ (D.κ * D.sc) * (1 + 1 + 2 * D.K)) ^ 2)
        ≤ D.a₀ * (9 * (C₀ * D.N ^ (5 * εS)) * (25 * D.K ^ 4 * D.N ^ (2 * (D.κ * D.sc)))) := by
          gcongr
      _ ≤ D.a₀ * (9 * (C₀ * D.N ^ (5 * εS)) * (25 * D.N ^ (4 * η) * D.N ^ (2 * (D.κ * D.sc)))) := by
          gcongr
      _ = 225 * C₀ * (D.N ^ (-D.s₀) * D.N ^ (5 * εS) * D.N ^ (4 * η) * D.N ^ (2 * (D.κ * D.sc))) := by
          unfold CoreData.a₀; ring
      _ = 225 * C₀ * D.N ^ (4 * η + 5 * εS + 2 * D.κ * D.sc - D.s₀) := by
          rw [rpow_mul_rpow hN0, rpow_mul_rpow hN0, rpow_mul_rpow hN0]; congr 2; ring
  -- each piece is a third of the target
  have Q1 := le_rpow_of_big hN0 (C := 21) (x := η) (y := Rout) hc1
  have Q2 := le_rpow_of_big hN0 (C := 72) (x := 5 * η + 2 * D.κ * D.s₀ - D.s₀) (y := Rout) hc2
  have Q3 := le_rpow_of_big hN0 (C := 675 * C₀) (x := 4 * η + 5 * εS + 2 * D.κ * D.sc - D.s₀)
    (y := Rout) hc3
  have e3 : 675 * C₀ * D.N ^ (4 * η + 5 * εS + 2 * D.κ * D.sc - D.s₀) =
      3 * (225 * C₀ * D.N ^ (4 * η + 5 * εS + 2 * D.κ * D.sc - D.s₀)) := by ring
  rw [e3] at Q3
  linarith only [P1, P2, P3, Q1, Q2, Q3]

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
