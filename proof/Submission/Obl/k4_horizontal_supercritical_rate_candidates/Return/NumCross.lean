import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.CandOut

/-!
# Numerics of the crossing constant

At the chosen scales (crossing cells `χ × χ × D`, natural slice coefficients
`B = C₀ N^(3εL)/D²`), the crossing constant is at most `(10⁹ K¹² K₁³ E³)^(1/(1-d))`, where
`E = N^εL`, and the Lipschitz constant of a kept slice law is at most
`14 (10⁹ K¹² K₁³ E³)^(1/(1-d)) a₀/D + a₁`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

theorem crossB_le {d e Cs θ X : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) (he : 0 ≤ e) (hCs : 0 ≤ Cs)
    (hθ : 0 < θ) (hX : 1 ≤ X) (hle : 2 * e + 40 * e * Cs / θ ^ 2 ≤ X) :
    crossB d e Cs θ ≤ X ^ (1 / (1 - d)) := by
  have hp : 0 < 1 / (1 - d) := by apply div_pos one_pos; linarith
  unfold crossB
  refine max_le (Real.one_le_rpow hX hp.le) ?_
  exact Real.rpow_le_rpow (by positivity) hle hp.le

/-- The pure-number core: `2e + 40 e Cs/θ² ≤ 10⁹ K¹² K₁³ E³`. -/
theorem cross_sum_le {K K₁ E e Cs θ : ℝ} (hK : 1 ≤ K) (hK₁ : 1 ≤ K₁) (hE : 1 ≤ E)
    (he0 : 0 ≤ e) (he : e ≤ 16 * K ^ 4 * E) (hCs0 : 0 ≤ Cs) (hCs : Cs ≤ 1620 * K ^ 6 * K₁)
    (hθ0 : 0 < θ) (hθ : 1 / (30 * K * K₁ * E) ≤ θ) :
    2 * e + 40 * e * Cs / θ ^ 2 ≤ 10 ^ 9 * K ^ 12 * K₁ ^ 3 * E ^ 3 := by
  have hK0 : 0 < K := by linarith
  have hK₁0 : 0 < K₁ := by linarith
  have hE0 : 0 < E := by linarith
  have hinv : 1 / θ ^ 2 ≤ (30 * K * K₁ * E) ^ 2 := by
    have h1 : 1 ≤ 30 * K * K₁ * E * θ := by
      rw [div_le_iff₀ (by positivity)] at hθ; linarith
    rw [div_le_iff₀ (by positivity)]
    calc (1 : ℝ) ≤ (30 * K * K₁ * E * θ) ^ 2 := one_le_pow₀ h1
      _ = (30 * K * K₁ * E) ^ 2 * θ ^ 2 := by ring
  have b1 : 40 * e * Cs ≤ 40 * (16 * K ^ 4 * E) * (1620 * K ^ 6 * K₁) :=
    mul_le_mul (mul_le_mul_of_nonneg_left he (by norm_num)) hCs hCs0 (by positivity)
  have b2 := mul_le_mul b1 hinv (by positivity) (by positivity)
  have h1 : K ^ 4 * E ≤ K ^ 12 * K₁ ^ 3 * E ^ 3 := by
    have a1 : K ^ 4 ≤ K ^ 12 := pow_le_pow_right₀ hK (by norm_num)
    have a2 : E ≤ E ^ 3 := le_self_pow₀ hE (by norm_num)
    have a3 : 1 ≤ K₁ ^ 3 := one_le_pow₀ hK₁
    calc K ^ 4 * E ≤ K ^ 12 * E ^ 3 := mul_le_mul a1 a2 (by positivity) (by positivity)
      _ ≤ K ^ 12 * K₁ ^ 3 * E ^ 3 := by
          rw [mul_right_comm]; exact le_mul_of_one_le_right (by positivity) a3
  have e2 : 40 * (16 * K ^ 4 * E) * (1620 * K ^ 6 * K₁) * (30 * K * K₁ * E) ^ 2 =
      933120000 * (K ^ 12 * K₁ ^ 3 * E ^ 3) := by ring
  have e3 : 10 ^ 9 * K ^ 12 * K₁ ^ 3 * E ^ 3 = 10 ^ 9 * (K ^ 12 * K₁ ^ 3 * E ^ 3) := by ring
  have e4 : 40 * e * Cs / θ ^ 2 = 40 * e * Cs * (1 / θ ^ 2) := by ring
  rw [e3, e4]
  rw [e2] at b2
  nlinarith

theorem one_le_cross_X {K K₁ E : ℝ} (hK : 1 ≤ K) (hK₁ : 1 ≤ K₁) (hE : 1 ≤ E) :
    1 ≤ 10 ^ 9 * K ^ 12 * K₁ ^ 3 * E ^ 3 := by
  have hP1 : 1 ≤ K ^ 12 * K₁ ^ 3 * E ^ 3 :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK)
      (one_le_pow₀ hK₁)) (one_le_pow₀ hE)
  have e : 10 ^ 9 * K ^ 12 * K₁ ^ 3 * E ^ 3 = 10 ^ 9 * (K ^ 12 * K₁ ^ 3 * E ^ 3) := by ring
  rw [e]
  exact hP1.trans (le_mul_of_one_le_left (le_trans zero_le_one hP1) (by norm_num))

/-- The hidden error and window of the crossing. -/
theorem cross_W (D : CoreData α) (H : CoreHyp D) {C₀ : ℝ} (hC₀ : 0 < C₀) (hεL : 0 ≤ D.εL)
    (hF1 : 18 * D.Bnat C₀ * D.N ^ (-D.M) * (1 + D.K + D.K ^ 2) ≤ D.a₁)
    (hF2 : 2 * D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M) ≤ D.a₁) :
    D.crossEb D.M (D.Bnat C₀) ≤ 2 * D.N ^ D.εL * D.a₁ ∧
    2 * D.N ^ D.εL * D.a₁ ≤ D.crossW D.M D.Dw (D.Bnat C₀) ∧
    D.crossW D.M D.Dw (D.Bnat C₀) ≤ 5 * D.N ^ D.εL * D.a₁ := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hE1 : 1 ≤ D.N ^ D.εL := Real.one_le_rpow (by linarith [H.N2]) hεL
  have ha1 : 0 < D.a₁ := Real.rpow_pos_of_pos hN0 _
  have hEb : D.crossEb D.M (D.Bnat C₀) ≤ 2 * D.N ^ D.εL * D.a₁ := by
    unfold CoreData.crossEb
    have h1 : 9 * D.Bnat C₀ * (2 * D.N ^ (-D.M)) * (1 + D.K + D.K ^ 2) ≤ D.a₁ := by
      linarith only [hF1]
    have h2 : D.a₁ ≤ D.N ^ D.εL * D.a₁ := le_mul_of_one_le_left ha1.le hE1
    linarith only [h1, h2]
  have hK0 : 0 < D.K := by linarith [H.K1]
  have hDw0 : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hG0 : 0 ≤ D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M) := by
    unfold CoreData.crossG CoreData.Bnat
    positivity
  have hEb0 : D.N ^ D.εL * D.a₁ ≤ D.crossEb D.M (D.Bnat C₀) := by
    unfold CoreData.crossEb CoreData.Bnat
    have : 0 ≤ 9 * (C₀ * D.N ^ D.εL * (D.N ^ D.εL) ^ 2 / D.Dw ^ 2) * (2 * D.N ^ (-D.M)) *
        (1 + D.K + D.K ^ 2) := by positivity
    linarith only [this]
  refine ⟨hEb, ?_, ?_⟩
  · unfold CoreData.crossW
    linarith only [hEb0, hG0]
  · unfold CoreData.crossW
    have h2 : D.a₁ ≤ D.N ^ D.εL * D.a₁ := le_mul_of_one_le_left ha1.le hE1
    linarith only [hEb, hF2, h2]

/-- The normalized crossing error. -/
theorem cross_e (D : CoreData α) (H : CoreHyp D) {C₀ : ℝ} (hC₀ : 0 < C₀) (hεL : 0 ≤ D.εL)
    (hχD : D.N ^ (-D.M) ≤ D.Dw) (hDa : D.Dw ≤ D.a₀) (ha10 : D.a₁ ≤ D.a₀)
    (hq0 : D.N ^ (-D.κ * D.s₀) ≤ D.K * D.f₀.q) (hDw : D.Dw = (D.N ^ (-D.κ * D.s₀)) ^ 2)
    (hF1 : 18 * D.Bnat C₀ * D.N ^ (-D.M) * (1 + D.K + D.K ^ 2) ≤ D.a₁)
    (hF2 : 2 * D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M) ≤ D.a₁) :
    D.crossEa D.M D.Dw / D.a₀ ≤ 13 * D.K ^ 4 ∧
    0 ≤ (D.crossEa D.M D.Dw + D.crossEb D.M (D.Bnat C₀) +
      D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M)) / D.a₀ ∧
    (D.crossEa D.M D.Dw + D.crossEb D.M (D.Bnat C₀) +
      D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M)) / D.a₀ ≤ 16 * D.K ^ 4 * D.N ^ D.εL := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  have hE1 : 1 ≤ D.N ^ D.εL := Real.one_le_rpow (by linarith [H.N2]) hεL
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have ha1 : 0 < D.a₁ := Real.rpow_pos_of_pos hN0 _
  have hDw0 : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hχ0 : 0 < D.N ^ (-D.M) := Real.rpow_pos_of_pos hN0 _
  have hq00 : 0 < D.f₀.q := f₀_q_pos D
  obtain ⟨hEb, -, -⟩ := cross_W D H hC₀ hεL hF1 hF2
  have hq02 : D.a₀ / D.f₀.q ^ 2 ≤ D.K ^ 2 * D.a₀ / D.Dw := by
    rw [div_le_div_iff₀ (by positivity) hDw0, hDw]
    have : (D.N ^ (-D.κ * D.s₀)) ^ 2 ≤ (D.K * D.f₀.q) ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hq0 2
    have ha := ha0.le
    calc D.a₀ * (D.N ^ (-D.κ * D.s₀)) ^ 2 ≤ D.a₀ * (D.K * D.f₀.q) ^ 2 :=
          mul_le_mul_of_nonneg_left this ha
      _ = D.K ^ 2 * D.a₀ * D.f₀.q ^ 2 := by ring
  have hEa : D.crossEa D.M D.Dw / D.a₀ ≤ 13 * D.K ^ 4 := by
    unfold CoreData.crossEa
    rw [div_le_iff₀ ha0]
    have h1 : 2 * D.N ^ (-D.M) + D.Dw ≤ 3 * D.Dw := by linarith only [hχD]
    have h2 : 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) * (2 * D.N ^ (-D.M) + D.Dw) ≤
        2 * D.K ^ 2 * (1 + D.K ^ 2 * D.a₀ / D.Dw) * (3 * D.Dw) := by
      have hA : 0 ≤ 2 * D.K ^ 2 := by positivity
      have hB : 0 ≤ 1 + D.a₀ / D.f₀.q ^ 2 := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left (by linarith only [hq02]) hA) h1
        (by positivity) (by positivity)
    have h3 : 2 * D.K ^ 2 * (1 + D.K ^ 2 * D.a₀ / D.Dw) * (3 * D.Dw) =
        6 * D.K ^ 2 * D.Dw + 6 * D.K ^ 4 * D.a₀ := by field_simp; ring
    have h4 : D.K ≤ D.K ^ 4 := le_self_pow₀ hK1 (by norm_num)
    have h5 : D.K ^ 2 ≤ D.K ^ 4 := pow_le_pow_right₀ hK1 (by norm_num)
    have h6 : D.K * D.a₀ ≤ D.K ^ 4 * D.a₀ := mul_le_mul_of_nonneg_right h4 ha0.le
    have h7 : D.K ^ 2 * D.Dw ≤ D.K ^ 4 * D.a₀ := mul_le_mul h5 hDa hDw0.le (by positivity)
    linarith only [h2, h3, h6, h7]
  have hGχ0 : 0 ≤ D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M) := by
    unfold CoreData.crossG CoreData.Bnat; positivity
  have hGχ : D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M) ≤ D.a₁ := by
    linarith only [hF2, hGχ0]
  have hEa0 : 0 ≤ D.crossEa D.M D.Dw := by unfold CoreData.crossEa; positivity
  have hEb0 : 0 ≤ D.crossEb D.M (D.Bnat C₀) := by
    unfold CoreData.crossEb CoreData.Bnat; positivity
  refine ⟨hEa, by positivity, ?_⟩
  rw [add_div, add_div]
  have h1 : D.crossEb D.M (D.Bnat C₀) / D.a₀ ≤ 2 * D.N ^ D.εL := by
    rw [div_le_iff₀ ha0]
    have : 2 * D.N ^ D.εL * D.a₁ ≤ 2 * D.N ^ D.εL * D.a₀ :=
      mul_le_mul_of_nonneg_left ha10 (by positivity)
    linarith only [hEb, this]
  have h2 : D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M) / D.a₀ ≤ 1 := by
    rw [div_le_iff₀ ha0]; linarith only [hGχ, ha10]
  have h4 : D.K ^ 4 ≤ D.K ^ 4 * D.N ^ D.εL := le_mul_of_one_le_right (by positivity) hE1
  have h5 : 1 ≤ D.K ^ 4 * D.N ^ D.εL := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK1) hE1
  have h6 : D.N ^ D.εL ≤ D.K ^ 4 * D.N ^ D.εL :=
    le_mul_of_one_le_left (by positivity) (one_le_pow₀ hK1)
  linarith only [hEa, h1, h2, h4, h5, h6]

/-- The crossing's count constant. -/
theorem cross_Cs (D : CoreData α) (H : CoreHyp D) {K₁ : ℝ} (hK₁ : 1 ≤ K₁) (hd1 : D.d < 1)
    (hχD : D.N ^ (-D.M) ≤ D.Dw) (hEa : D.crossEa D.M D.Dw / D.a₀ ≤ 13 * D.K ^ 4) :
    0 ≤ D.crossCs D.M D.Dw K₁ ∧ D.crossCs D.M D.Dw K₁ ≤ 1620 * D.K ^ 6 * K₁ := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  have hK₁0 : 0 < K₁ := by linarith
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hDw0 : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hχ0 : 0 < D.N ^ (-D.M) := Real.rpow_pos_of_pos hN0 _
  have hEa0 : 0 ≤ D.crossEa D.M D.Dw := by unfold CoreData.crossEa; have := f₀_q_pos D; positivity
  set P := (1 + 2 * D.crossEa D.M D.Dw / D.a₀) ^ D.d with hP
  have hb1 : 1 ≤ 1 + 2 * D.crossEa D.M D.Dw / D.a₀ := by
    have : 0 ≤ 2 * D.crossEa D.M D.Dw / D.a₀ := by positivity
    linarith only [this]
  have hb2 : 1 + 2 * D.crossEa D.M D.Dw / D.a₀ ≤ 27 * D.K ^ 4 := by
    have e2 : 2 * D.crossEa D.M D.Dw / D.a₀ = 2 * (D.crossEa D.M D.Dw / D.a₀) := by ring
    have : (1 : ℝ) ≤ D.K ^ 4 := one_le_pow₀ hK1
    rw [e2]; linarith only [hEa, this]
  have hP27 : P ≤ 27 * D.K ^ 4 := (Real.rpow_le_self_of_one_le hb1 hd1.le).trans hb2
  have hP0 : 0 ≤ P := Real.rpow_nonneg (by linarith only [hb1]) _
  have hCs_eq : D.crossCs D.M D.Dw K₁ = (8 * D.K + 2) * (1 + 2 * D.N ^ (-D.M) / D.Dw) * 2 * D.K *
      P * K₁ := by
    unfold CoreData.crossCs
    rw [← hP]
    have ha0d : 0 < D.a₀ ^ D.d := Real.rpow_pos_of_pos ha0 _
    field_simp
  have hX0 : 0 ≤ 1 + 2 * D.N ^ (-D.M) / D.Dw := by positivity
  rw [hCs_eq]
  refine ⟨by positivity, ?_⟩
  have h1 : 1 + 2 * D.N ^ (-D.M) / D.Dw ≤ 3 := by
    have : 2 * D.N ^ (-D.M) / D.Dw ≤ 2 := by rw [div_le_iff₀ hDw0]; linarith only [hχD]
    linarith only [this]
  have h2 : 8 * D.K + 2 ≤ 10 * D.K := by linarith only [hK1]
  have a1 : (8 * D.K + 2) * (1 + 2 * D.N ^ (-D.M) / D.Dw) ≤ (10 * D.K) * 3 :=
    mul_le_mul h2 h1 hX0 (by positivity)
  have a2 : (8 * D.K + 2) * (1 + 2 * D.N ^ (-D.M) / D.Dw) * 2 * D.K ≤ (10 * D.K) * 3 * 2 * D.K :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right a1 (by norm_num)) hK0.le
  have a3 : (8 * D.K + 2) * (1 + 2 * D.N ^ (-D.M) / D.Dw) * 2 * D.K * P ≤
      (10 * D.K) * 3 * 2 * D.K * (27 * D.K ^ 4) := mul_le_mul a2 hP27 hP0 (by positivity)
  calc (8 * D.K + 2) * (1 + 2 * D.N ^ (-D.M) / D.Dw) * 2 * D.K * P * K₁
      ≤ (10 * D.K) * 3 * 2 * D.K * (27 * D.K ^ 4) * K₁ := mul_le_mul_of_nonneg_right a3 hK₁0.le
    _ = 1620 * D.K ^ 6 * K₁ := by ring

/-- The crossing's density ratio. -/
theorem cross_θ (D : CoreData α) (H : CoreHyp D) {K₁ C₀ : ℝ} (hK₁ : 1 ≤ K₁) (hεL : 0 ≤ D.εL)
    (hd0 : 0 ≤ D.d) (hd1 : D.d < 1) (hχD : D.N ^ (-D.M) ≤ D.Dw)
    (hWlo : 2 * D.N ^ D.εL * D.a₁ ≤ D.crossW D.M D.Dw (D.Bnat C₀))
    (hW : D.crossW D.M D.Dw (D.Bnat C₀) ≤ 5 * D.N ^ D.εL * D.a₁) :
    1 / (30 * D.K * K₁ * D.N ^ D.εL) ≤ D.crossTheta D.M D.Dw K₁ (D.Bnat C₀) := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  have hK₁0 : 0 < K₁ := by linarith
  have hE1 : 1 ≤ D.N ^ D.εL := Real.one_le_rpow (by linarith [H.N2]) hεL
  have hE0 : 0 < D.N ^ D.εL := by linarith only [hE1]
  have ha1 : 0 < D.a₁ := Real.rpow_pos_of_pos hN0 _
  have hDw0 : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hχ0 : 0 < D.N ^ (-D.M) := Real.rpow_pos_of_pos hN0 _
  set W := D.crossW D.M D.Dw (D.Bnat C₀) with hWdef
  have hW0 : 0 < W := lt_of_lt_of_le (by positivity) hWlo
  have hWd : W ^ D.d ≤ 5 * D.N ^ D.εL * D.a₁ ^ D.d := by
    calc W ^ D.d ≤ (5 * D.N ^ D.εL * D.a₁) ^ D.d := Real.rpow_le_rpow hW0.le hW hd0
      _ = (5 * D.N ^ D.εL) ^ D.d * D.a₁ ^ D.d :=
          Real.mul_rpow (x := 5 * D.N ^ D.εL) (y := D.a₁) (by positivity) ha1.le
      _ ≤ 5 * D.N ^ D.εL * D.a₁ ^ D.d := by
          have h5E : (5 * D.N ^ D.εL) ^ D.d ≤ 5 * D.N ^ D.εL :=
            Real.rpow_le_self_of_one_le (by linarith only [hE1]) hd1.le
          exact mul_le_mul_of_nonneg_right h5E (Real.rpow_nonneg ha1.le _)
  have ha1d : 0 < D.a₁ ^ D.d := Real.rpow_pos_of_pos ha1 _
  unfold CoreData.crossTheta
  rw [← hWdef]
  have hWd0 : 0 < W ^ D.d := Real.rpow_pos_of_pos hW0 _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : D.Dw + 2 * D.N ^ (-D.M) ≤ 3 * D.Dw := by linarith only [hχD]
  have hA : 0 ≤ 2 * D.K * K₁ := by positivity
  calc 1 * (2 * D.K * K₁ * W ^ D.d * (D.Dw + 2 * D.N ^ (-D.M)))
      ≤ 1 * (2 * D.K * K₁ * (5 * D.N ^ D.εL * D.a₁ ^ D.d) * (3 * D.Dw)) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_left hWd hA) h3
          (by positivity) (by positivity)) zero_le_one
    _ = D.Dw * D.a₁ ^ D.d * (30 * D.K * K₁ * D.N ^ D.εL) := by ring

/-- The Lipschitz constant of a kept slice law at the chosen scales. -/
theorem crossLip_le (D : CoreData α) (H : CoreHyp D) {K₁ C₀ : ℝ} (hK₁ : 1 ≤ K₁) (hC₀ : 0 < C₀)
    (hεL : 0 ≤ D.εL) (hd0 : 0 ≤ D.d) (hd1 : D.d < 1)
    (hχD : D.N ^ (-D.M) ≤ D.Dw) (hDa : D.Dw ≤ D.a₀) (ha10 : D.a₁ ≤ D.a₀)
    (hq0 : D.N ^ (-D.κ * D.s₀) ≤ D.K * D.f₀.q) (hDw : D.Dw = (D.N ^ (-D.κ * D.s₀)) ^ 2)
    (hF1 : 18 * D.Bnat C₀ * D.N ^ (-D.M) * (1 + D.K + D.K ^ 2) ≤ D.a₁)
    (hF2 : 2 * D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M) ≤ D.a₁) :
    D.crossLip D.M D.Dw K₁ (D.Bnat C₀) ≤
      14 * (10 ^ 9 * D.K ^ 12 * K₁ ^ 3 * (D.N ^ D.εL) ^ 3) ^ (1 / (1 - D.d)) * (D.a₀ / D.Dw) +
        D.a₁ := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hK1 := H.K1
  have hE1 : 1 ≤ D.N ^ D.εL := Real.one_le_rpow (by linarith [H.N2]) hεL
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hDw0 : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hχ0 : 0 < D.N ^ (-D.M) := Real.rpow_pos_of_pos hN0 _
  obtain ⟨-, hWlo, hW⟩ := cross_W D H hC₀ hεL hF1 hF2
  obtain ⟨hEa, he0, he⟩ := cross_e D H hC₀ hεL hχD hDa ha10 hq0 hDw hF1 hF2
  obtain ⟨hCs0, hCs⟩ := cross_Cs D H hK₁ hd1 hχD hEa
  have hθ := cross_θ D H (C₀ := C₀) hK₁ hεL hd0 hd1 hχD hWlo hW
  have hθ0 : 0 < D.crossTheta D.M D.Dw K₁ (D.Bnat C₀) := lt_of_lt_of_le (by
    have : 0 < K₁ := by linarith
    have : 0 < D.K := by linarith
    positivity) hθ
  have hsum := cross_sum_le hK1 hK₁ hE1 he0 he hCs0 hCs hθ0 hθ
  have hcB := crossB_le hd0 hd1 he0 hCs0 hθ0 (one_le_cross_X hK1 hK₁ hE1) hsum
  unfold CoreData.crossLip
  have hden : D.a₀ / (D.Dw + 2 * D.N ^ (-D.M)) ≤ D.a₀ / D.Dw :=
    div_le_div_of_nonneg_left ha0.le hDw0 (by linarith only [hχ0])
  have hB0 : 0 ≤ D.Bnat C₀ := by unfold CoreData.Bnat; positivity
  have hB2 : 9 * D.Bnat C₀ * (2 * D.N ^ (-D.M)) ≤ D.a₁ := by
    have : 0 ≤ D.Bnat C₀ * D.N ^ (-D.M) * (D.K + D.K ^ 2) := by
      have : 0 ≤ D.K := by linarith
      positivity
    linarith only [hF1, this]
  have hX : 0 ≤ (10 ^ 9 * D.K ^ 12 * K₁ ^ 3 * (D.N ^ D.εL) ^ 3) ^ (1 / (1 - D.d)) :=
    Real.rpow_nonneg (by linarith only [one_le_cross_X hK1 hK₁ hE1]) _
  have c1 := mul_le_mul hcB hden (by positivity) hX
  have e1 : 14 * crossB D.d ((D.crossEa D.M D.Dw + D.crossEb D.M (D.Bnat C₀) +
      D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M)) / D.a₀) (D.crossCs D.M D.Dw K₁)
        (D.crossTheta D.M D.Dw K₁ (D.Bnat C₀)) * D.a₀ / (D.Dw + 2 * D.N ^ (-D.M)) =
      14 * (crossB D.d ((D.crossEa D.M D.Dw + D.crossEb D.M (D.Bnat C₀) +
      D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M)) / D.a₀) (D.crossCs D.M D.Dw K₁)
        (D.crossTheta D.M D.Dw K₁ (D.Bnat C₀)) * (D.a₀ / (D.Dw + 2 * D.N ^ (-D.M)))) := by ring
  rw [e1]
  linarith only [c1, hB2]

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
