import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.NumCross
import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.NumBasic

/-!
# Sample numerics

Each numerical hypothesis of `core_sample` follows, at one sample, from the sample bounds
`K ≤ N^η`, `εL ≤ η`, the label scales `q ≈ N^(-κ s)` and one pure inequality in `N`.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Label scales from the block counts. -/
theorem fam_q_bounds {ν : Measure α} {μ : Measure (α × ℝ)} {π : Measure ℝ}
    {b : α → Fin 6 → ℝ} {N K d κ s χ : ℝ} {f : Fam α} (hf : f.Good ν μ π b N K d κ s χ)
    (hN : 0 < N) (hK : 0 < K) : f.q ≤ K * N ^ (-κ * s) ∧ N ^ (-κ * s) ≤ K * f.q := by
  have hT : (0 : ℝ) < 2 ^ f.T := by positivity
  have hNs : 0 < N ^ (κ * s) := Real.rpow_pos_of_pos hN _
  have hneg : N ^ (-κ * s) = (N ^ (κ * s))⁻¹ := by
    rw [neg_mul, Real.rpow_neg hN.le]
  unfold Fam.q
  rw [hneg]
  constructor
  · have h := hf.Tlo
    rw [div_le_iff₀ hK] at h
    rw [← div_eq_mul_inv, le_div_iff₀ hNs, inv_mul_eq_div, div_le_iff₀ hT]
    linarith
  · have h := hf.Thi
    have h2 : 2 ^ f.T / N ^ (κ * s) ≤ K := by rw [div_le_iff₀ hNs]; exact h
    calc (N ^ (κ * s))⁻¹ = ((2 : ℝ) ^ f.T)⁻¹ * (2 ^ f.T / N ^ (κ * s)) := by field_simp
      _ ≤ ((2 : ℝ) ^ f.T)⁻¹ * K := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = K * ((2 : ℝ) ^ f.T)⁻¹ := mul_comm _ _

theorem Dw_eq_sq (D : CoreData α) (H : CoreHyp D) : D.Dw = (D.N ^ (-D.κ * D.s₀)) ^ 2 := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  unfold CoreData.Dw
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
  congr 1; push_cast; ring

/-- The natural slice coefficient bound. -/
theorem Bnat_le (D : CoreData α) (H : CoreHyp D) {C₀ η : ℝ} (hC₀ : 0 < C₀) (hεL0 : 0 ≤ D.εL)
    (hεLη : D.εL ≤ η) : D.Bnat C₀ ≤ C₀ * D.N ^ (3 * η + 4 * D.κ * D.s₀) := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hE : D.N ^ D.εL ≤ D.N ^ η := rpow_le_rpow_exp hN1 hεLη
  have hE0 : 0 ≤ D.N ^ D.εL := Real.rpow_nonneg hN0.le _
  have hDw2 : 1 / D.Dw ^ 2 = D.N ^ (4 * D.κ * D.s₀) := by
    unfold CoreData.Dw
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, one_div, ← Real.rpow_neg hN0.le]
    congr 1; push_cast; ring
  unfold CoreData.Bnat
  have e1 : C₀ * D.N ^ D.εL * (D.N ^ D.εL) ^ 2 / D.Dw ^ 2 =
      C₀ * (D.N ^ D.εL) ^ 3 * (1 / D.Dw ^ 2) := by ring
  rw [e1, hDw2]
  have h3 : (D.N ^ D.εL) ^ 3 ≤ D.N ^ (3 * η) := by
    rw [show 3 * η = ((3 : ℕ) : ℝ) * η by norm_num, mul_comm, Real.rpow_mul_natCast hN0.le]
    exact pow_le_pow_left₀ hE0 hE 3
  calc C₀ * (D.N ^ D.εL) ^ 3 * D.N ^ (4 * D.κ * D.s₀)
      ≤ C₀ * D.N ^ (3 * η) * D.N ^ (4 * D.κ * D.s₀) := by gcongr
    _ = C₀ * D.N ^ (3 * η + 4 * D.κ * D.s₀) := by rw [mul_assoc, rpow_mul_rpow hN0]

/-- The first crossing smallness condition. -/
theorem num_F1 (D : CoreData α) (H : CoreHyp D) {C₀ η : ℝ} (hC₀ : 0 < C₀) (hεL0 : 0 ≤ D.εL)
    (hεLη : D.εL ≤ η) (hKη : D.K ≤ D.N ^ η)
    (hbig : 54 * C₀ * D.N ^ (5 * η + 4 * D.κ * D.s₀ - D.M + D.s₁) ≤ 1) :
    18 * D.Bnat C₀ * D.N ^ (-D.M) * (1 + D.K + D.K ^ 2) ≤ D.a₁ := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hB := Bnat_le D H hC₀ hεL0 hεLη
  have hB0 : 0 ≤ D.Bnat C₀ := by unfold CoreData.Bnat; positivity
  have hK2 : 1 + D.K + D.K ^ 2 ≤ 3 * D.N ^ (2 * η) := by
    have : D.K ^ 2 ≤ D.N ^ (2 * η) := by
      have := pow_le_rpow_mul hK1 hKη hN0 2; simpa using this
    nlinarith
  have hχ0 : 0 < D.N ^ (-D.M) := Real.rpow_pos_of_pos hN0 _
  calc 18 * D.Bnat C₀ * D.N ^ (-D.M) * (1 + D.K + D.K ^ 2)
      ≤ 18 * (C₀ * D.N ^ (3 * η + 4 * D.κ * D.s₀)) * D.N ^ (-D.M) * (3 * D.N ^ (2 * η)) := by
        gcongr
    _ = 54 * C₀ * D.N ^ (5 * η + 4 * D.κ * D.s₀ - D.M + D.s₁) * D.N ^ (-D.s₁) := by
        rw [show 54 * C₀ * D.N ^ (5 * η + 4 * D.κ * D.s₀ - D.M + D.s₁) * D.N ^ (-D.s₁) =
          54 * C₀ * (D.N ^ (5 * η + 4 * D.κ * D.s₀ - D.M + D.s₁) * D.N ^ (-D.s₁)) by ring,
          rpow_mul_rpow hN0]
        rw [show 18 * (C₀ * D.N ^ (3 * η + 4 * D.κ * D.s₀)) * D.N ^ (-D.M) * (3 * D.N ^ (2 * η)) =
          54 * C₀ * (D.N ^ (3 * η + 4 * D.κ * D.s₀) * D.N ^ (-D.M) * D.N ^ (2 * η)) by ring,
          rpow_mul_rpow hN0, rpow_mul_rpow hN0]
        congr 2; ring
    _ ≤ 1 * D.N ^ (-D.s₁) := mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg hN0.le _)
    _ = D.a₁ := by rw [one_mul]; rfl

/-- The second crossing smallness condition. -/
theorem num_F2 (D : CoreData α) (H : CoreHyp D) {C₀ η : ℝ} (hC₀ : 0 < C₀) (hεL0 : 0 ≤ D.εL)
    (hεLη : D.εL ≤ η) (hKη : D.K ≤ D.N ^ η) (hχD : D.N ^ (-D.M) ≤ D.Dw) (hDw1 : D.Dw ≤ 1)
    (hbig : 198 * C₀ * D.N ^ (4 * η + 4 * D.κ * D.s₀ - D.M + D.s₁) ≤ 1) :
    2 * D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M) ≤ D.a₁ := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hB := Bnat_le D H hC₀ hεL0 hεLη
  have hB0 : 0 ≤ D.Bnat C₀ := by unfold CoreData.Bnat; positivity
  have hχ0 : 0 < D.N ^ (-D.M) := Real.rpow_pos_of_pos hN0 _
  have hχ1 : D.N ^ (-D.M) ≤ 1 := hχD.trans hDw1
  have hG : 1 + 2 * (D.K + 2 * D.Dw + 2 * D.N ^ (-D.M)) ≤ 11 * D.N ^ η := by
    have : 1 ≤ D.N ^ η := le_trans hK1 hKη
    linarith
  unfold CoreData.crossG
  calc 2 * (9 * D.Bnat C₀ * (1 + 2 * (D.K + 2 * D.Dw + 2 * D.N ^ (-D.M)))) * D.N ^ (-D.M)
      ≤ 2 * (9 * (C₀ * D.N ^ (3 * η + 4 * D.κ * D.s₀)) * (11 * D.N ^ η)) * D.N ^ (-D.M) := by
        have hG0 : 0 ≤ 1 + 2 * (D.K + 2 * D.Dw + 2 * D.N ^ (-D.M)) := by
          have : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
          linarith
        have := mul_le_mul (mul_le_mul_of_nonneg_left hB (by norm_num : (0:ℝ) ≤ 9)) hG hG0
          (by positivity)
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num : (0:ℝ) ≤ 2))
          hχ0.le
        linarith
    _ = 198 * C₀ * D.N ^ (4 * η + 4 * D.κ * D.s₀ - D.M + D.s₁) * D.N ^ (-D.s₁) := by
        rw [show 198 * C₀ * D.N ^ (4 * η + 4 * D.κ * D.s₀ - D.M + D.s₁) * D.N ^ (-D.s₁) =
          198 * C₀ * (D.N ^ (4 * η + 4 * D.κ * D.s₀ - D.M + D.s₁) * D.N ^ (-D.s₁)) by ring,
          rpow_mul_rpow hN0]
        rw [show 2 * (9 * (C₀ * D.N ^ (3 * η + 4 * D.κ * D.s₀)) * (11 * D.N ^ η)) * D.N ^ (-D.M) =
          198 * C₀ * (D.N ^ (3 * η + 4 * D.κ * D.s₀) * D.N ^ η * D.N ^ (-D.M)) by ring,
          rpow_mul_rpow hN0, rpow_mul_rpow hN0]
        congr 2; ring
    _ ≤ 1 * D.N ^ (-D.s₁) := mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg hN0.le _)
    _ = D.a₁ := by rw [one_mul]; rfl

/-- `C N^x ≤ N^y` from `C N^(x-y) ≤ 1`. -/
theorem le_rpow_of_big {N C x y : ℝ} (hN : 0 < N) (hbig : C * N ^ (x - y) ≤ 1) :
    C * N ^ x ≤ N ^ y := by
  have e : C * N ^ x = C * N ^ (x - y) * N ^ y := by
    rw [mul_assoc, rpow_mul_rpow hN]; congr 2; ring
  rw [e]
  calc C * N ^ (x - y) * N ^ y ≤ 1 * N ^ y :=
        mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg hN.le _)
    _ = N ^ y := one_mul _

/-- The ancestor slope bound. -/
theorem Λa_le (D : CoreData α) (H : CoreHyp D) (hDa : D.Dw ≤ D.a₀)
    (hq0 : D.N ^ (-D.κ * D.s₀) ≤ D.K * D.f₀.q) :
    D.Λa ≤ 4 * D.K ^ 4 * (D.a₀ / D.Dw) := by
  have hN0 : 0 < D.N := by linarith [H.N2]
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hDw0 : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hq00 := f₀_q_pos D
  have hq02 : D.a₀ / D.f₀.q ^ 2 ≤ D.K ^ 2 * (D.a₀ / D.Dw) := by
    have h1 : (D.N ^ (-D.κ * D.s₀)) ^ 2 ≤ (D.K * D.f₀.q) ^ 2 :=
      pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hq0 2
    have hg : 0 < (D.N ^ (-D.κ * D.s₀)) ^ 2 := by positivity
    rw [Dw_eq_sq D H, mul_div_assoc', div_le_div_iff₀ (by positivity) hg]
    have : D.a₀ * (D.N ^ (-D.κ * D.s₀)) ^ 2 ≤ D.a₀ * (D.K * D.f₀.q) ^ 2 :=
      mul_le_mul_of_nonneg_left h1 ha0.le
    calc D.a₀ * (D.N ^ (-D.κ * D.s₀)) ^ 2 ≤ D.a₀ * (D.K * D.f₀.q) ^ 2 := this
      _ = D.K ^ 2 * D.a₀ * D.f₀.q ^ 2 := by ring
  have hratio : 1 ≤ D.a₀ / D.Dw := by rw [le_div_iff₀ hDw0]; linarith
  unfold CoreData.Λa
  have hK2 : D.K ^ 2 ≤ D.K ^ 4 := pow_le_pow_right₀ hK1 (by norm_num)
  have h1 : 1 + D.a₀ / D.f₀.q ^ 2 ≤ 2 * D.K ^ 2 * (D.a₀ / D.Dw) := by
    have : 1 ≤ D.K ^ 2 * (D.a₀ / D.Dw) := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hK1) hratio
    linarith
  calc 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) ≤ 2 * D.K ^ 2 * (2 * D.K ^ 2 * (D.a₀ / D.Dw)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = 4 * D.K ^ 4 * (D.a₀ / D.Dw) := by ring

/-- The pruning loss. -/
theorem num_loss (D : CoreData α) (H : CoreHyp D) {η η₁ : ℝ} (hεL0 : 0 ≤ D.εL) (hεLη : D.εL ≤ η)
    (hKη : D.K ≤ D.N ^ η) (hη : 0 ≤ η) (hbig : 6426 * D.N ^ (5 * η - η₁) ≤ 1) :
    (810 * D.K ^ 4 + 4 * (594 * (D.N ^ D.εL) ^ 2 * D.N ^ D.εL) + 27) / D.N ^ η₁ ≤
      D.N ^ (-D.εL) / 2 := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hE : D.N ^ D.εL ≤ D.N ^ η := rpow_le_rpow_exp hN1 hεLη
  have hE0 : 0 ≤ D.N ^ D.εL := Real.rpow_nonneg hN0.le _
  have hη1 : 1 ≤ D.N ^ η := Real.one_le_rpow hN1 hη
  have hK4 : D.K ^ 4 ≤ D.N ^ (4 * η) := by
    have := pow_le_rpow_mul hK1 hKη hN0 4; simpa using this
  have hE3 : (D.N ^ D.εL) ^ 2 * D.N ^ D.εL ≤ D.N ^ (4 * η) := by
    have h3 : (D.N ^ D.εL) ^ 2 * D.N ^ D.εL = (D.N ^ D.εL) ^ 3 := by ring
    rw [h3]
    calc (D.N ^ D.εL) ^ 3 ≤ (D.N ^ η) ^ 3 := pow_le_pow_left₀ hE0 hE 3
      _ = D.N ^ (3 * η) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
      _ ≤ D.N ^ (4 * η) := rpow_le_rpow_exp hN1 (by linarith)
  have h27 : (27 : ℝ) ≤ 27 * D.N ^ (4 * η) := by
    have : 1 ≤ D.N ^ (4 * η) := Real.one_le_rpow hN1 (by linarith)
    linarith
  have hnum : 810 * D.K ^ 4 + 4 * (594 * (D.N ^ D.εL) ^ 2 * D.N ^ D.εL) + 27 ≤
      3213 * D.N ^ (4 * η) := by nlinarith
  have hK₁ : 0 < D.N ^ η₁ := Real.rpow_pos_of_pos hN0 _
  rw [div_le_iff₀ hK₁]
  have hεL' : D.N ^ (-η) ≤ D.N ^ (-D.εL) := rpow_le_rpow_exp hN1 (by linarith)
  have hb := le_rpow_of_big hN0 (x := 4 * η) (y := η₁ - η) (C := 6426) (by
    have e : 4 * η - (η₁ - η) = 5 * η - η₁ := by ring
    rw [e]; exact hbig)
  have e2 : D.N ^ (η₁ - η) = D.N ^ (-η) * D.N ^ η₁ := by rw [rpow_mul_rpow hN0]; congr 1; ring
  rw [e2] at hb
  calc 810 * D.K ^ 4 + 4 * (594 * (D.N ^ D.εL) ^ 2 * D.N ^ D.εL) + 27 ≤ 3213 * D.N ^ (4 * η) := hnum
    _ ≤ D.N ^ (-η) * D.N ^ η₁ / 2 := by linarith
    _ ≤ D.N ^ (-D.εL) / 2 * D.N ^ η₁ := by
        rw [div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hεL' hK₁.le) (by norm_num)

/-- Scalar's size conditions on `K` and the mass. -/
theorem num_Kη (D : CoreData α) (H : CoreHyp D) {η ηS : ℝ} (hεLη : D.εL ≤ η)
    (hKη : D.K ≤ D.N ^ η) (hbig : 2 * D.N ^ (η - ηS) ≤ 1) :
    2 * D.K ≤ D.N ^ ηS ∧ D.N ^ (-ηS) ≤ D.N ^ (-D.εL) / 2 := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hb := le_rpow_of_big hN0 (x := η) (y := ηS) (C := 2) hbig
  refine ⟨by linarith, ?_⟩
  have hb2 := le_rpow_of_big hN0 (x := -ηS) (y := -η) (C := 2) (by
    have e : -ηS - -η = η - ηS := by ring
    rw [e]; exact hbig)
  have : D.N ^ (-η) ≤ D.N ^ (-D.εL) := rpow_le_rpow_exp hN1 (by linarith)
  linarith

/-- The doubled coarse scale is small. -/
theorem num_2a0 (D : CoreData α) (H : CoreHyp D) (hbig : 2 * D.N ^ (-D.s₀) ≤ 1) :
    2 * D.a₀ ≤ 1 := hbig

/-- The deep spread is below one terminal bin. -/
theorem num_deep (D : CoreData α) (H : CoreHyp D) {η s : ℝ} (hKη : D.K ≤ D.N ^ η)
    (hκ1 : D.κ ≤ 1) (hse : 0 ≤ D.se) (hκ0 : 0 ≤ D.κ) (hDa : D.Dw ≤ D.a₀)
    (hq0 : D.N ^ (-D.κ * D.s₀) ≤ D.K * D.f₀.q)
    (hbig : 68 * D.N ^ (7 * η - D.κ * D.se + 2 * D.κ * D.s₀ + s) ≤ 1) :
    D.deepSpread ≤ D.N ^ (-s) := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hDw0 : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  obtain ⟨hqe1, hqe2⟩ := fam_q_bounds H.fegood hN0 hK0
  set ge := D.N ^ (-D.κ * D.se) with hge
  set ae := D.N ^ (-D.se) with hae
  set qe := D.fe.q with hqe
  have hqe0 : 0 < qe := by rw [hqe]; unfold Fam.q; positivity
  have hge0 : 0 < ge := Real.rpow_pos_of_pos hN0 _
  have hae0 : 0 < ae := Real.rpow_pos_of_pos hN0 _
  have haege : ae ≤ ge := rpow_le_rpow_exp hN1 (by nlinarith)
  have hge1 : ge ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hN1 (by nlinarith)
  have hΛ := Λa_le D H hDa hq0
  have hratio : 1 ≤ D.a₀ / D.Dw := by rw [le_div_iff₀ hDw0]; linarith
  -- the four terms
  have hKge : ge ≤ D.K * ge := le_mul_of_one_le_left hge0.le hK1
  have T1 : 2 * (D.K * ae) ≤ 2 * D.K * ge := by
    have := mul_le_mul_of_nonneg_left haege hK0.le
    linarith only [this]
  have T2 : D.K * (1 + ae / qe) * (qe + 3 * D.K * qe) ≤ 8 * D.K ^ 3 * ge := by
    have e : D.K * (1 + ae / qe) * (qe + 3 * D.K * qe) = D.K * (qe + ae) * (1 + 3 * D.K) := by
      field_simp
    rw [e]
    have h1 : qe + ae ≤ 2 * D.K * ge := by linarith only [hqe1, haege, hKge]
    have h2 : 1 + 3 * D.K ≤ 4 * D.K := by linarith only [hK1]
    have h3 : 0 ≤ qe + ae := by linarith only [hqe0, hae0]
    calc D.K * (qe + ae) * (1 + 3 * D.K) ≤ D.K * (2 * D.K * ge) * (4 * D.K) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 hK0.le) h2 (by linarith only [hK1])
            (by positivity)
      _ = 8 * D.K ^ 3 * ge := by ring
  have T3 : D.K * (1 + ae / qe ^ 2) * (5 / 2 * D.K * qe * qe + 3 / 2 * D.K * qe * (3 * D.K * qe) +
      2 * (D.K * qe * ge)) ≤ 18 * D.K ^ 5 * ge := by
    have hb : 5 / 2 * D.K * qe * qe + 3 / 2 * D.K * qe * (3 * D.K * qe) + 2 * (D.K * qe * ge) ≤
        9 * D.K ^ 2 * qe ^ 2 := by
      have h1 : D.K * qe * ge ≤ D.K * qe * (D.K * qe) := mul_le_mul_of_nonneg_left hqe2 (by positivity)
      have h2 : D.K * qe * qe ≤ D.K ^ 2 * qe ^ 2 := by
        have : D.K ≤ D.K ^ 2 := le_self_pow₀ hK1 (by norm_num)
        have := mul_le_mul_of_nonneg_right this (sq_nonneg qe)
        calc D.K * qe * qe = D.K * qe ^ 2 := by ring
          _ ≤ D.K ^ 2 * qe ^ 2 := this
      have e1 : D.K * qe * (D.K * qe) = D.K ^ 2 * qe ^ 2 := by ring
      have e2 : 3 / 2 * D.K * qe * (3 * D.K * qe) = 9 / 2 * (D.K ^ 2 * qe ^ 2) := by ring
      rw [e2]
      linarith only [h1, h2, e1]
    have hA : 0 ≤ D.K * (1 + ae / qe ^ 2) := by positivity
    have e : D.K * (1 + ae / qe ^ 2) * (9 * D.K ^ 2 * qe ^ 2) = 9 * D.K ^ 3 * (qe ^ 2 + ae) := by
      field_simp
    have hq2 : qe ^ 2 ≤ D.K ^ 2 * ge := by
      have h1 : qe ^ 2 ≤ (D.K * ge) ^ 2 := pow_le_pow_left₀ hqe0.le hqe1 2
      have h2 : (D.K * ge) ^ 2 = D.K ^ 2 * (ge * ge) := by ring
      have h3 : ge * ge ≤ ge := mul_le_of_le_one_left hge0.le hge1
      have h4 := mul_le_mul_of_nonneg_left h3 (sq_nonneg D.K)
      linarith only [h1, h2, h4]
    have hae2 : ae ≤ D.K ^ 2 * ge := haege.trans (le_mul_of_one_le_left hge0.le (one_le_pow₀ hK1))
    calc _ ≤ D.K * (1 + ae / qe ^ 2) * (9 * D.K ^ 2 * qe ^ 2) := mul_le_mul_of_nonneg_left hb hA
      _ = 9 * D.K ^ 3 * (qe ^ 2 + ae) := e
      _ ≤ 9 * D.K ^ 3 * (D.K ^ 2 * ge + D.K ^ 2 * ge) :=
          mul_le_mul_of_nonneg_left (add_le_add hq2 hae2) (by positivity)
      _ = 18 * D.K ^ 5 * ge := by ring
  have T4 : 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) * (qe + 3 * D.K * qe +
      (D.K * qe + D.K * (3 * D.K * qe) + 2 * (D.K * qe * ge))) ≤
      40 * D.K ^ 7 * (D.a₀ / D.Dw) * ge := by
    have hb : qe + 3 * D.K * qe + (D.K * qe + D.K * (3 * D.K * qe) + 2 * (D.K * qe * ge)) ≤
        10 * D.K ^ 3 * ge := by
      have h1 : D.K * qe * ge ≤ D.K * qe := mul_le_of_le_one_right (by positivity) hge1
      have b1 : qe + 3 * D.K * qe + (D.K * qe + D.K * (3 * D.K * qe) + 2 * (D.K * qe * ge)) ≤
          qe * (1 + 6 * D.K + 3 * D.K ^ 2) := by
        have e : qe * (1 + 6 * D.K + 3 * D.K ^ 2) = qe + 3 * D.K * qe + (D.K * qe +
            D.K * (3 * D.K * qe) + 2 * (D.K * qe)) := by ring
        rw [e]; linarith only [h1]
      have b2 : 1 + 6 * D.K + 3 * D.K ^ 2 ≤ 10 * D.K ^ 2 := by nlinarith only [hK1]
      have b3 := mul_le_mul_of_nonneg_left b2 hqe0.le
      have b4 : qe * (10 * D.K ^ 2) ≤ D.K * ge * (10 * D.K ^ 2) :=
        mul_le_mul_of_nonneg_right hqe1 (by positivity)
      have e2 : D.K * ge * (10 * D.K ^ 2) = 10 * D.K ^ 3 * ge := by ring
      linarith only [b1, b3, b4, e2]
    have hΛ' : 2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) ≤ 4 * D.K ^ 4 * (D.a₀ / D.Dw) := hΛ
    have hb0 : 0 ≤ qe + 3 * D.K * qe + (D.K * qe + D.K * (3 * D.K * qe) + 2 * (D.K * qe * ge)) := by
      positivity
    calc _ ≤ 4 * D.K ^ 4 * (D.a₀ / D.Dw) * (10 * D.K ^ 3 * ge) :=
          mul_le_mul hΛ' hb hb0 (by positivity)
      _ = 40 * D.K ^ 7 * (D.a₀ / D.Dw) * ge := by ring
  have hsum : 2 * (D.K * ae) + D.K * (1 + ae / qe) * (qe + 3 * D.K * qe) +
      D.K * (1 + ae / qe ^ 2) * (5 / 2 * D.K * qe * qe + 3 / 2 * D.K * qe * (3 * D.K * qe) +
        2 * (D.K * qe * ge)) +
      2 * D.K ^ 2 * (1 + D.a₀ / D.f₀.q ^ 2) * (qe + 3 * D.K * qe +
        (D.K * qe + D.K * (3 * D.K * qe) + 2 * (D.K * qe * ge))) ≤
      68 * D.K ^ 7 * (D.a₀ / D.Dw) * ge := by
    have k1 : D.K ≤ D.K ^ 7 := le_self_pow₀ hK1 (by norm_num)
    have k3 : D.K ^ 3 ≤ D.K ^ 7 := pow_le_pow_right₀ hK1 (by norm_num)
    have k5 : D.K ^ 5 ≤ D.K ^ 7 := pow_le_pow_right₀ hK1 (by norm_num)
    have hX0 : D.K ^ 7 * ge ≤ D.K ^ 7 * (D.a₀ / D.Dw * ge) :=
      mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hge0.le hratio) (by positivity)
    have hX : D.K ^ 7 * ge ≤ D.K ^ 7 * (D.a₀ / D.Dw) * ge := by
      calc D.K ^ 7 * ge ≤ D.K ^ 7 * (D.a₀ / D.Dw * ge) := hX0
        _ = D.K ^ 7 * (D.a₀ / D.Dw) * ge := by ring
    have a1 : 2 * D.K * ge ≤ 2 * (D.K ^ 7 * ge) := by
      have := mul_le_mul_of_nonneg_right k1 hge0.le; linarith only [this]
    have a2 : 8 * D.K ^ 3 * ge ≤ 8 * (D.K ^ 7 * ge) := by
      have := mul_le_mul_of_nonneg_right k3 hge0.le; linarith only [this]
    have a3 : 18 * D.K ^ 5 * ge ≤ 18 * (D.K ^ 7 * ge) := by
      have := mul_le_mul_of_nonneg_right k5 hge0.le; linarith only [this]
    linarith only [T1, T2, T3, T4, a1, a2, a3, hX]
  unfold CoreData.deepSpread
  rw [← hge, ← hae, ← hqe]
  rw [div_le_iff₀ ha0]
  refine hsum.trans ?_
  -- 68 K^7 (a₀/D) ge ≤ N^(-s) a₀
  have hK7 : D.K ^ 7 ≤ D.N ^ (7 * η) := by
    have := pow_le_rpow_mul hK1 hKη hN0 7; simpa using this
  have hgeD : ge / D.Dw = D.N ^ (-D.κ * D.se + 2 * D.κ * D.s₀) := by
    rw [hge]; unfold CoreData.Dw
    rw [div_eq_mul_inv, ← Real.rpow_neg hN0.le, rpow_mul_rpow hN0]; congr 1; ring
  have hb := le_rpow_of_big hN0 (C := 68) (x := 7 * η + (-D.κ * D.se + 2 * D.κ * D.s₀))
    (y := -s) (by
      have e : 7 * η + (-D.κ * D.se + 2 * D.κ * D.s₀) - -s = 7 * η - D.κ * D.se + 2 * D.κ * D.s₀ + s :=
        by ring
      rw [e]; exact hbig)
  rw [← rpow_mul_rpow hN0, ← hgeD] at hb
  calc 68 * D.K ^ 7 * (D.a₀ / D.Dw) * ge = 68 * D.K ^ 7 * (ge / D.Dw) * D.a₀ := by ring
    _ ≤ 68 * D.N ^ (7 * η) * (ge / D.Dw) * D.a₀ := by gcongr
    _ ≤ D.N ^ (-s) * D.a₀ := by
        apply mul_le_mul_of_nonneg_right _ ha0.le
        rw [mul_assoc]; exact hb

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
