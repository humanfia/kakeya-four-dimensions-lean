import Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return.NumFacts2

/-!
# Sample numerics: caps and the slice window

The cap numerics of Scalar; the key crossing estimate `Lip · δ₂ ≤ a₁` (kept slice laws barely
move across a candidate label's plank); the hidden spread of a candidate label in a Scalar cell.
-/

namespace Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {α : Type} [MeasurableSpace α]

/-- Scalar's cap numerics. -/
theorem num_cap (D : CoreData α) (H : CoreHyp D) {η m ηS : ℝ} (hKη : D.K ≤ D.N ^ η)
    (hσgc : D.N ^ (-m) ≤ D.N ^ (-D.κ * D.sc))
    (hbig : 1584 * D.N ^ (4 * η + D.S / D.Rcap - ηS) ≤ 1) :
    D.capLHS (D.N ^ (-m)) ≤ D.capRHS (D.N ^ (-m)) ηS := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  have hqc : 0 < D.fc.q := by unfold Fam.q; positivity
  have hσ : 0 < D.N ^ (-m) := Real.rpow_pos_of_pos hN0 _
  have hgc : 0 < D.N ^ (-D.κ * D.sc) := Real.rpow_pos_of_pos hN0 _
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have hac : 0 < D.ac := Real.rpow_pos_of_pos hN0 _
  have ha0d : 0 < D.a₀ ^ D.d := Real.rpow_pos_of_pos ha0 _
  have hacd : 0 < D.ac ^ D.d := Real.rpow_pos_of_pos hac _
  have hNS : 0 < D.N ^ (D.S / D.Rcap) := Real.rpow_pos_of_pos hN0 _
  -- abstract identities
  have idL : ∀ X h a E : ℝ, h ≠ 0 → 36 * (2 * X / h + 5) * (2 * (D.K * h ^ 3 * (2 * a))) * (D.K * E) =
      144 * D.K ^ 2 * E * a * h ^ 2 * (2 * X + 5 * h) := by
    intro X h a E hh; field_simp; ring
  have idR : ∀ (σ' A C q g : ℝ), 0 < C → A ^ D.d / C ^ D.d * (q * (C ^ D.d * q ^ 2 * g / D.K)) =
      A ^ D.d * q ^ 3 * g / D.K := by
    intro σ' A C q g hC
    have : C ^ D.d ≠ 0 := (Real.rpow_pos_of_pos hC _).ne'
    field_simp
  have hσq : D.N ^ (-m) * D.fc.q ≠ 0 := by positivity
  have hL : D.capLHS (D.N ^ (-m)) = 144 * D.K ^ 2 * D.N ^ (D.S / D.Rcap) * D.a₀ ^ D.d *
      (D.N ^ (-m) * D.fc.q) ^ 2 * (2 * (D.K * D.fc.q * D.N ^ (-D.κ * D.sc) +
        2 * D.K * (D.N ^ (-m) * D.fc.q)) + 5 * (D.N ^ (-m) * D.fc.q)) := by
    unfold CoreData.capLHS
    exact idL _ _ _ _ hσq
  have hR : D.capRHS (D.N ^ (-m)) ηS = D.N ^ ηS * (D.N ^ (-m)) ^ 2 *
      (D.a₀ ^ D.d * D.fc.q ^ 3 * D.N ^ (-D.κ * D.sc) / D.K) := by
    unfold CoreData.capRHS
    rw [Real.div_rpow ha0.le hac.le, mul_assoc (D.N ^ ηS * (D.N ^ (-m)) ^ 2)]
    congr 1
    exact idR 0 D.a₀ D.ac D.fc.q _ hac
  rw [hL, hR]
  -- the cell factor
  have hA : 2 * (D.K * D.fc.q * D.N ^ (-D.κ * D.sc) + 2 * D.K * (D.N ^ (-m) * D.fc.q)) +
      5 * (D.N ^ (-m) * D.fc.q) ≤ 11 * D.K * (D.fc.q * D.N ^ (-D.κ * D.sc)) := by
    have h1 : D.N ^ (-m) * D.fc.q ≤ D.fc.q * D.N ^ (-D.κ * D.sc) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left hσgc hqc.le
    have h2 : D.N ^ (-m) * D.fc.q ≤ D.K * (D.fc.q * D.N ^ (-D.κ * D.sc)) :=
      h1.trans (le_mul_of_one_le_left (by positivity) hK1)
    have h3 : D.K * (D.N ^ (-m) * D.fc.q) ≤ D.K * (D.fc.q * D.N ^ (-D.κ * D.sc)) :=
      mul_le_mul_of_nonneg_left h1 hK0.le
    have e : D.K * D.fc.q * D.N ^ (-D.κ * D.sc) = D.K * (D.fc.q * D.N ^ (-D.κ * D.sc)) := by ring
    rw [e]; linarith only [h2, h3]
  have hK4 : D.K ^ 4 ≤ D.N ^ (4 * η) := by
    have := pow_le_rpow_mul hK1 hKη hN0 4; simpa using this
  have hb := le_rpow_of_big hN0 (C := 1584) (x := 4 * η + D.S / D.Rcap) (y := ηS) hbig
  rw [← rpow_mul_rpow hN0] at hb
  have hX : 0 ≤ D.a₀ ^ D.d * (D.N ^ (-m) * D.fc.q) ^ 2 * (D.fc.q * D.N ^ (-D.κ * D.sc)) := by
    positivity
  have hP : 0 ≤ 144 * D.K ^ 2 * D.N ^ (D.S / D.Rcap) * D.a₀ ^ D.d * (D.N ^ (-m) * D.fc.q) ^ 2 := by
    positivity
  calc 144 * D.K ^ 2 * D.N ^ (D.S / D.Rcap) * D.a₀ ^ D.d * (D.N ^ (-m) * D.fc.q) ^ 2 *
        (2 * (D.K * D.fc.q * D.N ^ (-D.κ * D.sc) + 2 * D.K * (D.N ^ (-m) * D.fc.q)) +
          5 * (D.N ^ (-m) * D.fc.q))
      ≤ 144 * D.K ^ 2 * D.N ^ (D.S / D.Rcap) * D.a₀ ^ D.d * (D.N ^ (-m) * D.fc.q) ^ 2 *
        (11 * D.K * (D.fc.q * D.N ^ (-D.κ * D.sc))) := mul_le_mul_of_nonneg_left hA hP
    _ = 1584 * D.K ^ 3 * D.N ^ (D.S / D.Rcap) *
          (D.a₀ ^ D.d * (D.N ^ (-m) * D.fc.q) ^ 2 * (D.fc.q * D.N ^ (-D.κ * D.sc))) := by ring
    _ ≤ 1584 * D.K ^ 4 * D.N ^ (D.S / D.Rcap) *
          (D.a₀ ^ D.d * (D.N ^ (-m) * D.fc.q) ^ 2 * (D.fc.q * D.N ^ (-D.κ * D.sc))) / D.K := by
        rw [le_div_iff₀ hK0]
        have e : 1584 * D.K ^ 3 * D.N ^ (D.S / D.Rcap) *
            (D.a₀ ^ D.d * (D.N ^ (-m) * D.fc.q) ^ 2 * (D.fc.q * D.N ^ (-D.κ * D.sc))) * D.K =
            1584 * D.K ^ 4 * D.N ^ (D.S / D.Rcap) *
            (D.a₀ ^ D.d * (D.N ^ (-m) * D.fc.q) ^ 2 * (D.fc.q * D.N ^ (-D.κ * D.sc))) := by ring
        rw [e]
    _ ≤ 1584 * D.N ^ (4 * η) * D.N ^ (D.S / D.Rcap) *
          (D.a₀ ^ D.d * (D.N ^ (-m) * D.fc.q) ^ 2 * (D.fc.q * D.N ^ (-D.κ * D.sc))) / D.K := by
        gcongr
    _ ≤ D.N ^ ηS * (D.a₀ ^ D.d * (D.N ^ (-m) * D.fc.q) ^ 2 * (D.fc.q * D.N ^ (-D.κ * D.sc))) / D.K := by
        gcongr
        rw [mul_assoc]; exact hb
    _ = D.N ^ ηS * (D.N ^ (-m)) ^ 2 *
          (D.a₀ ^ D.d * D.fc.q ^ 3 * D.N ^ (-D.κ * D.sc) / D.K) := by ring

/-- The key crossing estimate: kept slice laws barely move across a candidate plank. -/
theorem num_lip (D : CoreData α) (H : CoreHyp D) {η η₁ C₀ m : ℝ} (hC₀ : 0 < C₀)
    (hεL0 : 0 ≤ D.εL) (hεLη : D.εL ≤ η) (hKη : D.K ≤ D.N ^ η) (hη₁ : 0 ≤ η₁)
    (hd0 : 0 ≤ D.d) (hd1 : D.d < 1)
    (hχD : D.N ^ (-D.M) ≤ D.Dw) (hDa : D.Dw ≤ D.a₀) (ha10 : D.a₁ ≤ D.a₀)
    (hq0 : D.N ^ (-D.κ * D.s₀) ≤ D.K * D.f₀.q)
    (hF1 : 18 * D.Bnat C₀ * D.N ^ (-D.M) * (1 + D.K + D.K ^ 2) ≤ D.a₁)
    (hF2 : 2 * D.crossG D.M D.Dw (D.Bnat C₀) * D.N ^ (-D.M) ≤ D.a₁)
    (hσgc : D.N ^ (-m) ≤ D.N ^ (-D.κ * D.sc))
    (hbig1 : 112 * (10 ^ 9 : ℝ) ^ (1 / (1 - D.d)) * D.N ^ ((15 * η + 3 * η₁) * (1 / (1 - D.d)) +
      2 * η - D.s₀ + 2 * D.κ * D.s₀ - 2 * D.κ * D.sc + D.s₁) ≤ 1)
    (hbig2 : 8 * D.N ^ (2 * η - 2 * D.κ * D.sc) ≤ 1) :
    D.crossLip D.M D.Dw (D.N ^ η₁) (D.Bnat C₀) * D.cellδ2 (D.N ^ (-m)) ≤ D.a₁ := by
  have hN1 : 1 ≤ D.N := by linarith [H.N2]
  have hN0 : 0 < D.N := by linarith
  have hK1 := H.K1
  have hK0 : 0 < D.K := by linarith
  have hK₁ : 1 ≤ D.N ^ η₁ := Real.one_le_rpow hN1 hη₁
  have hE1 : 1 ≤ D.N ^ D.εL := Real.one_le_rpow hN1 hεL0
  have hE : D.N ^ D.εL ≤ D.N ^ η := rpow_le_rpow_exp hN1 hεLη
  have ha0 : 0 < D.a₀ := Real.rpow_pos_of_pos hN0 _
  have ha1 : 0 < D.a₁ := Real.rpow_pos_of_pos hN0 _
  have hDw0 : 0 < D.Dw := Real.rpow_pos_of_pos hN0 _
  have hgc0 : 0 < D.N ^ (-D.κ * D.sc) := Real.rpow_pos_of_pos hN0 _
  have hp : 0 < 1 / (1 - D.d) := by apply div_pos one_pos; linarith
  have hLip := crossLip_le D H hK₁ hC₀ hεL0 hd0 hd1 hχD hDa ha10 hq0 (Dw_eq_sq D H) hF1 hF2
  have hδ := cellδ2_le D H hσgc
  have hδ0 : 0 ≤ D.cellδ2 (D.N ^ (-m)) := by
    unfold CoreData.cellδ2; have : 0 < D.fc.q := by unfold Fam.q; positivity
    positivity
  have hLip0 := crossLip_nonneg D H (r := D.M) (Hx := D.Dw) (K₁ := D.N ^ η₁) (B := D.Bnat C₀)
  -- the crossing constant as a power
  have hX : 10 ^ 9 * D.K ^ 12 * (D.N ^ η₁) ^ 3 * (D.N ^ D.εL) ^ 3 ≤
      10 ^ 9 * D.N ^ (15 * η + 3 * η₁) := by
    have h12 : D.K ^ 12 ≤ D.N ^ (12 * η) := by
      have := pow_le_rpow_mul hK1 hKη hN0 12; simpa using this
    have h3 : (D.N ^ D.εL) ^ 3 ≤ D.N ^ (3 * η) := by
      calc (D.N ^ D.εL) ^ 3 ≤ (D.N ^ η) ^ 3 := pow_le_pow_left₀ (by positivity) hE 3
        _ = D.N ^ (3 * η) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    have h31 : (D.N ^ η₁) ^ 3 = D.N ^ (3 * η₁) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
    rw [h31]
    calc 10 ^ 9 * D.K ^ 12 * D.N ^ (3 * η₁) * (D.N ^ D.εL) ^ 3
        ≤ 10 ^ 9 * D.N ^ (12 * η) * D.N ^ (3 * η₁) * D.N ^ (3 * η) := by gcongr
      _ = 10 ^ 9 * D.N ^ (15 * η + 3 * η₁) := by
          rw [mul_assoc (10 ^ 9 : ℝ), mul_assoc (10 ^ 9 : ℝ), rpow_mul_rpow hN0, rpow_mul_rpow hN0]
          congr 2; ring
  have hXp : (10 ^ 9 * D.K ^ 12 * (D.N ^ η₁) ^ 3 * (D.N ^ D.εL) ^ 3) ^ (1 / (1 - D.d)) ≤
      (10 ^ 9 : ℝ) ^ (1 / (1 - D.d)) * D.N ^ ((15 * η + 3 * η₁) * (1 / (1 - D.d))) := by
    calc (10 ^ 9 * D.K ^ 12 * (D.N ^ η₁) ^ 3 * (D.N ^ D.εL) ^ 3) ^ (1 / (1 - D.d))
        ≤ (10 ^ 9 * D.N ^ (15 * η + 3 * η₁)) ^ (1 / (1 - D.d)) :=
          Real.rpow_le_rpow (by positivity) hX hp.le
      _ = (10 ^ 9 : ℝ) ^ (1 / (1 - D.d)) * D.N ^ ((15 * η + 3 * η₁) * (1 / (1 - D.d))) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hN0.le]
  set Y := (10 ^ 9 : ℝ) ^ (1 / (1 - D.d)) * D.N ^ ((15 * η + 3 * η₁) * (1 / (1 - D.d))) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hLip' : D.crossLip D.M D.Dw (D.N ^ η₁) (D.Bnat C₀) ≤ 14 * Y * (D.a₀ / D.Dw) + D.a₁ := by
    refine hLip.trans ?_
    have : 0 ≤ D.a₀ / D.Dw := by positivity
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hXp (by norm_num : (0:ℝ) ≤ 14)) this
    linarith only [this]
  -- the two terms
  have hK2 : D.K ^ 2 ≤ D.N ^ (2 * η) := by
    have := pow_le_rpow_mul hK1 hKη hN0 2; simpa using this
  have hgc2 : (D.N ^ (-D.κ * D.sc)) ^ 2 = D.N ^ (-2 * D.κ * D.sc) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; congr 1; push_cast; ring
  have hDinv : D.a₀ / D.Dw = D.N ^ (-D.s₀ + 2 * D.κ * D.s₀) := by
    unfold CoreData.a₀ CoreData.Dw
    rw [div_eq_mul_inv, ← Real.rpow_neg hN0.le, rpow_mul_rpow hN0]; congr 1; ring
  have T1 : 14 * Y * (D.a₀ / D.Dw) * (4 * D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2) ≤ D.a₁ / 2 := by
    have hb := le_rpow_of_big hN0 (C := 112 * (10 ^ 9 : ℝ) ^ (1 / (1 - D.d)))
      (x := (15 * η + 3 * η₁) * (1 / (1 - D.d)) + 2 * η + (-D.s₀ + 2 * D.κ * D.s₀) +
        (-2 * D.κ * D.sc)) (y := -D.s₁) (by
        have e : (15 * η + 3 * η₁) * (1 / (1 - D.d)) + 2 * η + (-D.s₀ + 2 * D.κ * D.s₀) +
            (-2 * D.κ * D.sc) - -D.s₁ = (15 * η + 3 * η₁) * (1 / (1 - D.d)) + 2 * η - D.s₀ +
            2 * D.κ * D.s₀ - 2 * D.κ * D.sc + D.s₁ := by ring
        rw [e]; exact hbig1)
    rw [← rpow_mul_rpow hN0, ← rpow_mul_rpow hN0, ← rpow_mul_rpow hN0] at hb
    rw [hDinv, hgc2]
    have : 0 ≤ D.N ^ (-D.s₀ + 2 * D.κ * D.s₀) * D.N ^ (-2 * D.κ * D.sc) := by positivity
    calc 14 * Y * D.N ^ (-D.s₀ + 2 * D.κ * D.s₀) * (4 * D.K ^ 2 * D.N ^ (-2 * D.κ * D.sc))
        = 56 * Y * D.K ^ 2 * (D.N ^ (-D.s₀ + 2 * D.κ * D.s₀) * D.N ^ (-2 * D.κ * D.sc)) := by ring
      _ ≤ 56 * Y * D.N ^ (2 * η) * (D.N ^ (-D.s₀ + 2 * D.κ * D.s₀) * D.N ^ (-2 * D.κ * D.sc)) := by
          gcongr
      _ = (112 * (10 ^ 9 : ℝ) ^ (1 / (1 - D.d)) * (D.N ^ ((15 * η + 3 * η₁) * (1 / (1 - D.d))) *
            D.N ^ (2 * η) * D.N ^ (-D.s₀ + 2 * D.κ * D.s₀) * D.N ^ (-2 * D.κ * D.sc))) / 2 := by
          rw [hY]; ring
      _ ≤ D.N ^ (-D.s₁) / 2 := by gcongr
      _ = D.a₁ / 2 := rfl
  have T2 : D.a₁ * (4 * D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2) ≤ D.a₁ / 2 := by
    have hb : 4 * D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2 ≤ 1 / 2 := by
      rw [hgc2]
      have : D.N ^ (2 * η) * D.N ^ (-2 * D.κ * D.sc) = D.N ^ (2 * η - 2 * D.κ * D.sc) := by
        rw [rpow_mul_rpow hN0]; congr 1; ring
      have h2 : 4 * D.K ^ 2 * D.N ^ (-2 * D.κ * D.sc) ≤ 4 * D.N ^ (2 * η) * D.N ^ (-2 * D.κ * D.sc) := by
        gcongr
      linarith only [h2, this, hbig2]
    have := mul_le_mul_of_nonneg_left hb ha1.le
    linarith only [this]
  calc D.crossLip D.M D.Dw (D.N ^ η₁) (D.Bnat C₀) * D.cellδ2 (D.N ^ (-m))
      ≤ (14 * Y * (D.a₀ / D.Dw) + D.a₁) * (4 * D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2) :=
        mul_le_mul hLip' hδ hδ0 (by positivity)
    _ = 14 * Y * (D.a₀ / D.Dw) * (4 * D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2) +
          D.a₁ * (4 * D.K ^ 2 * (D.N ^ (-D.κ * D.sc)) ^ 2) := by ring
    _ ≤ D.a₁ / 2 + D.a₁ / 2 := add_le_add T1 T2
    _ = D.a₁ := by ring

end

end Submission.Obl.k4_horizontal_supercritical_rate_candidates.Return
