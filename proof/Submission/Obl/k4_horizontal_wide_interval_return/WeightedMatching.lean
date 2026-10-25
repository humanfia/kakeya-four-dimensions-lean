import Submission.Lib.K4QuadSheetMatching.Matching

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set
open Submission.Lib.K4QuadSheetMatching
open scoped ENNReal

noncomputable section

/-- Matching with separate reference weights in the two colors. In particular,
different layer thicknesses stay in their own reference measures. -/
theorem weighted_quad_matching (hTC : TwoColorStatement) {d₀ : ℝ}
    (hd₀ : 0 ≤ d₀) (hd₁ : d₀ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧
    ∀ R M ε : ℝ, R₀ ≤ R → 0 < M → 0 < ε → ε ≤ ε₀ →
    ∀ (n₁ n₂ : ℕ) (c₀ : Fin 6 → ℝ)
      (c₁ : Fin n₁ → Fin 6 → ℝ) (c₂ : Fin n₂ → Fin 6 → ℝ)
      (w₁ : Fin n₁ → ℝ) (w₂ : Fin n₂ → ℝ) (K : ℝ)
      (ρ : Fin n₁ × Fin n₂ → Measure (ℝ × ℝ)),
      (∀ i, IsFiniteMeasure (ρ i)) →
      (∀ i, 0 ≤ w₁ i) → (∀ i, 0 ≤ w₂ i) →
      0 < ∑ i, w₁ i → 0 < ∑ i, w₂ i → 0 ≤ K →
      (n₁ : ℝ) ≤ R ^ (d₀ + ε) → (n₂ : ℝ) ≤ R ^ (d₀ + ε) →
      (∀ i, ∀ z ∈ unitSq, |qev (c₁ i) z.1 z.2 - qev c₀ z.1 z.2| ≤ M * R ^ ε) →
      (∀ i, ∀ z ∈ unitSq, |qev (c₂ i) z.1 z.2 - qev c₀ z.1 z.2| ≤ M * R ^ ε) →
      (∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
        ∑ j, ρ (i, j) B ≤ ENNReal.ofReal (K * w₁ i) * volume B) →
      (∀ j (B : Set (ℝ × ℝ)), MeasurableSet B →
        ∑ i, ρ (i, j) B ≤ ENNReal.ofReal (K * w₂ j) * volume B) →
      (∀ i, ∀ᵐ z ∂ρ i, z ∈ unitSq ∧
        |qev (c₁ i.1) z.1 z.2 - qev (c₂ i.2) z.1 z.2| ≤ M * R ^ (-1 + ε) ∧
        ∃ z' ∈ unitSq,
          M * R ^ (-ε) ≤ |qev (c₁ i.1) z'.1 z'.2 - qev (c₂ i.2) z'.1 z'.2|) →
      ∑ i, ρ i univ ≤
        ENNReal.ofReal (K * max (∑ i, w₁ i) (∑ i, w₂ i) * R ^ (-ε)) := by
  classical
  obtain ⟨ε₀, hε₀, R₀, hR₀, hmain⟩ := quad_sheet_matching hTC hd₀ hd₁
  refine ⟨ε₀, hε₀, R₀, hR₀, ?_⟩
  intro R M ε hR hM hε hεle n₁ n₂ c₀ c₁ c₂ w₁ w₂ K ρ hρfin
    hw₁ hw₂ hW₁ hW₂ hK hn₁ hn₂ hc₁ hc₂ hm₁ hm₂ hgood
  letI : ∀ i, IsFiniteMeasure (ρ i) := hρfin
  have hRpos : 0 < R := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hp (a b : ℝ) (h : a ≤ b) : R ^ a ≤ R ^ b :=
    Real.rpow_le_rpow_of_exponent_le hR1 h
  by_contra hbad
  have hlt : ENNReal.ofReal (K * max (∑ i, w₁ i) (∑ i, w₂ i) * R ^ (-ε)) <
      ∑ i, ρ i univ := lt_of_not_ge hbad
  let mass : ℝ≥0∞ := ∑ i, ρ i univ
  have hmassTop : mass ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => measure_ne_top _ _)
  have hmass0 : mass ≠ 0 := ne_of_gt (lt_of_le_of_lt bot_le hlt)
  let mr : ℝ := mass.toReal
  have hmr : 0 < mr := ENNReal.toReal_pos hmass0 hmassTop
  have hmreq : mass = ENNReal.ofReal mr := (ENNReal.ofReal_toReal hmassTop).symm
  have hlt' : K * max (∑ i, w₁ i) (∑ i, w₂ i) * R ^ (-ε) < mr := by
    change ENNReal.ofReal _ < mass at hlt
    rw [hmreq] at hlt
    exact (ENNReal.ofReal_lt_ofReal_iff hmr).mp hlt
  have hweight {W w : ℝ} (hW : 0 < W) (hw : 0 ≤ w)
      (hWmax : W ≤ max (∑ i, w₁ i) (∑ i, w₂ i)) :
      mass⁻¹ * ENNReal.ofReal (K * w) ≤ ENNReal.ofReal (R ^ ε₀ * (w / W)) := by
    have hKW : K * W * R ^ (-ε) < mr :=
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWmax hK)
        (Real.rpow_nonneg hRpos.le _)).trans_lt hlt'
    have hbound : K * w ≤ mr * (R ^ ε * (w / W)) := by
      have heq : K * w = (K * W * R ^ (-ε)) * (R ^ ε * (w / W)) := by
        rw [Real.rpow_neg hRpos.le]
        field_simp
      rw [heq]
      exact mul_le_mul_of_nonneg_right hKW.le (by positivity)
    calc mass⁻¹ * ENNReal.ofReal (K * w)
        ≤ mass⁻¹ * ENNReal.ofReal (mr * (R ^ ε * (w / W))) := by
          gcongr
      _ = mass⁻¹ * (mass * ENNReal.ofReal (R ^ ε * (w / W))) := by
          rw [ENNReal.ofReal_mul hmr.le, ← hmreq]
      _ = ENNReal.ofReal (R ^ ε * (w / W)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hmass0 hmassTop, one_mul]
      _ ≤ ENNReal.ofReal (R ^ ε₀ * (w / W)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (hp _ _ hεle) (by positivity))
  let ρn : Fin n₁ × Fin n₂ → Measure (ℝ × ℝ) := fun i => mass⁻¹ • ρ i
  have hρnfin : ∀ i, IsFiniteMeasure (ρn i) := by
    intro i
    constructor
    simp only [ρn, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hmass0))
      (measure_lt_top _ _)
  have htotal : ∑ i, ρn i univ = 1 := by
    simp only [ρn, Measure.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    exact ENNReal.inv_mul_cancel hmass0 hmassTop
  let e₁ : Fin n₁ → Fin 6 → ℝ := fun i => M⁻¹ • (c₁ i - c₀)
  let e₂ : Fin n₂ → Fin 6 → ℝ := fun i => M⁻¹ • (c₂ i - c₀)
  have hqe (c : Fin 6 → ℝ) (t y : ℝ) :
      qev (M⁻¹ • (c - c₀)) t y = (qev c t y - qev c₀ t y) / M := by
    simp only [qev, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    field_simp
    ring
  have hdiff (i : Fin n₁) (j : Fin n₂) (t y : ℝ) :
      qev (e₁ i) t y - qev (e₂ j) t y =
        (qev (c₁ i) t y - qev (c₂ j) t y) / M := by
    simp only [e₁, e₂, hqe]
    ring
  apply hmain R hR n₁ n₂ e₁ e₂ (fun i => w₁ i / ∑ i, w₁ i)
    (fun i => w₂ i / ∑ i, w₂ i) ρn hρnfin
    (hn₁.trans (hp _ _ (by linarith))) (hn₂.trans (hp _ _ (by linarith)))
  · intro i z hz
    rw [hqe, abs_div, abs_of_pos hM, div_le_iff₀ hM]
    exact (hc₁ i z hz).trans
      ((mul_le_mul_of_nonneg_left (hp _ _ hεle) hM.le).trans_eq (mul_comm _ _))
  · intro i z hz
    rw [hqe, abs_div, abs_of_pos hM, div_le_iff₀ hM]
    exact (hc₂ i z hz).trans
      ((mul_le_mul_of_nonneg_left (hp _ _ hεle) hM.le).trans_eq (mul_comm _ _))
  · intro i; exact div_nonneg (hw₁ i) hW₁.le
  · intro i; exact div_nonneg (hw₂ i) hW₂.le
  · rw [← Finset.sum_div, div_self hW₁.ne']
  · rw [← Finset.sum_div, div_self hW₂.ne']
  · intro i B hB
    simp only [ρn, Measure.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    calc mass⁻¹ * ∑ j, ρ (i, j) B
        ≤ mass⁻¹ * (ENNReal.ofReal (K * w₁ i) * volume B) := by gcongr; exact hm₁ i B hB
      _ = (mass⁻¹ * ENNReal.ofReal (K * w₁ i)) * volume B := by ring
      _ ≤ ENNReal.ofReal (R ^ ε₀ * (w₁ i / ∑ i, w₁ i)) * volume B :=
          mul_le_mul' (hweight hW₁ (hw₁ i) (le_max_left _ _)) le_rfl
  · intro j B hB
    simp only [ρn, Measure.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum]
    calc mass⁻¹ * ∑ i, ρ (i, j) B
        ≤ mass⁻¹ * (ENNReal.ofReal (K * w₂ j) * volume B) := by gcongr; exact hm₂ j B hB
      _ = (mass⁻¹ * ENNReal.ofReal (K * w₂ j)) * volume B := by ring
      _ ≤ ENNReal.ofReal (R ^ ε₀ * (w₂ j / ∑ i, w₂ i)) * volume B :=
          mul_le_mul' (hweight hW₂ (hw₂ j) (le_max_right _ _)) le_rfl
  · rw [htotal]
    exact_mod_cast Real.rpow_le_one_of_one_le_of_nonpos hR1 (by linarith : -ε₀ ≤ 0)
  · intro i
    have hg : ∀ᵐ z ∂ρ i, z ∈ unitSq ∧
        |qev (e₁ i.1) z.1 z.2 - qev (e₂ i.2) z.1 z.2| ≤ R ^ (-1 + ε₀) ∧
        ∃ z' ∈ unitSq,
          R ^ (-ε₀) ≤ |qev (e₁ i.1) z'.1 z'.2 - qev (e₂ i.2) z'.1 z'.2| := by
      filter_upwards [hgood i] with z hz
      refine ⟨hz.1, ?_, ?_⟩
      · rw [hdiff, abs_div, abs_of_pos hM, div_le_iff₀ hM]
        exact hz.2.1.trans
          ((mul_le_mul_of_nonneg_left (hp _ _ (by linarith)) hM.le).trans_eq (mul_comm _ _))
      · obtain ⟨z', hz', hfar⟩ := hz.2.2
        refine ⟨z', hz', ?_⟩
        rw [hdiff, abs_div, abs_of_pos hM, le_div_iff₀ hM]
        exact ((mul_le_mul_of_nonneg_right (hp _ _ (by linarith)) hM.le).trans_eq
          (mul_comm _ _)).trans hfar
    rw [ae_iff] at hg ⊢
    simp only [ρn, Measure.smul_apply, smul_eq_mul, hg, mul_zero]

end

end Submission.Obl.k4_horizontal_wide_interval_return
