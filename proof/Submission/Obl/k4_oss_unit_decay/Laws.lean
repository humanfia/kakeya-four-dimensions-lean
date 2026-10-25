import Submission.Obl.k4_oss_unit_decay.Defs

open MeasureTheory Set Filter
open scoped ENNReal

namespace Submission.Obl.k4_oss_unit_decay

scoped instance mix_probability (α β : Measure ℝ) [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] : IsProbabilityMeasure (mix α β) := by
  unfold mix
  infer_instance

scoped instance halfLaw_probability (α : Measure ℝ) [IsProbabilityMeasure α] :
    IsProbabilityMeasure (halfLaw α) := by
  unfold halfLaw
  infer_instance

lemma halfLaw_support {α : Measure ℝ} (hα : α (Icc (1 : ℝ) 2)ᶜ = 0) :
    halfLaw α (Icc (-1 : ℝ) 1)ᶜ = 0 := by
  rw [halfLaw, Measure.map_apply (by fun_prop) measurableSet_Icc.compl]
  apply measure_mono_null _ hα
  intro x hx
  simp only [mem_preimage, mem_compl_iff, mem_Icc] at hx ⊢
  intro h
  exact hx ⟨by linarith [h.1], by linarith [h.2]⟩

lemma mix_support {α β : Measure ℝ} [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] (hα : α (Icc (-1 : ℝ) 1)ᶜ = 0)
    (hβ : β (Icc (1 : ℝ) 2)ᶜ = 0) :
    mix α β (Icc (-1 : ℝ) 1)ᶜ = 0 := by
  have ha : ∀ᵐ x ∂α, x ∈ Icc (-1 : ℝ) 1 := by exact hα
  have hb : ∀ᵐ y ∂β, y ∈ Icc (1 : ℝ) 2 := by exact hβ
  have hab : ∀ᵐ p ∂α.prod β, p.1 ∈ Icc (-1 : ℝ) 1 ∧ p.2 ∈ Icc (1 : ℝ) 2 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [ha] with x hx
    filter_upwards [hb] with y hy
    exact ⟨hx, hy⟩
  have habab : ∀ᵐ q ∂(α.prod β).prod (α.prod β),
      (q.1.1 ∈ Icc (-1 : ℝ) 1 ∧ q.1.2 ∈ Icc (1 : ℝ) 2) ∧
      (q.2.1 ∈ Icc (-1 : ℝ) 1 ∧ q.2.2 ∈ Icc (1 : ℝ) 2) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).2
    filter_upwards [hab] with p hp
    filter_upwards [hab] with q hq
    exact ⟨hp, hq⟩
  change ∀ᵐ z ∂mix α β, z ∈ Icc (-1 : ℝ) 1
  rw [mix]
  apply (ae_map_iff (by fun_prop) (show MeasurableSet {z : ℝ | z ∈ Icc (-1 : ℝ) 1}
    from measurableSet_Icc)).2
  filter_upwards [habab] with q hq
  rcases hq with ⟨⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩⟩, ⟨⟨hc₁, hc₂⟩, ⟨hd₁, hd₂⟩⟩⟩
  have hxy : -2 ≤ q.1.1 * q.1.2 ∧ q.1.1 * q.1.2 ≤ 2 := by
    constructor <;> nlinarith
  have hzw : -2 ≤ q.2.1 * q.2.2 ∧ q.2.1 * q.2.2 ≤ 2 := by
    constructor <;> nlinarith
  constructor <;> linarith

lemma intervalCap_of_frostman {α : Measure ℝ} [IsProbabilityMeasure α]
    {δ s A : ℝ} (hA : 1 ≤ A) (hs : 0 ≤ s)
    (h : ∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      α (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (A * u ^ s)) :
    IntervalCap α δ s A := by
  intro x u hu
  by_cases hu1 : u ≤ 1
  · exact h x u hu hu1
  · have hp : 1 ≤ u ^ s := Real.one_le_rpow (le_of_not_ge hu1) hs
    have hprod : 1 ≤ A * u ^ s := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hp)]
    exact (prob_le_one).trans (by simpa using ENNReal.ofReal_le_ofReal hprod)

lemma IntervalCap.mono {α : Measure ℝ} {δ s A B : ℝ} (h : IntervalCap α δ s A)
    (hδ : 0 < δ) (hAB : A ≤ B) : IntervalCap α δ s B := by
  intro x u hu
  exact (h x u hu).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (le_trans hδ.le hu) _)))

lemma intervalCap_halfLaw {α : Measure ℝ} {δ s A : ℝ}
    (hδ : 0 < δ) (hs : s ≤ 1) (hA : 0 ≤ A) (h : IntervalCap α δ s A) :
    IntervalCap (halfLaw α) δ s (2 * A) := by
  intro x u hu
  have hu0 : 0 ≤ u := (hδ.le.trans hu)
  rw [halfLaw, Measure.map_apply (by fun_prop) measurableSet_Icc]
  calc
    α ((fun z : ℝ => z / 2) ⁻¹' Icc (x - u) (x + u))
        ≤ α (Icc (2 * x - 2 * u) (2 * x + 2 * u)) := by
          apply measure_mono
          intro z hz
          simp only [mem_preimage, mem_Icc] at hz ⊢
          constructor <;> linarith
    _ ≤ ENNReal.ofReal (A * (2 * u) ^ s) := h _ _ (by linarith)
    _ ≤ ENNReal.ofReal ((2 * A) * u ^ s) := by
      apply ENNReal.ofReal_le_ofReal
      rw [Real.mul_rpow (by norm_num) hu0]
      have h2 : (2 : ℝ) ^ s ≤ 2 := by
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs
      nlinarith [Real.rpow_nonneg hu0 s,
        mul_le_mul_of_nonneg_left h2 hA]

lemma intervalCap_mix {α β : Measure ℝ} [IsProbabilityMeasure α]
    [IsProbabilityMeasure β] {δ s A : ℝ} (hδ : 0 < δ) (hs : s ≤ 1) (hA : 0 ≤ A)
    (h : IntervalCap α δ s A) (hβ : β (Icc (1 : ℝ) 2)ᶜ = 0) :
    IntervalCap (mix α β) δ s (4 * A) := by
  intro x u hu
  have hu0 : 0 ≤ u := hδ.le.trans hu
  have hb : ∀ᵐ y ∂β, 1 ≤ y := by
    have hh : ∀ᵐ y ∂β, y ∈ Icc (1 : ℝ) 2 := by exact hβ
    exact hh.mono fun _ hy => hy.1
  rw [mix, Measure.map_apply (by fun_prop) measurableSet_Icc]
  rw [Measure.prod_apply_symm (by measurability)]
  calc
    (∫⁻ q : ℝ × ℝ, (α.prod β)
        ((fun p : ℝ × ℝ => (p, q)) ⁻¹'
          ((fun q : (ℝ × ℝ) × (ℝ × ℝ) =>
            (q.1.1 * q.1.2 - q.2.1 * q.2.2) / 4) ⁻¹' Icc (x - u) (x + u)))
        ∂(α.prod β)) ≤ ∫⁻ _q : ℝ × ℝ, ENNReal.ofReal ((4 * A) * u ^ s)
          ∂(α.prod β) := by
      apply lintegral_mono
      intro q
      dsimp only
      rw [Measure.prod_apply_symm (by measurability)]
      calc
        _ ≤ ∫⁻ _y : ℝ, ENNReal.ofReal ((4 * A) * u ^ s) ∂β := by
          apply lintegral_mono_ae
          filter_upwards [hb] with y hy
          calc
            _ ≤ α (Icc ((4 * x + q.1 * q.2) / y - 4 * u)
                ((4 * x + q.1 * q.2) / y + 4 * u)) := by
              apply measure_mono
              intro z hz
              simp only [mem_preimage, mem_Icc] at hz ⊢
              have hy0 : 0 < y := lt_of_lt_of_le (by norm_num) hy
              constructor
              · rw [sub_le_iff_le_add, div_le_iff₀ hy0]
                nlinarith [mul_nonneg (sub_nonneg.mpr hy) hu0]
              · rw [← sub_le_iff_le_add, le_div_iff₀ hy0]
                nlinarith [mul_nonneg (sub_nonneg.mpr hy) hu0]
            _ ≤ ENNReal.ofReal (A * (4 * u) ^ s) := h _ _ (by linarith)
            _ ≤ ENNReal.ofReal ((4 * A) * u ^ s) := by
              apply ENNReal.ofReal_le_ofReal
              rw [Real.mul_rpow (by norm_num) hu0]
              have h4 : (4 : ℝ) ^ s ≤ 4 := by
                simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hs
              nlinarith [Real.rpow_nonneg hu0 s,
                mul_le_mul_of_nonneg_left h4 hA]
        _ = _ := by simp
    _ = ENNReal.ofReal ((4 * A) * u ^ s) := by simp

lemma IntervalCap.change_scale {α : Measure ℝ} {δ d s A C : ℝ}
    (h : IntervalCap α δ s A) (hd : 0 < d) (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hC : 1 ≤ C) (hscale : δ ≤ C * d) :
    IntervalCap α d s (A * C ^ s) := by
  intro x u hu
  have hu0 : 0 ≤ u := hd.le.trans hu
  have hCu : u ≤ C * u := by nlinarith
  have hδCu : δ ≤ C * u := hscale.trans
    (mul_le_mul_of_nonneg_left hu (by linarith))
  have hv : max δ u ≤ C * u := max_le hδCu hCu
  calc
    α (Icc (x - u) (x + u)) ≤ α (Icc (x - max δ u) (x + max δ u)) := by
      apply measure_mono
      exact Icc_subset_Icc (by linarith [le_max_right δ u])
        (by linarith [le_max_right δ u])
    _ ≤ ENNReal.ofReal (A * (max δ u) ^ s) := h _ _ (le_max_left _ _)
    _ ≤ ENNReal.ofReal ((A * C ^ s) * u ^ s) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        A * (max δ u) ^ s ≤ A * (C * u) ^ s :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hu0.trans (le_max_right _ _)) hv hs) hA
        _ = _ := by rw [Real.mul_rpow (by linarith) hu0]; ring

end Submission.Obl.k4_oss_unit_decay
