import Mathlib

namespace Submission.Obl.k4_scalar_guarded_tangent_preparation

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- A fixed small uniform blur of a reference velocity-bin center. -/
def scatterKernel (δ center : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Icc (center - 2 * δ) (center + 2 * δ))

theorem scatterKernel_probability {δ : ℝ} (hδ : 0 < δ) (center : ℝ) :
    IsProbabilityMeasure (scatterKernel δ center) := by
  have hvol : volume (Icc (center - 2 * δ) (center + 2 * δ)) = ENNReal.ofReal (4 * δ) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [hvol]
    exact (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  · rw [hvol]
    exact ENNReal.ofReal_ne_top

/-- A reference palette blurred once, before the likelihood restriction.
The original finite velocity-bin probabilities remain its mixture weights. -/
def scatterPalette {ι : Type*} [Fintype ι] (p : ι → ℝ) (center : ι → ℝ) (δ : ℝ) : Measure ℝ :=
  ∑ i, ENNReal.ofReal (p i) • scatterKernel δ (center i)

theorem scatterPalette_probability {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (center : ι → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    IsProbabilityMeasure (scatterPalette p center δ) := by
  letI (i : ι) : IsProbabilityMeasure (scatterKernel δ (center i)) := scatterKernel_probability hδ _
  constructor
  simp only [scatterPalette, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hp i), hp1, ENNReal.ofReal_one]

/-- A coarse interval meeting a fine velocity cell contains at least a
quarter of the cell center's fixed blur. -/
theorem scatterKernel_interval_lower {δ center a b : ℝ} (hδ : 0 < δ)
    (hlength : 2 * δ ≤ b - a) (hleft : a - δ ≤ center) (hright : center ≤ b + δ) :
    ENNReal.ofReal (1 / 4 : ℝ) ≤ scatterKernel δ center (Icc a b) := by
  have hlow : max (center - 2 * δ) a + δ ≤ min (center + 2 * δ) b := by
    apply le_min
    · rw [← max_add_add_right]
      apply max_le <;> linarith
    · rw [← max_add_add_right]
      apply max_le <;> linarith
  have hmass : ENNReal.ofReal δ ≤
      volume (Icc (center - 2 * δ) (center + 2 * δ) ∩ Icc a b) := by
    rw [Set.Icc_inter_Icc, Real.volume_Icc]
    apply ENNReal.ofReal_le_ofReal
    linarith
  have hvol : volume (Icc (center - 2 * δ) (center + 2 * δ)) = ENNReal.ofReal (4 * δ) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  rw [scatterKernel, ProbabilityTheory.cond_apply measurableSet_Icc, hvol]
  have hfour : ENNReal.ofReal (4 * δ) ≠ 0 := (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hprod : ENNReal.ofReal (4 * δ) * ENNReal.ofReal (1 / 4 : ℝ) = ENNReal.ofReal δ := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  calc
    ENNReal.ofReal (1 / 4 : ℝ) = (ENNReal.ofReal (4 * δ))⁻¹ * ENNReal.ofReal δ := by
      rw [← hprod, ← mul_assoc, ENNReal.inv_mul_cancel hfour ENNReal.ofReal_ne_top, one_mul]
    _ ≤ _ := mul_le_mul le_rfl hmass bot_le bot_le

/-- The blurred palette dominates all old fine-cell probabilities whose
centers can meet the requested coarse interval, even at bin boundaries. -/
theorem scatterPalette_interval_lower {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (center : ι → ℝ) {δ a b : ℝ}
    (hδ : 0 < δ) (hlength : 2 * δ ≤ b - a) (s : Finset ι)
    (hs : ∀ i ∈ s, a - δ ≤ center i ∧ center i ≤ b + δ) :
    ENNReal.ofReal (1 / 4 : ℝ) * (∑ i ∈ s, ENNReal.ofReal (p i)) ≤
      scatterPalette p center δ (Icc a b) := by
  rw [Finset.mul_sum]
  calc
    (∑ i ∈ s, ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal (p i)) ≤
        ∑ i ∈ s, ENNReal.ofReal (p i) * scatterKernel δ (center i) (Icc a b) := by
      apply Finset.sum_le_sum
      intro i hi
      have hbound := scatterKernel_interval_lower hδ hlength (hs i hi).1 (hs i hi).2
      simpa only [mul_comm] using (mul_le_mul le_rfl hbound bot_le bot_le :
        ENNReal.ofReal (p i) * ENNReal.ofReal (1 / 4 : ℝ) ≤ _)
    _ ≤ ∑ i, ENNReal.ofReal (p i) * scatterKernel δ (center i) (Icc a b) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => bot_le)
    _ = scatterPalette p center δ (Icc a b) := by
      simp only [scatterPalette, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul]

theorem scatterKernel_singleton (δ center x : ℝ) : scatterKernel δ center {x} = 0 := by
  have hac : scatterKernel δ center ≪ (volume : Measure ℝ) :=
    ProbabilityTheory.cond_absolutelyContinuous
  exact hac (by simp)

theorem scatterPalette_singleton {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (center : ι → ℝ) (δ x : ℝ) : scatterPalette p center δ {x} = 0 := by
  simp only [scatterPalette, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    scatterKernel_singleton, mul_zero, Finset.sum_const_zero]

theorem scatterPalette_Ico_eq_Icc {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (center : ι → ℝ) (δ a b : ℝ) :
    scatterPalette p center δ (Ico a b) = scatterPalette p center δ (Icc a b) := by
  have hset : Icc a b \ {b} = Ico a b := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_singleton_iff, Set.mem_Ico]
    constructor
    · rintro ⟨⟨ha, hb⟩, hne⟩
      exact ⟨ha, lt_of_le_of_ne hb hne⟩
    · rintro ⟨ha, hb⟩
      exact ⟨⟨ha, hb.le⟩, hb.ne⟩
  simpa only [hset] using
    (measure_sdiff_null (s := Icc a b) (scatterPalette_singleton p center δ b))

/-- Smoothing preserves interval caps by charging only old palette
centers in the bounded enlargement of the tested interval. -/
theorem scatterPalette_interval_upper {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (center : ι → ℝ) {δ : ℝ} (hδ : 0 < δ) (a b : ℝ) :
    scatterPalette p center δ (Icc a b) ≤
      ∑ i ∈ Finset.univ.filter (fun i => center i ∈ Icc (a - 2 * δ) (b + 2 * δ)),
        ENNReal.ofReal (p i) := by
  classical
  simp only [scatterPalette, Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul,
    Finset.sum_filter]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : center i ∈ Icc (a - 2 * δ) (b + 2 * δ)
  · rw [ite_eq_left hi]
    letI : IsProbabilityMeasure (scatterKernel δ (center i)) := scatterKernel_probability hδ _
    simpa only [mul_one] using (mul_le_mul le_rfl (prob_le_one (μ := scatterKernel δ (center i))
      (s := Icc a b)) bot_le bot_le :
        ENNReal.ofReal (p i) * scatterKernel δ (center i) (Icc a b) ≤ ENNReal.ofReal (p i) * 1)
  · rw [ite_eq_right hi]
    have hempty : Icc (center i - 2 * δ) (center i + 2 * δ) ∩ Icc a b = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hi
      exact ⟨by linarith [hx.1.2, hx.2.1], by linarith [hx.1.1, hx.2.2]⟩
    rw [scatterKernel, ProbabilityTheory.cond_apply measurableSet_Icc, hempty, measure_empty,
      mul_zero, mul_zero]

theorem old_palette_cells_le_four_smoothed {ι : Type*} [Fintype ι]
    (p : ι → ℝ) (center : ι → ℝ) {δ a b : ℝ}
    (hδ : 0 < δ) (hlength : 2 * δ ≤ b - a) (s : Finset ι)
    (hs : ∀ i ∈ s, a - δ ≤ center i ∧ center i ≤ b + δ) :
    (∑ i ∈ s, ENNReal.ofReal (p i)) ≤ 4 * scatterPalette p center δ (Ico a b) := by
  rw [scatterPalette_Ico_eq_Icc]
  have hlower := scatterPalette_interval_lower p center hδ hlength s hs
  calc
    (∑ i ∈ s, ENNReal.ofReal (p i)) =
        4 * (ENNReal.ofReal (1 / 4 : ℝ) * ∑ i ∈ s, ENNReal.ofReal (p i)) := by
      have hquarter : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 4 : ℝ) = 1 := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
          ← ENNReal.ofReal_mul (by norm_num)]
        norm_num
      rw [← mul_assoc, hquarter, one_mul]
    _ ≤ _ := mul_le_mul le_rfl hlower bot_le bot_le

end

end Submission.Obl.k4_scalar_guarded_tangent_preparation
