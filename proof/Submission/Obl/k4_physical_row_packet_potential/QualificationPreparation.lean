import Submission.Lib.K4HighRetention
import Submission.Obl.k4_scalar_grid_cartesian_field.MassRatio

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential

open Set MeasureTheory
open Submission.Lib.K4StateFractionKeep
open scoped ENNReal

/-- Remove entire states with more than one percent unqualified mass. The
pointwise qualified subset is measurable even when the qualification event is
an arbitrary existential set. Relative to the original finite law the state
cut retains at least half the mass. -/
theorem qualified_state_preparation {Ω σ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace σ] [Countable σ] [MeasurableSingletonClass σ]
    (μ : Measure Ω) [IsFiniteMeasure μ] (Se : Set Ω) (hSe : MeasurableSet Se)
    (hconc : μ Seᶜ = 0) (st : Ω → σ) (hst : Measurable st)
    (Qual : Set Ω) (hbad : μ Qualᶜ ≤ (1 / 10000 : ℝ≥0∞) * μ univ) :
    ∃ E0 Q : Set Ω,
      MeasurableSet E0 ∧ MeasurableSet Q ∧ E0 ⊆ Se ∧ Q ⊆ E0 ∩ Qual ∧
      (∀ x ∈ Se, ∀ y ∈ E0, st x = st y → x ∈ E0) ∧
      (1 / 2 : ℝ≥0∞) * μ univ ≤ μ E0 ∧
      μ (Se \ E0) ≤ (1 / 100 : ℝ≥0∞) * μ univ ∧
      (∀ k, (μ.restrict E0) (st ⁻¹' {k} \ Q) ≤
        (1 / 100 : ℝ≥0∞) * (μ.restrict E0) (st ⁻¹' {k})) := by
  classical
  let R : Set Ω := (toMeasurable μ Qualᶜ)ᶜ
  have hRm : MeasurableSet R := (measurableSet_toMeasurable μ Qualᶜ).compl
  have hRQual : R ⊆ Qual := by
    intro x hx
    by_contra hxQ
    exact hx (subset_toMeasurable μ Qualᶜ hxQ)
  have hRbad : μ Rᶜ = μ Qualᶜ := by
    simp only [R, compl_compl, measure_toMeasurable]
  let Good : Set σ := goodStates μ st R (ENNReal.ofReal (99 / 100 : ℝ))
  let E0 : Set Ω := Se ∩ st ⁻¹' Good
  let Q : Set Ω := E0 ∩ R
  have hGood : MeasurableSet (st ⁻¹' Good) := hst (to_countable Good).measurableSet
  have hE0 : MeasurableSet E0 := hSe.inter hGood
  have hQ : MeasurableSet Q := hE0.inter hRm
  have hE0sub : E0 ⊆ Se := inter_subset_left
  have hkeep : fractionKeep μ st R (ENNReal.ofReal (99 / 100 : ℝ)) ⊆ st ⁻¹' Good :=
    inter_subset_right
  have hstateLoss : μ (st ⁻¹' Good)ᶜ ≤ (1 / 100 : ℝ≥0∞) * μ univ := by
    have h := Submission.Lib.K4HighRetention.StateRetention.measure_compl_fractionKeep_le
      μ st hst R hRm (f := (99 / 100 : ℝ)) (by norm_num) (by norm_num)
    have hnum : ENNReal.ofReal (1 / (1 - (99 / 100 : ℝ))) = (100 : ℝ≥0∞) := by norm_num
    rw [hnum, hRbad] at h
    calc
      _ ≤ μ (fractionKeep μ st R (ENNReal.ofReal (99 / 100 : ℝ)))ᶜ :=
        measure_mono (compl_subset_compl.mpr hkeep)
      _ ≤ 100 * μ Qualᶜ := h
      _ ≤ 100 * ((1 / 10000 : ℝ≥0∞) * μ univ) := mul_le_mul' le_rfl hbad
      _ = _ := by
        have hcoef : (100 : ℝ≥0∞) * (1 / 10000 : ℝ≥0∞) = (1 / 100 : ℝ≥0∞) := by
          calc
            _ = ENNReal.ofReal (100 : ℝ) * ENNReal.ofReal (1 / 10000 : ℝ) := by
              congr 1 <;> norm_num [ENNReal.ofReal_div_of_pos]
            _ = ENNReal.ofReal ((100 : ℝ) * (1 / 10000 : ℝ)) :=
              (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 100)).symm
            _ = _ := by norm_num [ENNReal.ofReal_div_of_pos]
        rw [← mul_assoc, hcoef]
  have hE0Loss : μ (Se \ E0) ≤ (1 / 100 : ℝ≥0∞) * μ univ := by
    apply (measure_mono ?_).trans hstateLoss
    rintro x ⟨hxSe, hxE0⟩ hxGood
    exact hxE0 ⟨hxSe, hxGood⟩
  have hE0compl : μ E0ᶜ ≤ (1 / 100 : ℝ≥0∞) * μ univ := by
    calc
      _ ≤ μ (Seᶜ ∪ (st ⁻¹' Good)ᶜ) := measure_mono (by
        intro x hx
        by_cases hxs : x ∈ Se
        · exact Or.inr (fun hxg => hx ⟨hxs, hxg⟩)
        · exact Or.inl hxs)
      _ ≤ μ Seᶜ + μ (st ⁻¹' Good)ᶜ := measure_union_le _ _
      _ ≤ 0 + (1 / 100 : ℝ≥0∞) * μ univ := add_le_add (le_of_eq hconc) hstateLoss
      _ = _ := zero_add _
  have hhalf : (1 / 2 : ℝ≥0∞) * μ univ ≤ μ E0 := by
    have hcover : μ univ ≤ μ E0 + μ E0ᶜ :=
      le_of_eq (measure_add_measure_compl hE0).symm
    have hquarter : (1 / 100 : ℝ≥0∞) ≤ ENNReal.ofReal (1 / 4 : ℝ) := by
      norm_num [ENNReal.ofReal_div_of_pos]
    have hh := Submission.Obl.k4_scalar_grid_cartesian_field.half_mass_of_quarter_bad
      (measure_ne_top μ univ) (measure_mono (subset_univ E0))
      (measure_mono (subset_univ E0ᶜ)) hcover
      (hE0compl.trans (mul_le_mul' hquarter le_rfl))
    simpa only [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using hh
  refine ⟨E0, Q, hE0, hQ, hE0sub, ?_, ?_, hhalf, hE0Loss, ?_⟩
  · rintro x ⟨hxE0, hxR⟩
    exact ⟨hxE0, hRQual hxR⟩
  · intro x hxSe y hyE0 hxy
    refine ⟨hxSe, ?_⟩
    have hy : st y ∈ Good := hyE0.2
    change st x ∈ Good
    rwa [hxy]
  · intro k
    have hfiber : MeasurableSet (st ⁻¹' {k}) := hst (measurableSet_singleton k)
    by_cases hk : k ∈ Good
    · have hRet : ENNReal.ofReal (99 / 100 : ℝ) * μ (st ⁻¹' {k}) ≤
          μ (R ∩ st ⁻¹' {k}) := hk
      have hbadCell : μ ((st ⁻¹' {k}) \ R) ≤
          (1 / 100 : ℝ≥0∞) * μ (st ⁻¹' {k}) := by
        have hr := ENNReal.toReal_mono (measure_ne_top μ _) hRet
        norm_num [ENNReal.toReal_mul] at hr
        have hsplit := measureReal_inter_add_sdiff (μ := μ) (s := st ⁻¹' {k}) hRm
        rw [inter_comm] at hsplit
        have hh : μ.real ((st ⁻¹' {k}) \ R) ≤ (1 / 100 : ℝ) * μ.real (st ⁻¹' {k}) := by
          change (99 / 100 : ℝ) * μ.real (st ⁻¹' {k}) ≤ μ.real (R ∩ st ⁻¹' {k}) at hr
          linarith
        have h := ENNReal.ofReal_le_ofReal hh
        simpa only [measureReal_def, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 100),
          ENNReal.ofReal_toReal (measure_ne_top μ _),
          ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 100),
          ENNReal.ofReal_one, ENNReal.ofReal_ofNat] using h
      have hden : (μ.restrict E0) (st ⁻¹' {k}) = μ (st ⁻¹' {k}) := by
        rw [Measure.restrict_apply hfiber]
        have heq : (st ⁻¹' {k}) ∩ E0 = (st ⁻¹' {k}) ∩ Se := by
          ext x
          constructor
          · exact fun hx => ⟨hx.1, hx.2.1⟩
          · intro hx
            refine ⟨hx.1, hx.2, ?_⟩
            change st x ∈ Good
            have hxk : st x = k := hx.1
            rwa [hxk]
        rw [heq]
        exact measure_inter_conull hconc
      rw [hden]
      rw [Measure.restrict_apply' hE0]
      exact (measure_mono (by
        rintro x ⟨hxBad, hxE0⟩
        refine ⟨hxBad.1, ?_⟩
        intro hxR
        exact hxBad.2 ⟨hxE0, hxR⟩)).trans hbadCell
    · have heq : st ⁻¹' {k} ∩ E0 = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨hxk, hxE0⟩
        have hstx : st x = k := hxk
        have hh : st x ∈ Good := hxE0.2
        exact hk (hstx ▸ hh)
      have hden : (μ.restrict E0) (st ⁻¹' {k}) = 0 := by
        rw [Measure.restrict_apply' hE0, heq, measure_empty]
      have hnum : (μ.restrict E0) (st ⁻¹' {k} \ Q) = 0 :=
        measure_mono_null sdiff_subset hden
      rw [hnum]
      exact zero_le

end Submission.Obl.k4_physical_row_packet_potential
