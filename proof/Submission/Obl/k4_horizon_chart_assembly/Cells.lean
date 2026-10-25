import Submission.Obl.k4_horizon_chart_assembly.Packets

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory
attribute [local instance] Classical.propDecidable
open scoped ENNReal BigOperators

noncomputable section

/-- Positive whole-cell floors give a finite table under the original measure. -/
theorem finite_heavy_codes {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → Z) (hcode : Measurable code) {θ : ℝ} (hθ : 0 < θ) :
    Set.Finite {z | ENNReal.ofReal θ ≤ μ (code ⁻¹' {z})} := by
  apply Measure.finite_const_le_meas_of_disjoint_iUnion μ (ENNReal.ofReal_pos.mpr hθ)
    (fun z => hcode (measurableSet_singleton z))
  · intro z z' hne
    exact Set.disjoint_left.mpr (by
      intro x hx hx'
      exact hne (hx.symm.trans hx'))
  · exact measure_ne_top μ _

noncomputable def heavyTable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → Z) (hcode : Measurable code) (θ : ℝ) (hθ : 0 < θ) : Finset Z :=
  (finite_heavy_codes μ code hcode hθ).toFinset

theorem mem_heavyTable {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → Z) (hcode : Measurable code) {θ : ℝ} (hθ : 0 < θ) (z : Z) :
    z ∈ heavyTable μ code hcode θ hθ ↔ ENNReal.ofReal θ ≤ μ (code ⁻¹' {z}) :=
  Set.Finite.mem_toFinset _

/-- Count arbitrary original whole cells by their disjoint mass witnesses. -/
theorem whole_cell_card_bound {Ω Z : Type*} [MeasurableSpace Ω] [MeasurableSpace Z]
    [MeasurableSingletonClass Z] (μ : Measure Ω) [IsFiniteMeasure μ]
    (code : Ω → Z) (hcode : Measurable code) (F : Finset Z)
    {θ : ℝ} (hθ : 0 < θ)
    (hfloor : ∀ z ∈ F, ENNReal.ofReal θ ≤ μ (code ⁻¹' {z})) :
    (F.card : ℝ) ≤ μ.real univ / θ := by
  classical
  have hsum : ENNReal.ofReal (θ * (F.card : ℝ)) ≤ μ univ := by
    calc
      _ = ∑ z ∈ F, ENNReal.ofReal θ := by simp [mul_comm, ENNReal.ofReal_mul hθ.le]
      _ ≤ ∑ z ∈ F, μ (code ⁻¹' {z}) := Finset.sum_le_sum hfloor
      _ = μ (⋃ z ∈ F, code ⁻¹' {z}) := by
        symm
        apply measure_biUnion_finset
        · intro z hz z' hz' hne
          exact Set.disjoint_left.mpr (by
            intro x hx hx'
            exact hne (hx.symm.trans hx'))
        · exact fun z hz => hcode (measurableSet_singleton z)
      _ ≤ μ univ := measure_mono (subset_univ _)
  apply (le_div_iff₀ hθ).mpr
  simpa only [measureReal_def, mul_comm] using
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ univ)).mp hsum

/-- Counting incidences between finite tables in either order is exact. -/
theorem sum_filter_card_swap {I Z : Type*} [Fintype I] [DecidableEq Z]
    (F : Finset Z) (R : I → Z → Prop) :
    ∑ i : I, (F.filter (R i)).card =
      ∑ z ∈ F, (Finset.univ.filter (fun i => R i z)).card := by
  classical
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]

/-- A bounded list of compatible groups per cell controls the sum of table sizes. -/
theorem compatible_table_card_bound {I Z : Type*} [Fintype I] [DecidableEq Z]
    (F : Finset Z) (R : I → Z → Prop) {L : ℝ}
    (hR : ∀ z ∈ F, ((Finset.univ.filter (fun i => R i z)).card : ℝ) ≤ L) :
    (∑ i : I, ((F.filter (R i)).card : ℝ)) ≤ L * (F.card : ℝ) := by
  classical
  have heq := sum_filter_card_swap F R
  have heq' := congrArg (fun n : ℕ => (n : ℝ)) heq
  push_cast at heq'
  rw [heq']
  exact (Finset.sum_le_sum hR).trans_eq (by simp [mul_comm])

/-- Removing the hidden coordinate or translating the integer codes cannot
increase the support-table budget. -/
theorem normalized_table_card_bound {I Z Y : Type*} [Fintype I]
    [DecidableEq Z] [DecidableEq Y] (F : Finset Z) (R : I → Z → Prop)
    (f : I → Z → Y) {L : ℝ}
    (hR : ∀ z ∈ F, ((Finset.univ.filter (fun i => R i z)).card : ℝ) ≤ L) :
    (∑ i : I, (((F.filter (R i)).image (f i)).card : ℝ)) ≤ L * (F.card : ℝ) := by
  classical
  apply (Finset.sum_le_sum (fun i _ => ?_)).trans (compatible_table_card_bound F R hR)
  exact_mod_cast Finset.card_image_le

end
end Submission.Obl.k4_horizon_chart_assembly
