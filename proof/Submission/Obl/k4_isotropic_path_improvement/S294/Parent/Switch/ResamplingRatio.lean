-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Switch.ResamplingRatio, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Switch/ResamplingRatio.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Conditional state resampling for countable states, and
per-state breadth ratios in the form used by
`Submission.Lib.K4PolynomialNorming.actual_substantial_six_basis_switch_family`.
-/
import Submission.Lib.K4ScalarSwitching.Resampling

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Switch

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Almost every event has a state of positive mass. -/
theorem ae_state_mass_ne_zero {Ω Q : Type*} [MeasurableSpace Ω] [MeasurableSpace Q]
    [MeasurableSingletonClass Q] [Countable Q] (μ : Measure Ω) (state : Ω → Q) :
    ∀ᵐ z ∂μ, μ (state ⁻¹' {state z}) ≠ 0 := by
  have hnull : μ {z | μ (state ⁻¹' {state z}) = 0} = 0 := by
    have hsub : {z | μ (state ⁻¹' {state z}) = 0} ⊆
        ⋃ q ∈ {q : Q | μ (state ⁻¹' {q}) = 0}, state ⁻¹' {q} := by
      intro z hz
      exact Set.mem_biUnion (x := state z) hz rfl
    refine measure_mono_null hsub ?_
    exact (measure_biUnion_null_iff (Set.to_countable _)).mpr (fun q hq => hq)
  rw [ae_iff]
  simpa only [ne_eq, not_not] using hnull

/-- For countable states the conditional redraw is the normalized
restriction to the current state. -/
theorem conditionalResampling_apply_of_countable {Ω Q : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (state : Ω → Q) (hstate : Measurable state) :
    ∀ᵐ z ∂μ, ∀ s : Set Ω, MeasurableSet s →
      Submission.Lib.K4ScalarSwitching.conditionalResampling μ state hstate z s =
        (μ (state ⁻¹' {state z}))⁻¹ * μ (state ⁻¹' {state z} ∩ s) := by
  filter_upwards [ae_state_mass_ne_zero μ state] with z hz s hs
  have hmap : μ.map state {state z} ≠ 0 := by
    rw [Measure.map_apply hstate (measurableSet_singleton _)]
    exact hz
  change ((condDistrib (id : Ω → Ω) state μ).comap state hstate) z s = _
  rw [Kernel.comap_apply, condDistrib_apply_of_ne_zero hstate measurable_id (state z) hmap s,
    Measure.map_apply hstate (measurableSet_singleton _)]
  congr 1
  rw [Measure.map_apply (hstate.prodMk measurable_id) ((measurableSet_singleton _).prod hs)]
  congr 1

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Switch

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Switch

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- Per-state breadth ratios give the conditional-redraw breadth hypothesis
of the six-switch experiment. -/
theorem broad_resampling_of_state_ratio {L Q C : Type*} [MeasurableSpace L]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace C] [MeasurableSingletonClass C] [Countable C]
    [StandardBorelSpace (L × ℝ)] [Nonempty (L × ℝ)]
    (P : Measure (L × ℝ)) [IsFiniteMeasure P] (state : L × ℝ → Q) (hstate : Measurable state)
    (control : L → C) (hcontrol : Measurable control) (v : C → EuclideanSpace ℝ (Fin 3))
    (r : ℝ) (p : ENNReal)
    (hratio : ∀ q (W : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ W < 3 →
      P (state ⁻¹' {q} ∩ {z | Metric.infDist (v (control z.1)) (W : Set _) < r}) ≤
        p * P (state ⁻¹' {q})) :
    ∀ᵐ z ∂P, ∀ W : Submodule ℝ (EuclideanSpace ℝ (Fin 3)), Module.finrank ℝ W < 3 →
      (Submission.Lib.K4ScalarSwitching.conditionalResampling P state hstate z).map
        (fun y => control y.1) {c | Metric.infDist (v c) (W : Set _) < r} ≤ p := by
  filter_upwards [conditionalResampling_apply_of_countable P state hstate,
    ae_state_mass_ne_zero P state] with z hz hz0 W hW
  have hc : Measurable (fun y : L × ℝ => control y.1) := hcontrol.comp measurable_fst
  have hB : MeasurableSet {c : C | Metric.infDist (v c) (W : Set _) < r} :=
    (Set.to_countable _).measurableSet
  rw [Measure.map_apply hc hB, hz _ (hc hB)]
  calc (P (state ⁻¹' {state z}))⁻¹ *
        P (state ⁻¹' {state z} ∩ (fun y => control y.1) ⁻¹'
          {c | Metric.infDist (v c) (W : Set _) < r})
      ≤ (P (state ⁻¹' {state z}))⁻¹ * (p * P (state ⁻¹' {state z})) :=
        mul_le_mul_right (hratio (state z) W hW) _
    _ = p := by
      rw [mul_comm p, ← mul_assoc, ENNReal.inv_mul_cancel hz0 (measure_ne_top _ _), one_mul]

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Switch
