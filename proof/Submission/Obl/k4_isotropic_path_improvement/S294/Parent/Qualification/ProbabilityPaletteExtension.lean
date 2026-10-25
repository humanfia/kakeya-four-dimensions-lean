-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ProbabilityPaletteExtension, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ProbabilityPaletteExtension.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 9990050b5ef6bdaa550836abbcdb33eb4643e8c9,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ProbabilityPaletteExtension.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalCoarsePalette
import Mathlib.MeasureTheory.Measure.Sum

/-! # Probability palettes dominating unchanged original subprobability weights

Only the auxiliary velocity palette is extended. No trajectory prior
or incidence law is normalized or replaced.
-/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification
open Set MeasureTheory
open scoped ENNReal
noncomputable section

theorem exists_probability_palette_dominating_subprobability {V : Type*}
    [MeasurableSpace V] (v0 : V) (μ : Measure V) (hμ : μ univ ≤ 1) :
    ∃ π : Measure V, IsProbabilityMeasure π ∧ μ ≤ π := by
  by_cases hzero : μ univ=0
  · refine ⟨Measure.dirac v0,inferInstance,?_⟩
    intro A
    rw [measure_mono_null (subset_univ A) hzero]
    exact zero_le
  · have htop : μ univ ≠ ∞ := (lt_of_le_of_lt hμ (by norm_num : (1 : ENNReal)<∞)).ne
    refine ⟨originalCoarsePalette μ univ,
      originalCoarsePalette_probability μ univ hzero htop,?_⟩
    intro A
    calc
      μ A = (μ univ)⁻¹*(μ univ*μ A) := by
        rw [← mul_assoc,ENNReal.inv_mul_cancel hzero htop,one_mul]
      _ ≤ (μ univ)⁻¹*(1*μ A) :=
        mul_le_mul' le_rfl (mul_le_mul' hμ le_rfl)
      _ = (originalCoarsePalette μ univ) A := by
        simp only [originalCoarsePalette,Measure.restrict_univ,Measure.smul_apply,
          smul_eq_mul,one_mul]

theorem exists_probability_palette_dominating_weights {V : Type*}
    [MeasurableSpace V] [MeasurableSingletonClass V]
    (v0 : V) (w : V → ENNReal) (hweight : (∑' v, w v) ≤ 1) :
    ∃ π : Measure V, IsProbabilityMeasure π ∧
      Measure.sum (fun v => w v • Measure.dirac v) ≤ π ∧ ∀ v, w v ≤ π {v} := by
  let μ := Measure.sum (fun v => w v • Measure.dirac v)
  have hμ : μ univ ≤ 1 := by
    simpa only [μ,Measure.sum_apply _ MeasurableSet.univ,Measure.smul_apply,
      smul_eq_mul,Measure.dirac_apply_of_mem (mem_univ _),mul_one] using hweight
  obtain ⟨π,hπ,hdom⟩ := exists_probability_palette_dominating_subprobability v0 μ hμ
  refine ⟨π,hπ,hdom,?_⟩
  intro v
  have hh := Measure.le_sum (fun u => w u • Measure.dirac u) v {v}
  have hpoint : w v ≤ μ {v} := by
    simpa only [Measure.smul_apply,smul_eq_mul,
      Measure.dirac_apply_of_mem (mem_singleton v),mul_one] using hh
  exact hpoint.trans (hdom _)

/-- Atomic ceilings with an original subprobability palette imply
all measurable palette tests against one dominating probability.
The original incidence law and state references are unchanged. -/
theorem exists_probability_palette_with_state_caps {Ω V Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (v0 : V) (w : V → ENNReal) (hweight : (∑' v, w v) ≤ 1)
    (μ : Measure Ω) (state : Ω → Q) (control : Ω → V) (hm : Measurable control)
    (reference : Q → ENNReal) (C : ENNReal)
    (hcap : ∀ q v, μ {z | state z=q ∧ control z=v} ≤ C*reference q*w v) :
    ∃ π : Measure V, IsProbabilityMeasure π ∧
      ∀ q (D : Set V), MeasurableSet D →
        μ {z | state z=q ∧ control z∈D} ≤ C*reference q*π D := by
  obtain ⟨π,hπ,_,hpoint⟩ := exists_probability_palette_dominating_weights v0 w hweight
  refine ⟨π,hπ,?_⟩
  intro q D hD
  let ν := μ.restrict {z | state z=q}
  have hnum (v : V) : ν (control ⁻¹' {v}) ≤ C*reference q*π {v} := by
    rw [Measure.restrict_apply (hm (measurableSet_singleton v))]
    have heq : control ⁻¹' {v} ∩ {z | state z=q}={z | state z=q ∧ control z=v} := by
      ext z
      simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_setOf_eq,and_comm]
    rw [heq]
    exact (hcap q v).trans (mul_le_mul' le_rfl (hpoint v))
  have hsumπ : (∑' v : D, π {(v : V)})=π D := by
    simpa using tsum_measure_preimage_singleton (μ := π) (f := id) (Set.to_countable D)
      (fun v _ => measurableSet_singleton v)
  calc
    _ = ν (control ⁻¹' D) := by
      rw [Measure.restrict_apply (hm hD)]
      congr 1
      ext z
      simp only [mem_inter_iff,mem_preimage,mem_setOf_eq,and_comm]
    _ = ∑' v : D, ν (control ⁻¹' {(v : V)}) :=
      (tsum_measure_preimage_singleton (Set.to_countable D)
        (fun v _ => hm (measurableSet_singleton v))).symm
    _ ≤ ∑' v : D, C*reference q*π {(v : V)} := ENNReal.tsum_le_tsum (fun v => hnum v)
    _ = C*reference q*π D := by rw [ENNReal.tsum_mul_left,hsumπ]

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
