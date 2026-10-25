-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.WholeCodePruning, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/WholeCodePruning.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit adc5136f,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/WholeCodePruning.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o265/x0943, commit4fa13b3cf,
-- Broad/Source/PhysicalCodePruning.lean. Original generic whole-cell proof by x0943.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.LightCells
import Submission.Lib.K4ReferencePruning

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ClockCalibration
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem whole_code_pruning
    {Ω I : Type*} [MeasurableSpace Ω] [MeasurableSpace I]
    [MeasurableSingletonClass I] [Countable I]
    (μ : Measure Ω) (code : Ω → I) (hcode : Measurable code)
    (S : Finset I) (hsupp : ∀ᵐ z ∂μ, code z ∈ S)
    {baseMesh C profile lossRate : ℝ} (_hp : 0 < baseMesh) (hprofile : 0 < profile) (hRate : 0 ≤ lossRate)
    (reference : ENNReal)
    (hcount : (S.card : ℝ) * baseMesh ^ 3 ≤ C * profile) :
    ∃ keep : Set Ω, MeasurableSet keep ∧
      μ keepᶜ ≤ ENNReal.ofReal (C * lossRate) * reference ∧
      (∀ k : I,
        (μ.restrict keep) (code ⁻¹' {k}) = 0 ∨
          (ENNReal.ofReal (lossRate * baseMesh ^ 3 / profile) * reference) ≤
            (μ.restrict keep) (code ⁻¹' {k})) ∧
      (∀ z ∈ keep,
        (ENNReal.ofReal (lossRate * baseMesh ^ 3 / profile) * reference) ≤
          (μ.restrict keep) (code ⁻¹' {code z})) ∧
      ∀ x y, code x=code y → (x∈keep ↔ y∈keep) := by
  let floor := ENNReal.ofReal (lossRate * baseMesh ^ 3 / profile) * reference
  let keep := Broad.heavySet μ code floor
  refine ⟨keep, Broad.measurableSet_heavySet μ hcode floor, ?_, ?_, ?_, ?_⟩
  · have hnull : μ {z | code z ∉ S} = 0 := ae_iff.mp hsupp
    have hraw := Broad.measure_compl_heavySet_le μ code floor S hnull
    have hreal : (S.card : ℝ) * (lossRate * baseMesh ^ 3 / profile) ≤ C * lossRate := by
      have hh := mul_le_mul_of_nonneg_right hcount (div_nonneg hRate hprofile.le)
      calc
        _ = ((S.card : ℝ) * baseMesh ^ 3) * (lossRate / profile) := by ring
        _ ≤ (C * profile) * (lossRate / profile) := hh
        _ = _ := by field_simp
    refine hraw.trans ?_
    change (S.card : ENNReal) * (ENNReal.ofReal (lossRate * baseMesh ^ 3 / profile) * reference) ≤ _
    rw [← mul_assoc, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ (S.card : ℝ))]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hreal) le_rfl
  · exact Broad.restrict_heavySet_fibre μ hcode floor
  · intro z hz
    have hz' : floor ≤ μ (code ⁻¹' {code z}) := hz
    have hm := Submission.Lib.K4ReferencePruning.reference_kept_state_mass
      μ code hcode (fun _ => floor) 1 (code z)
    have hkeepEq : Submission.Lib.K4ReferencePruning.referenceKeep
        μ code (fun _ => floor) 1=keep := by
      ext x
      simp only [Submission.Lib.K4ReferencePruning.referenceKeep, keep, Broad.heavySet,
        Set.mem_ofPred_eq, Set.mem_preimage, one_mul]
    rw [hkeepEq] at hm
    have heq : (μ.restrict keep) (code ⁻¹' {code z}) = μ (code ⁻¹' {code z}) := by
      simpa only [one_mul, ite_eq_left hz'] using hm
    rw [heq]
    exact hz'
  · intro x y hxy
    change floor ≤ μ (code ⁻¹' {code x}) ↔ floor ≤ μ (code ⁻¹' {code y})
    rw [hxy]

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ClockCalibration
