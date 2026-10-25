-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.PhysicalCodePruning, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/PhysicalCodePruning.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/PhysicalCodePruning.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AffineCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.LightCells
import Submission.Lib.K4ReferencePruning

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open scoped ENNReal

noncomputable section

def Native.PathData.originalPhysicalCode {W : ℕ} (p : Native.PathData W) (Nk : ℝ)
    (old : Fin p.C) (baseMesh hidden : ℝ) (z : Ev) : Fin 4 → ℤ :=
  jointCode baseMesh hidden (p.nativeBaseCoordinates old z) (packetSignal Nk p old z)

theorem Native.PathData.originalPhysicalCode_coordinates {W : ℕ} (p : Native.PathData W)
    (Nk : ℝ) (old : Fin p.C) (baseMesh hidden : ℝ) (z : Ev) :
    p.originalPhysicalCode Nk old baseMesh hidden z =
      fun j => ⌊packetPhysicalPoint Nk p old z j / (if j = 3 then hidden else baseMesh)⌋ := by
  have hb : p.nativeBaseCoordinates old z = WithLp.ofLp (packetBase p old z) :=
    congrArg WithLp.ofLp (p.native_base_coordinates_eq_packetBase old z)
  unfold Native.PathData.originalPhysicalCode
  rw [hb]
  ext j
  fin_cases j <;> rfl

theorem Native.PathData.originalPhysicalCode_isotropic {W : ℕ} (p : Native.PathData W) (Nk : ℝ)
    (old : Fin p.C) (mesh : ℝ) (z : Ev) :
    p.originalPhysicalCode Nk old mesh mesh z =
      fun j => ⌊packetPhysicalPoint Nk p old z j / mesh⌋ := by
  have hb : p.nativeBaseCoordinates old z = WithLp.ofLp (packetBase p old z) :=
    congrArg WithLp.ofLp (p.native_base_coordinates_eq_packetBase old z)
  unfold Native.PathData.originalPhysicalCode
  rw [hb]
  ext j
  fin_cases j <;> rfl

theorem Native.PathData.measurable_originalPhysicalCode {W : ℕ} (p : Native.PathData W) (Nk : ℝ)
    (old : Fin p.C) (baseMesh hidden : ℝ) : Measurable (p.originalPhysicalCode Nk old baseMesh hidden) := by
  apply measurable_pi_iff.mpr
  intro j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · change Measurable (fun z : Ev => ⌊packetSignal Nk p old z / hidden⌋)
    exact Int.measurable_floor.comp ((measurable_packetSignal Nk p old).div_const hidden)
  · simp only [Native.PathData.originalPhysicalCode, jointCode, Fin.snoc_castSucc, baseCode]
    have hc : Measurable (fun z : Ev => p.nativeBaseCoordinates old z j) := by
      convert (PiLp.continuous_apply 2 _ j).measurable.comp (measurable_packetBase p old) using 1
      funext z
      exact congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v j)
        (p.native_base_coordinates_eq_packetBase old z)
    exact Int.measurable_floor.comp (hc.div_const baseMesh)

/-- A concrete finite support gives original-reference light-cell pruning.
The mesh and profile factors cancel in the total deletion budget. -/
theorem original_code_pruning_with_whole_cells
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

/-- Compatibility form of the whole-cell preparation, for any countable code. -/
theorem original_physical_code_pruning_with_pointwise_floor
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
      ∀ z ∈ keep,
        (ENNReal.ofReal (lossRate * baseMesh ^ 3 / profile) * reference) ≤
          (μ.restrict keep) (code ⁻¹' {code z}) := by
  obtain ⟨keep,hm,hl,hf,hpoint,-⟩ := original_code_pruning_with_whole_cells
    μ code hcode S hsupp _hp hprofile hRate reference hcount
  exact ⟨keep,hm,hl,hf,hpoint⟩

/-- The finite-support light-cell preparation, with a zero-or-floor conclusion. -/
theorem original_physical_code_pruning
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → Fin 4 → ℤ) (hcode : Measurable code)
    (S : Finset (Fin 4 → ℤ)) (hsupp : ∀ᵐ z ∂μ, code z ∈ S)
    {baseMesh C profile lossRate : ℝ} (hp : 0 < baseMesh) (hprofile : 0 < profile) (hRate : 0 ≤ lossRate)
    (reference : ENNReal)
    (hcount : (S.card : ℝ) * baseMesh ^ 3 ≤ C * profile) :
    ∃ keep : Set Ω, MeasurableSet keep ∧
      μ keepᶜ ≤ ENNReal.ofReal (C * lossRate) * reference ∧
      ∀ k : Fin 4 → ℤ,
        (μ.restrict keep) (code ⁻¹' {k}) = 0 ∨
          (ENNReal.ofReal (lossRate * baseMesh ^ 3 / profile) * reference) ≤
            (μ.restrict keep) (code ⁻¹' {k}) := by
  obtain ⟨keep, hm, hl, hf, -⟩ := original_physical_code_pruning_with_pointwise_floor
    μ code hcode S hsupp hp hprofile hRate reference hcount
  exact ⟨keep, hm, hl, hf⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
