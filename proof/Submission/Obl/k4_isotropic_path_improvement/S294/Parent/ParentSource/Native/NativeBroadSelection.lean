-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeBroadSelection, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeBroadSelection.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeBroadSelection.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeBroadSelection.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeBroadSelection.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeNarrowSelection
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.ConditionedLikelihood

/-! The complement of intrinsic narrowness gives actual broad probability
laws on retained fine states. All thresholds still use the OLD fine marginal. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal

/-- Normalizing a retained fine state costs only its explicit retained
fraction. This does not replace any old reference marginal in a likelihood cap. -/
theorem selected_fine_state_breadth {Ω Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → Z) (U : Set Ω)
    (hcell : ∀ e, MeasurableSet {z | f z = e}) (hU : MeasurableSet U)
    (V : Ω → StripSpace) (r fraction α : ℝ) (hα : 0 < α) (hfraction : 0 ≤ fraction)
    (e : Z) (hpos : 0 < μ.real {z | f z = e})
    (he : e ∉ narrowFineStates μ f U V r fraction)
    (hretain : α * μ.real {z | f z = e} ≤ μ.real {z | f z = e ∧ z ∈ U}) :
    IsProbabilityMeasure (ProbabilityTheory.cond μ {z | f z = e ∧ z ∈ U}) ∧
      ∀ (n : StripSpace) (β : ℝ), ‖n‖ = 1 →
        (ProbabilityTheory.cond μ {z | f z = e ∧ z ∈ U}).real
          {z | V z ∈ affineStrip n β r} < fraction / α := by
  let A := {z | f z = e ∧ z ∈ U}
  have hA : MeasurableSet A := (hcell e).inter hU
  have hApos : 0 < μ.real A := (mul_pos hα hpos).trans_le hretain
  have hAne : μ A ≠ 0 := by
    intro hz
    simp only [measureReal_def, hz, ENNReal.toReal_zero, lt_self_iff_false] at hApos
  refine ⟨ProbabilityTheory.cond_isProbabilityMeasure_of_finite hAne (measure_ne_top _ _), ?_⟩
  intro n β hn
  rw [cond_real_apply μ A hA]
  apply (div_lt_iff₀ hApos).mpr
  have hstrip := broad_of_not_mem_narrowFineStates μ f U V r fraction hpos he n β hn
  have hnum : μ.real (A ∩ {z | V z ∈ affineStrip n β r}) =
      μ.real {z | f z = e ∧ z ∈ U ∧ V z ∈ affineStrip n β r} := by
    congr 1
    ext z
    simp only [A, mem_inter_iff, mem_ofPred_eq, and_assoc]
  rw [hnum]
  apply hstrip.trans_le
  calc
    fraction * μ.real {z | f z = e} = (fraction / α) * (α * μ.real {z | f z = e}) := by
      field_simp
    _ ≤ (fraction / α) * μ.real A :=
      mul_le_mul_of_nonneg_left hretain (div_nonneg hfraction hα.le)

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)

theorem PreparedAngularPath.intrinsic_broad_fine_state
    (hF : ∀ b, MeasurableSet (p.F b)) (code : Fin p.C → ℕ) (stop : ℕ)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)))
    (r fraction α : ℝ) (hα : 0 < α) (hfraction : 0 ≤ fraction)
    (b : Fin p.C) (hU : MeasurableSet (U b)) (e : ℕ)
    (hpos : 0 < (Q.coarseLaw (p.lev b) (code b)).real
      {z | finitePacketHistory p.lev p.γ p.F stop z = e})
    (he : e ∉ Q.intrinsicNarrowStates code stop U r fraction b)
    (hretain : α * (Q.coarseLaw (p.lev b) (code b)).real
        {z | finitePacketHistory p.lev p.γ p.F stop z = e} ≤
      (Q.coarseLaw (p.lev b) (code b)).real
        {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ U b}) :
    IsProbabilityMeasure (ProbabilityTheory.cond (Q.coarseLaw (p.lev b) (code b))
      {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ U b}) ∧
      ∀ (n : StripSpace) (β : ℝ), ‖n‖ = 1 →
        (ProbabilityTheory.cond (Q.coarseLaw (p.lev b) (code b))
          {z | finitePacketHistory p.lev p.γ p.F stop z = e ∧ z ∈ U b}).real
          {z | p.normalizedVelocity b z.2 ∈ affineStrip n β r} < fraction / α := by
  let : IsFiniteMeasure (Q.coarseLaw (p.lev b) (code b)) := by
    change IsFiniteMeasure (ProbabilityTheory.cond Q.law _)
    infer_instance
  exact selected_fine_state_breadth (Q.coarseLaw (p.lev b) (code b))
    (finitePacketHistory p.lev p.γ p.F stop) (U b)
    (fun e => measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF stop) measurable_const)
    hU (fun z => p.normalizedVelocity b z.2) r fraction α hα hfraction e hpos he hretain

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
