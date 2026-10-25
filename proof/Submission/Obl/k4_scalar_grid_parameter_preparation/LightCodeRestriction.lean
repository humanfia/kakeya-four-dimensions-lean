/- Adapted from this LOT tree, o092, session x0317, commit d881f97f20e4.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/LightCodeRestriction.lean -/
import Mathlib

/-! Light original coefficient bins define a measurable restriction with strict bin ceilings. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

noncomputable section

open Set MeasureTheory
open scoped Classical ENNReal

def lightCodeSet {X C : Type*} [MeasurableSpace X] (μ : Measure X) (code : X → C)
    (τ : C → ℝ≥0∞) : Set X := {l | μ {l' | code l' = code l} < τ (code l)}

theorem measurableSet_lightCodeSet {X C : Type*} [MeasurableSpace X] [Countable C]
    (μ : Measure X) (code : X → C) (τ : C → ℝ≥0∞)
    (hcode : ∀ c, MeasurableSet {l | code l = c}) : MeasurableSet (lightCodeSet μ code τ) := by
  have he : lightCodeSet μ code τ = ⋃ c ∈ {c | μ {l | code l = c} < τ c}, {l | code l = c} := by
    ext l
    constructor
    · intro hl
      exact Set.mem_iUnion₂.mpr ⟨code l,hl,rfl⟩
    · intro hl
      obtain ⟨c,hc,hlc⟩ := Set.mem_iUnion₂.mp hl
      change μ {l' | code l' = code l} < τ (code l)
      change code l = c at hlc
      change μ {l' | code l' = c} < τ c at hc
      simpa only [hlc] using hc
  rw [he]
  exact MeasurableSet.biUnion (Set.to_countable _) (fun c _ => hcode c)

theorem restrict_lightCodeSet_bin_lt {X C : Type*} [MeasurableSpace X]
    (μ : Measure X) (code : X → C) (τ : C → ℝ≥0∞)
    (hcode : ∀ c, MeasurableSet {l | code l = c}) (c : C) (hτ : 0 < τ c) :
    (μ.restrict (lightCodeSet μ code τ)) {l | code l = c} < τ c := by
  by_cases hc : μ {l | code l = c} < τ c
  · have hle : μ.restrict (lightCodeSet μ code τ) ≤ μ := Measure.restrict_le_self
    exact (hle _).trans_lt hc
  · rw [Measure.restrict_apply (hcode c)]
    have he : {l | code l = c} ∩ lightCodeSet μ code τ = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro l hl
      have hh := hl.2
      change μ {l' | code l' = code l} < τ (code l) at hh
      rw [hl.1] at hh
      exact hc hh
    rw [he,measure_empty]
    exact hτ

end

end Submission.Obl.k4_scalar_grid_parameter_preparation
