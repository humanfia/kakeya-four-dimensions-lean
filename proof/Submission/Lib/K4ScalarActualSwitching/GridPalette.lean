/-
Adapted from: here:o062
Original proof: session x0212, branch x0212, commit 0e63fd12e103b2363672ba95f33ca7f7ac0f50ba,
Submission/Obl/k4_scalar_mesh_projection/GridPalette.lean.
The conditional and switching primitives are imported from the accepted
K4ScalarSwitching contribution, rather than copied.
-/

import Submission.Lib.K4ScalarActualSwitching.PaletteConditioning

namespace Submission.Lib.K4ScalarActualSwitching

open Submission.Lib.K4ScalarSwitching

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

theorem measure_le_of_countable_atoms {V : Type*}
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (μ ν : Measure V) (hatom : ∀ v : V, μ {v} ≤ ν {v}) : μ ≤ ν := by
  classical
  refine Measure.le_iff.mpr ?_
  intro A _
  have hA : A = ⋃ v : A, ({v.val} : Set V) := by
    ext v
    simp only [mem_iUnion, mem_singleton_iff]
    constructor
    · intro hv
      exact ⟨⟨v, hv⟩, rfl⟩
    · rintro ⟨v, rfl⟩
      exact v.property
  have hd : Pairwise (fun v w : A => Disjoint ({v.val} : Set V) {w.val}) := by
    intro v w hvw
    apply Set.disjoint_left.mpr
    intro z hzv hzw
    apply hvw
    apply Subtype.ext
    exact (mem_singleton_iff.mp hzv).symm.trans (mem_singleton_iff.mp hzw)
  rw [hA, measure_iUnion hd (fun v => measurableSet_singleton v.val),
    measure_iUnion hd (fun v => measurableSet_singleton v.val)]
  exact ENNReal.tsum_le_tsum fun v => hatom v.val

/-- Relative caps on individual countable palette bins give the entire
rectangular cap used by the actual conditional redraw. -/
theorem rectangular_palette_caps_of_atoms {Ω Q V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (μ : Measure Ω) (state : Ω → Q) (hstate : Measurable state)
    (control : Ω → V) (hcontrol : Measurable control) (π : Measure V) (K : ENNReal)
    (hatom : ∀ q v, μ {ω | state ω = q ∧ control ω = v} ≤
      K * μ (state ⁻¹' {q}) * π {v}) :
    ∀ q (A : Set V), MeasurableSet A →
      μ {ω | state ω = q ∧ control ω ∈ A} ≤ K * μ (state ⁻¹' {q}) * π A := by
  intro q A hA
  let μq := (μ.restrict (state ⁻¹' {q})).map control
  have hrect (E : Set V) (hE : MeasurableSet E) :
      μq E = μ {ω | state ω = q ∧ control ω ∈ E} := by
    rw [Measure.map_apply hcontrol hE,
      Measure.restrict_apply (hE.preimage hcontrol)]
    congr 1
    ext ω
    simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    exact and_comm
  have hdom : μq ≤ (K * μ (state ⁻¹' {q})) • π := by
    apply measure_le_of_countable_atoms
    intro v
    rw [hrect {v} (measurableSet_singleton v), Measure.smul_apply, smul_eq_mul]
    simpa only [mem_singleton_iff] using hatom q v
  have h := Measure.le_iff.mp hdom A hA
  simpa only [hrect A hA, Measure.smul_apply, smul_eq_mul] using h

theorem conditionalResampling_palette_le_of_atoms {Ω Q V : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
    [MeasurableSingletonClass V] [Countable V]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (state : Ω → Q) (hstate : Measurable state)
    (control : Ω → V) (hcontrol : Measurable control) (π : Measure V) (K : ENNReal)
    (hatom : ∀ q v, μ {ω | state ω = q ∧ control ω = v} ≤
      K * μ (state ⁻¹' {q}) * π {v}) :
    ∀ᵐ ω ∂μ, (conditionalResampling μ state hstate ω).map control ≤ K • π :=
  conditionalResampling_palette_le μ state hstate control hcontrol π K
    (rectangular_palette_caps_of_atoms μ state hstate control hcontrol π K hatom)

/-- The primitive countable bin caps can be pushed to real-valued bin
centers before any actual incidence is redrawn. -/
theorem rectangular_rounded_palette_caps_of_atoms {Ω Q V : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
    (μ : Measure Ω) (state : Ω → Q) (hstate : Measurable state)
    (code : Ω → V) (hcode : Measurable code)
    (center : V → ℝ) (hcenter : Measurable center) (π : Measure V) (K : ENNReal)
    (hatom : ∀ q v, μ {ω | state ω = q ∧ code ω = v} ≤
      K * μ (state ⁻¹' {q}) * π {v}) :
    ∀ q (A : Set ℝ), MeasurableSet A →
      μ {ω | state ω = q ∧ center (code ω) ∈ A} ≤
        K * μ (state ⁻¹' {q}) * π.map center A := by
  intro q A hA
  have h := rectangular_palette_caps_of_atoms μ state hstate code hcode π K hatom
    q (center ⁻¹' A) (hA.preimage hcenter)
  simpa only [Measure.map_apply hcenter hA, mem_preimage] using h

/-- Individual original grid-bin caps control the rounded real velocity
observed from the genuine conditional redraw. -/
theorem conditionalResampling_rounded_palette_le {Ω Q V : Type*}
    [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    [MeasurableSpace V] [StandardBorelSpace V] [Nonempty V]
    [MeasurableSingletonClass V] [Countable V]
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (state : Ω → Q) (hstate : Measurable state)
    (code : Ω → V) (hcode : Measurable code)
    (center : V → ℝ) (hcenter : Measurable center) (π : Measure V) (K : ENNReal)
    (hatom : ∀ q v, μ {ω | state ω = q ∧ code ω = v} ≤
      K * μ (state ⁻¹' {q}) * π {v}) :
    ∀ᵐ ω ∂μ, (conditionalResampling μ state hstate ω).map (center ∘ code) ≤
      K • π.map center := by
  filter_upwards [conditionalResampling_palette_le_of_atoms μ state hstate code hcode π K hatom]
    with ω hω
  have h := Measure.map_mono hω hcenter
  rw [Measure.map_smul K hcenter.aemeasurable, Measure.map_map hcenter hcode] at h
  exact h

end Submission.Lib.K4ScalarActualSwitching
