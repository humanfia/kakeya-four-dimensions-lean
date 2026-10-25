-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativeVelocityReference, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalPaletteVector
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.CommonDyadicVelocityReference
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.ChildRecordRatioStates

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily velocityPalette)
open Parent.OriginalVelocityPalette
open Parent.Qualification.Jets2
open scoped ENNReal

noncomputable section

/-- Pair-coded original velocity caps pass to all dyadic query bins
under ONE fixed real reference. Original state masses are unchanged. -/
theorem current_pair_caps_under_common_reference
    {Ω Q : Type*} [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) (state : Ω → Q) (hstate : Measurable state)
    (velocity : Ω → Fin 2 → ℝ) (hvelocity : Measurable velocity)
    (palette : Measure (ℤ×ℤ)) (mass : Q → ENNReal) (C : ENNReal)
    {fineWidth : ℝ} {finest : ℕ} {reference : Measure (Fin 2 → ℝ)}
    (href : CommonDyadicVelocityReference fineWidth finest
      (fun b => (palette.map palettePairVector) {b}) reference)
    (hfine : 0 < fineWidth) (hwidth : fineWidth ≤ dyadicParameterWidth finest)
    (hcap : ∀ q (D : Set (ℤ×ℤ)), MeasurableSet D →
      μ {z | state z=q ∧ velocityPalette fineWidth (velocity z)∈D} ≤ C*mass q*palette D) :
    ∀ query : ℕ, query ≤ finest → ∀ q (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      μ {z | state z=q ∧ parameterCode (dyadicParameterWidth query) (velocity z)∈D} ≤
        (4*C)*mass q*(reference.map (parameterCode (dyadicParameterWidth query))) D := by
  have hsingle (q : Q) (b : Fin 2 → ℤ) :
      μ {z | state z=q ∧ parameterCode fineWidth (velocity z)=b} ≤
        C*mass q*(palette.map palettePairVector) {b} := by
    have hh := vector_palette_guarded_cap μ palette fineWidth velocity
      {z | state z=q} (C*mass q) (by
        intro D hD
        change μ {z | state z=q ∧ velocityPalette fineWidth (velocity z)∈D} ≤ _
        exact hcap q D hD) b
    exact hh
  intro query hquery q D hD
  rw [Measure.map_apply (measurable_parameterCode _) hD]
  exact href.current_caps hfine hwidth μ state hstate velocity hvelocity mass C hsingle
    query hquery q D

/-- The post-state graph ratios supply the exact all-query current
palette bounds used by physical row regularity and residual comparison. -/
theorem GraphRecordRatios.dyadic_current_caps {W : ℕ} {p : PathData W} {N : ℝ}
    {root : Fin p.C} {graphMesh finePv radius stripWidth : ℝ}
    {stripCoeff paletteCoeff : ENNReal} {raw : Measure Ev} {E : Set Ev}
    {palette : Measure (ℤ×ℤ)}
    (ratios : GraphRecordRatios p N root graphMesh finePv radius stripWidth
      stripCoeff paletteCoeff raw E palette)
    {finest : ℕ} {reference : Measure (Fin 2 → ℝ)}
    (href : CommonDyadicVelocityReference finePv finest
      (fun b => (palette.map palettePairVector) {b}) reference)
    (hfine : 0 < finePv) (hwidth : finePv ≤ dyadicParameterWidth finest) :
    ∀ query : ℕ, query ≤ finest → ∀ q (D : Set (Fin 2 → ℤ)), MeasurableSet D →
      (raw.restrict E) {z |
        clockParentCode p root (Parent.SignalGraph.ancestorSignal N p root) graphMesh z=q ∧
        parameterCode (dyadicParameterWidth query) (fun j => Parent.v z.1 j)∈D} ≤
      (4*paletteCoeff)*(raw.restrict E)
        (clockParentCode p root (Parent.SignalGraph.ancestorSignal N p root) graphMesh ⁻¹' {q})*
          (reference.map (parameterCode (dyadicParameterWidth query))) D :=
  current_pair_caps_under_common_reference (raw.restrict E)
    (clockParentCode p root (Parent.SignalGraph.ancestorSignal N p root) graphMesh)
    (measurable_clockParentCode p root _ graphMesh) (fun z j => Parent.v z.1 j)
    (by unfold Parent.v; fun_prop) palette
    (fun q => (raw.restrict E)
      (clockParentCode p root (Parent.SignalGraph.ancestorSignal N p root) graphMesh ⁻¹' {q}))
    paletteCoeff href hfine hwidth ratios.2.2

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
    (F : PaletteFamily Q i stop a A θ)

/-- Construct the actual ancestor's single dyadic reference before
all incidence restrictions, states, cells and query widths. -/
theorem exists_original_common_dyadic_reference (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w⊆d.E k w) (root : Fin p.C) (hactive : F.active root)
    (fineWidth : ℝ) (finest : ℕ) :
    ∃ reference : Measure (Fin 2 → ℝ), CommonDyadicVelocityReference fineWidth finest
      (fun b => originalVectorPalette F root fineWidth {b}) reference := by
  letI : IsProbabilityMeasure (originalVectorPalette F root fineWidth) :=
    originalVectorPalette_probability F hd hp hHE root hactive fineWidth
  apply exists_common_dyadic_velocity_reference
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro bins
  rw [sum_measure_singleton]
  exact (measure_mono (subset_univ _)).trans_eq (by simp)

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
