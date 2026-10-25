-- Adapted from this LOT tree, o232/x0812 014729b9, Submission/Obl/k4_finite_positive_prepared_models/SourceSelectionNumerator.lean; namespace renamed.
import Submission.Obl.k4_finite_affine_parent_sources.SourceNumerator
import Submission.Obl.k4_finite_affine_parent_sources.ModelMeasures

/-!
# End histories of counted incidences, and native-bin numerators

`history_eq_of_counted`: a terminal incidence counted by a label off that label's block endpoints
has that label as its history at the label's level.

`bin_numerator`: a fixed reference law `μ R` (original law restricted to a reference set `R`,
normalised by `nuE`) and a palette `π` dominating every per-code numerator of submeasures of
`nuE μ R` (x0807's `exists_masked_parent_palette`) turn a per-code numerator of an original
event `T ⊆ R` into a numerator of every native velocity bin: `≤ 4 c π (bin)`.

Written by x0812 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

open MeasureTheory Set
open Submission.Obl.k4_finite_forest_width_selection
open scoped Classical

noncomputable section

local instance optMeasSSN (C : ℕ) : MeasurableSpace (Option (Fin C)) := ⊤
local instance optSingSSN (C : ℕ) : MeasurableSingletonClass (Option (Fin C)) := ⟨fun _ => trivial⟩

section

variable {W m Mp Dp : ℕ} {p : PathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Trajectory}
    {E : Fin W → Set Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {sg : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m sg δ₀ Mp Dp σ)

include hp

/-- **The history of a counted terminal incidence** at the counting label's level. -/
theorem history_eq_of_counted {w : Fin W} {h : Fin p.C} {x : Incidence}
    (hw : p.world h = w)
    (hterm : x ∈ TerminalInc W p.C m p.lev p.world p.counted w)
    (hx : x ∈ p.counted h)
    (hend : x.2 ≠ (p.bin h : ℝ) / (2 : ℝ) ^ p.T (p.lev h) ∧
      x.2 ≠ ((p.bin h : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev h)) :
    p.history m (p.lev h) (w, x) = some h := by
  obtain ⟨bt, hbt⟩ := p.terminalCode_exists m w hterm
  have hspec := p.terminalCode_spec m hbt
  simp only [PathData.history, Function.comp_apply, hbt, PathData.ancestorCode, Option.map_some,
    Option.some.injEq]
  have hsup := hp.counted_support h x hx
  have hlev : p.lev h ≤ p.lev bt := by
    rw [hspec.1]
    have := hp.label_level h
    omega
  have hio : x.2 ∈ Ioo ((p.bin h : ℝ) / (2 : ℝ) ^ p.T (p.lev h))
      (((p.bin h : ℝ) + 1) / (2 : ℝ) ^ p.T (p.lev h)) :=
    ⟨lt_of_le_of_ne hsup.2.2.1.1 (Ne.symm hend.1), lt_of_le_of_ne hsup.2.2.1.2 hend.2⟩
  exact hp.ancestor_eq_of_interior hlev (hspec.2.1.trans hw.symm) hspec.2.2 hsup.2.1 hio

end

/-- **Native-bin numerator from per-code numerators.** -/
theorem bin_numerator {ι : Type*} [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (μ : Measure Incidence) [IsFiniteMeasure μ] (R T : Set Incidence) (hR : MeasurableSet R)
    (hT : MeasurableSet T) (hTR : T ⊆ R) (hR0 : μ R ≠ 0)
    (U : Incidence → ι) (hU : Measurable U) (V : Incidence → ℝ) (π : Measure ℝ) {blur : ℝ}
    (hdom : ∀ (ρ : Measure Incidence), ρ ≤ nuE μ R → ∀ (P : Set Incidence) (C : ENNReal)
      (width : ℝ), 2 * blur ≤ width →
      (∀ i, ρ (P ∩ U ⁻¹' {i}) ≤ C * nuE μ R (U ⁻¹' {i})) → ∀ e : ℤ,
      ρ (P ∩ {z | ⌊V z / width⌋ = e}) ≤ 4 * C * π {w | ⌊w / width⌋ = e})
    (c : ENNReal) (hcode : ∀ i, μ (T ∩ U ⁻¹' {i}) ≤ c * nuE μ R (U ⁻¹' {i}))
    {width : ℝ} (hwidth : 2 * blur ≤ width) (e : ℤ) :
    μ (T ∩ {z | ⌊V z / width⌋ = e}) ≤ 4 * c * π {w | ⌊w / width⌋ = e} := by
  have hRt : μ R ≠ ⊤ := measure_ne_top _ _
  set ρ := (μ R)⁻¹ • μ.restrict T with hρ
  have hρle : ρ ≤ nuE μ R := by
    rw [hρ, nuE]
    refine Measure.le_iff'.mpr fun A => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  have hρcode : ∀ i, ρ (univ ∩ U ⁻¹' {i}) ≤ ((μ R)⁻¹ * c) * nuE μ R (U ⁻¹' {i}) := by
    intro i
    rw [univ_inter, hρ, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (hU (measurableSet_singleton i)), inter_comm, mul_assoc]
    gcongr
    exact hcode i
  have h := hdom ρ hρle univ ((μ R)⁻¹ * c) width hwidth hρcode e
  rw [univ_inter] at h
  have hρbin : ρ {z | ⌊V z / width⌋ = e} = (μ R)⁻¹ * μ (T ∩ {z | ⌊V z / width⌋ = e}) := by
    rw [hρ, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' hT, inter_comm]
  rw [hρbin] at h
  calc μ (T ∩ {z | ⌊V z / width⌋ = e})
      = μ R * ((μ R)⁻¹ * μ (T ∩ {z | ⌊V z / width⌋ = e})) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hR0 hRt, one_mul]
    _ ≤ μ R * (4 * ((μ R)⁻¹ * c) * π {w | ⌊w / width⌋ = e}) := by gcongr
    _ = 4 * c * π {w | ⌊w / width⌋ = e} * (μ R * (μ R)⁻¹) := by ring
    _ = 4 * c * π {w | ⌊w / width⌋ = e} := by
        rw [ENNReal.mul_inv_cancel hR0 hRt, mul_one]

end

end Submission.Obl.k4_finite_affine_parent_sources
