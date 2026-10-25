-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Forward.CoarseTransfer, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PreparedLaw

/-!
# The front's coarse laws are multiples of the original world measure

The ported front (`Parent/ParentSource/Native`) states its palette caps and breadth for
`ProbabilityTheory.cond (preparedResidualLaw μ ω H) C`, where `C` is the coarse support of one
packet (a single world `w₀`). This file shows that this conditional law is, on every
measurable set, the original world measure `μ w₀` of `H w₀ ∩ C ∩ D` divided by that of
`H w₀ ∩ C`; so every ratio inequality of the front holds verbatim for the original
measure, which is what the virtual packet's clauses are stated with.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294

namespace Forward

open MeasureTheory Set
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
open scoped ENNReal

noncomputable section

variable {W : ℕ} {X : Type*} [MeasurableSpace X]

/-- The world section of a labelled set. -/
def worldSection (w₀ : Fin W) (D : Set (Fin W × X)) : Set X := {x | (w₀, x) ∈ D}

theorem measurableSet_worldSection (w₀ : Fin W) {D : Set (Fin W × X)} (hD : MeasurableSet D) :
    MeasurableSet (worldSection w₀ D) :=
  measurable_prodMk_left hD

/-- The prepared law of a set inside one world. -/
theorem preparedResidualLaw_single (μ : Fin W → Measure X) (ω : Fin W → ℝ) (H : Fin W → Set X)
    (w₀ : Fin W) {D : Set (Fin W × X)} (hD : MeasurableSet D) (hDw : ∀ z ∈ D, z.1 = w₀) :
    preparedResidualLaw μ ω H D =
      ENNReal.ofReal (ω w₀) * μ w₀ (H w₀ ∩ worldSection w₀ D) /
        (∑ w, ENNReal.ofReal (ω w) * μ w (H w)) := by
  rw [preparedResidualLaw_apply μ ω H D hD]
  congr 1
  rw [Finset.sum_eq_single w₀]
  · rfl
  · intro w _ hw
    have hempty : H w ∩ {x | (w, x) ∈ D} = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro _ hx
      exact hw (hDw _ hx)
    rw [hempty, measure_empty, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ w₀) h

theorem worldSection_inter (w₀ : Fin W) (C D : Set (Fin W × X)) :
    worldSection w₀ (C ∩ D) = worldSection w₀ C ∩ worldSection w₀ D := rfl

/-- The coarse law of a single-world support, on any measurable set: the original world
measure of `H ∩ C ∩ D` over that of `H ∩ C`. -/
theorem cond_preparedResidualLaw_single (μ : Fin W → Measure X) (ω : Fin W → ℝ)
    (H : Fin W → Set X) (w₀ : Fin W) (hω : 0 < ω w₀)
    (hZ : (∑ w, ENNReal.ofReal (ω w) * μ w (H w)) ≠ ⊤)
    {C : Set (Fin W × X)} (hC : MeasurableSet C) (hCw : ∀ z ∈ C, z.1 = w₀)
    (hfin : μ w₀ (H w₀ ∩ worldSection w₀ C) ≠ ⊤)
    {D : Set (Fin W × X)} (hD : MeasurableSet D) :
    ProbabilityTheory.cond (preparedResidualLaw μ ω H) C D =
      (μ w₀ (H w₀ ∩ worldSection w₀ C))⁻¹ * μ w₀ (H w₀ ∩ worldSection w₀ C ∩ worldSection w₀ D) := by
  set Z := ∑ w, ENNReal.ofReal (ω w) * μ w (H w)
  set mC := μ w₀ (H w₀ ∩ worldSection w₀ C)
  set mCD := μ w₀ (H w₀ ∩ worldSection w₀ C ∩ worldSection w₀ D)
  rw [ProbabilityTheory.cond_apply hC]
  have hCD : ∀ z ∈ C ∩ D, z.1 = w₀ := fun z hz => hCw z hz.1
  rw [preparedResidualLaw_single μ ω H w₀ hC hCw,
    preparedResidualLaw_single μ ω H w₀ (hC.inter hD) hCD, worldSection_inter, ← inter_assoc]
  have hω0 : ENNReal.ofReal (ω w₀) ≠ 0 := by simpa using hω
  have hωtop : ENNReal.ofReal (ω w₀) ≠ ⊤ := ENNReal.ofReal_ne_top
  by_cases hZ0 : Z = 0
  · -- then every world mass vanishes, in particular `mC = 0 = mCD`
    have hmC : ENNReal.ofReal (ω w₀) * μ w₀ (H w₀) = 0 := by
      have := Finset.single_le_sum (f := fun w => ENNReal.ofReal (ω w) * μ w (H w))
        (fun _ _ => bot_le) (Finset.mem_univ w₀)
      exact le_antisymm (this.trans hZ0.le) bot_le
    have hH0 : μ w₀ (H w₀) = 0 := by
      rcases mul_eq_zero.mp hmC with h | h
      · exact absurd h hω0
      · exact h
    have h1 : mC = 0 := measure_mono_null inter_subset_left hH0
    have h2 : mCD = 0 := measure_mono_null (inter_subset_left.trans inter_subset_left) hH0
    have e : μ w₀ (H w₀ ∩ worldSection w₀ C ∩ worldSection w₀ D) = 0 := h2
    rw [e, mul_zero, ENNReal.zero_div, mul_zero]
    show (0 : ℝ≥0∞) = mC⁻¹ * mCD
    rw [h2, mul_zero]
  · rw [div_eq_mul_inv, div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr hZ0)) (Or.inr (ENNReal.inv_ne_zero.mpr hZ)),
      ENNReal.mul_inv (Or.inl hω0) (Or.inl hωtop), inv_inv]
    calc (ENNReal.ofReal (ω w₀))⁻¹ * mC⁻¹ * Z * (ENNReal.ofReal (ω w₀) * mCD * Z⁻¹)
        = ((ENNReal.ofReal (ω w₀))⁻¹ * ENNReal.ofReal (ω w₀)) * (Z * Z⁻¹) * (mC⁻¹ * mCD) := by
          ring
      _ = mC⁻¹ * mCD := by
          rw [ENNReal.inv_mul_cancel hω0 hωtop, ENNReal.mul_inv_cancel hZ0 hZ, one_mul, one_mul]

/-- Ratio inequalities of the coarse law are ratio inequalities of the original world
measure on `H ∩ C`. -/
theorem world_ratio_of_cond_ratio (μ : Fin W → Measure X) (ω : Fin W → ℝ)
    (H : Fin W → Set X) (w₀ : Fin W) (hω : 0 < ω w₀)
    (hZ : (∑ w, ENNReal.ofReal (ω w) * μ w (H w)) ≠ ⊤)
    {C : Set (Fin W × X)} (hC : MeasurableSet C) (hCw : ∀ z ∈ C, z.1 = w₀)
    (hfin : μ w₀ (H w₀ ∩ worldSection w₀ C) ≠ ⊤)
    (hpos : μ w₀ (H w₀ ∩ worldSection w₀ C) ≠ 0)
    {D₁ D₂ : Set (Fin W × X)} (hD₁ : MeasurableSet D₁) (hD₂ : MeasurableSet D₂) (t : ℝ≥0∞)
    (h : ProbabilityTheory.cond (preparedResidualLaw μ ω H) C D₁ ≤
      t * ProbabilityTheory.cond (preparedResidualLaw μ ω H) C D₂) :
    μ w₀ (H w₀ ∩ worldSection w₀ C ∩ worldSection w₀ D₁) ≤
      t * μ w₀ (H w₀ ∩ worldSection w₀ C ∩ worldSection w₀ D₂) := by
  rw [cond_preparedResidualLaw_single μ ω H w₀ hω hZ hC hCw hfin hD₁,
    cond_preparedResidualLaw_single μ ω H w₀ hω hZ hC hCw hfin hD₂] at h
  set mC := μ w₀ (H w₀ ∩ worldSection w₀ C)
  have hinv0 : mC⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr hfin
  have hinvtop : mC⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hpos
  have h' : mC⁻¹ * μ w₀ (H w₀ ∩ worldSection w₀ C ∩ worldSection w₀ D₁) ≤
      mC⁻¹ * (t * μ w₀ (H w₀ ∩ worldSection w₀ C ∩ worldSection w₀ D₂)) := by
    calc _ ≤ t * (mC⁻¹ * μ w₀ (H w₀ ∩ worldSection w₀ C ∩ worldSection w₀ D₂)) := h
      _ = _ := by ring
  have h'' := mul_le_mul_right h' mC
  rwa [← mul_assoc, ← mul_assoc, ENNReal.mul_inv_cancel hpos hfin, one_mul, one_mul] at h''

/-- Real-valued form: a real ratio inequality of the coarse law gives the same inequality for
the original world measure on `H ∩ C`. -/
theorem world_ratio_of_cond_ratio_real (μ : Fin W → Measure X) (ω : Fin W → ℝ)
    (H : Fin W → Set X) (w₀ : Fin W) (hω : 0 < ω w₀)
    (hZ : (∑ w, ENNReal.ofReal (ω w) * μ w (H w)) ≠ ⊤)
    {C : Set (Fin W × X)} (hC : MeasurableSet C) (hCw : ∀ z ∈ C, z.1 = w₀)
    (hfin : μ w₀ (H w₀ ∩ worldSection w₀ C) ≠ ⊤)
    (hpos : μ w₀ (H w₀ ∩ worldSection w₀ C) ≠ 0)
    {D₁ D₂ : Set (Fin W × X)} (hD₁ : MeasurableSet D₁) (hD₂ : MeasurableSet D₂) {c : ℝ}
    (hc : 0 ≤ c)
    (h : (ProbabilityTheory.cond (preparedResidualLaw μ ω H) C).real D₁ ≤
      c * (ProbabilityTheory.cond (preparedResidualLaw μ ω H) C).real D₂) :
    μ w₀ (H w₀ ∩ worldSection w₀ C ∩ worldSection w₀ D₁) ≤
      ENNReal.ofReal c * μ w₀ (H w₀ ∩ worldSection w₀ C ∩ worldSection w₀ D₂) := by
  set κ := ProbabilityTheory.cond (preparedResidualLaw μ ω H) C
  have hfinκ : ∀ D, κ D ≠ ⊤ := by
    intro D
    have : IsFiniteMeasure κ := by unfold κ; infer_instance
    exact measure_ne_top κ D
  apply world_ratio_of_cond_ratio μ ω H w₀ hω hZ hC hCw hfin hpos hD₁ hD₂
  rw [← ENNReal.ofReal_toReal (hfinκ D₁), ← ENNReal.ofReal_toReal (hfinκ D₂),
    ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal h

end

end Forward

end Submission.Obl.k4_isotropic_path_improvement.S294
