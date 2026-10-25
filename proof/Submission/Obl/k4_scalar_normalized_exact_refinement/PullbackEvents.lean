import Submission.Obl.k4_scalar_normalized_exact_refinement.PolynomialCoordinates
import Submission.Obl.k4_scalar_normalized_exact_refinement.RawNumerics
import Submission.Obl.k4_scalar_conditional_crop_worlds.FormatLemmas

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_normalized_exact_refinement

open MeasureTheory Set
open k4_scalar_linear_critical_extremizers.Split

noncomputable section

/-- Restricting a transported law is exactly transport of the selected
preimage event. The conditioning budget is unchanged. -/
lemma restrict_transported_selected {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (C : Set X) (f : X → Y) (hf : Measurable f)
    (a : ENNReal) (F : Set Y) (hF : MeasurableSet F) :
    (a • (μ.restrict C).map f).restrict F =
      a • (μ.restrict (C ∩ f ⁻¹' F)).map f := by
  rw [Measure.restrict_smul, Measure.restrict_map hf hF,
    Measure.restrict_restrict (hf hF), inter_comm]

/-- The selected preimage of a formatted normalized event has a uniform
polynomial format in the original incidence coordinates. -/
lemma formatted_chart_pullback {N : ℝ} {B M D B' : ℕ}
    (hN : 2 ≤ N) (hcount : max (B : ℝ) (M : ℝ) + 1 ≤ (B' : ℝ))
    (hdeg : max B (2 * D) ≤ B')
    (C F : Set (Line × ℝ))
    (hC : ∀ label, Format 6 (N ^ (B : ℝ)) B {a | coefficientState label a ∈ C})
    (hF : ∀ label, Format 6 (N ^ (M : ℝ)) D {a | coefficientState label a ∈ F})
    (P : MvPolynomial (Fin 2) ℝ) (hP : P.totalDegree ≤ 2)
    (t₀ dt u v J δ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (hδ : δ ≠ 0) :
    ∀ label, Format 6 (N ^ (B' : ℝ)) B'
      {a | coefficientState label a ∈ C ∩
        (fun z : Line × ℝ => (normalizeLine P t₀ dt u v J δ z.1, (z.2 - t₀) / dt)) ⁻¹' F} := by
  intro label
  have hN1 : 1 ≤ N := by linarith
  have hR : 1 ≤ N ^ (M : ℝ) := Real.one_le_rpow hN1 (Nat.cast_nonneg _)
  have hp := format_incidence_normalization_preimage label (hF label) hR P hP
    t₀ dt u v J δ hdt hJ hδ
  have he : ⇑((normalizeEquiv P hP t₀ dt u v J δ hdt hJ hδ).prodCongr
      (timeEquiv t₀ dt hdt)) =
      (fun z : Line × ℝ => (normalizeLine P t₀ dt u v J δ z.1, (z.2 - t₀) / dt)) := by
    funext z
    apply Prod.ext
    · exact normalizeEquiv_apply ..
    · exact timeEquiv_apply ..
  rw [he] at hp
  have hC' : k4_scalar_conditional_crop_worlds.Format 6 (N ^ (B : ℝ)) (max B (2 * D))
      {a | coefficientState label a ∈ C} :=
    k4_scalar_conditional_crop_worlds.Format.mono (hC label) le_rfl (le_max_left _ _)
  have hF' : k4_scalar_conditional_crop_worlds.Format 6 (N ^ (M : ℝ)) (max B (2 * D))
      {a | coefficientState label a ∈
        (fun z : Line × ℝ => (normalizeLine P t₀ dt u v J δ z.1, (z.2 - t₀) / dt)) ⁻¹' F} :=
    k4_scalar_conditional_crop_worlds.Format.mono hp le_rfl (le_max_right _ _)
  exact k4_scalar_conditional_crop_worlds.Format.mono
    (k4_scalar_conditional_crop_worlds.Format.inter hC' hF')
    ((normalization_format_count_bound hN).trans
      (Real.rpow_le_rpow_of_exponent_le hN1 hcount)) hdeg

end

end Submission.Obl.k4_scalar_normalized_exact_refinement
