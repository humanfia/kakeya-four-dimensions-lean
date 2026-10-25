import Submission.Obl.k4_scalar_candidate_original_return.ObservationTransfer
import Submission.Lib.K4ModelReduction.FiniteTable

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_candidate_original_return

open MeasureTheory Set
open Submission.Lib.K4ModelReduction

noncomputable section

/-- Finite actual records, allowing a different width for the original hidden tag. -/
def originalRecordCodes (R ρ δ : ℝ) : Finset (Fin 3 → ℤ) :=
  meshCodes (Fin 3) 1 (max (R / ρ) (R / δ))

lemma rawObservation_tag_mem {R ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (w : Fin 6 → ℝ) (hw : ∀ i, |w i| ≤ R) :
    observationMeshTag ρ (rawObservation δ w) ∈ originalRecordCodes R ρ δ := by
  let z : Fin 3 → ℝ := ![w 0 / ρ, w 1 / ρ, w 3 / δ]
  have hz (i : Fin 3) : |z i| ≤ max (R / ρ) (R / δ) := by
    fin_cases i
    · change |w 0 / ρ| ≤ max (R / ρ) (R / δ)
      simpa only [abs_div, abs_of_pos hρ] using
        (div_le_div_of_nonneg_right (hw 0) hρ.le).trans (le_max_left (R / ρ) (R / δ))
    · change |w 1 / ρ| ≤ max (R / ρ) (R / δ)
      simpa only [abs_div, abs_of_pos hρ] using
        (div_le_div_of_nonneg_right (hw 1) hρ.le).trans (le_max_left (R / ρ) (R / δ))
    · change |w 3 / δ| ≤ max (R / ρ) (R / δ)
      simpa only [abs_div, abs_of_pos hδ] using
        (div_le_div_of_nonneg_right (hw 3) hδ.le).trans (le_max_right (R / ρ) (R / δ))
  have htag : meshTag 1 z = observationMeshTag ρ (rawObservation δ w) := by
    funext i
    fin_cases i <;> simp [meshTag, z, observationMeshTag, rawObservation]
  rw [← htag]
  exact meshTag_mem_codes (by norm_num) z hz

lemma originalRecordCodes_card {R ρ δ : ℝ} (hR : 0 ≤ R) (hρ : 0 < ρ) (hδ : 0 < δ) :
    ((originalRecordCodes R ρ δ).card : ℝ) ≤
      (2 * max (R / ρ) (R / δ) + 2) ^ 3 := by
  have hmax : 0 ≤ max (R / ρ) (R / δ) :=
    (div_nonneg hR hρ.le).trans (le_max_left _ _)
  simpa [originalRecordCodes] using meshCodes_card_le (ι := Fin 3) (ρ := 1) (by norm_num) hmax

/-- Exact selected source support implies support on a finite set of original
terminal-observation records. No support assumption on an approximating law is needed. -/
theorem original_record_support {R ρ δ : ℝ} (hρ : 0 < ρ) (hδ : 0 < δ)
    (μ : Measure Inc) (C : Set Inc) (f : (Fin 6 → ℝ) → ℝ)
    (hsource : (μ.restrict C).map fullSourceCoordinates =
      volume.withDensity (fun w => ENNReal.ofReal (f w)))
    (hsupport : supportedInCube f R) :
    μ {q | q ∈ C ∧ observationMeshTag ρ (originalObservation δ q) ∉
      originalRecordCodes R ρ δ} = 0 := by
  let F := originalRecordCodes R ρ δ
  let B : Set (Fin 6 → ℝ) := {w | observationMeshTag ρ (rawObservation δ w) ∉ F}
  have hB : MeasurableSet B :=
    ((F.finite_toSet.measurableSet).preimage
      ((measurable_observationMeshTag ρ).comp (measurable_rawObservation δ))).compl
  have hzero : ∀ w ∈ B, f w = 0 := by
    intro w hw
    by_contra hf
    apply hw
    apply rawObservation_tag_mem hρ hδ w
    intro i
    exact le_of_not_gt fun hi => hf (hsupport w i hi)
  have hbad : (volume.withDensity (fun w => ENNReal.ofReal (f w))) B = 0 := by
    rw [withDensity_apply _ hB]
    calc
      _ = ∫⁻ w, (0 : ENNReal) ∂(volume : Measure (Fin 6 → ℝ)).restrict B := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem hB] with w hw
        rw [hzero w hw, ENNReal.ofReal_zero]
      _ = 0 := by simp
  have heq : {q | q ∈ C ∧ observationMeshTag ρ (originalObservation δ q) ∉ F} =
      (fullSourceCoordinates ⁻¹' B) ∩ C := by
    ext q
    change q ∈ C ∧ observationMeshTag ρ (originalObservation δ q) ∉ F ↔
      observationMeshTag ρ (rawObservation δ (fullSourceCoordinates q)) ∉ F ∧ q ∈ C
    have hobs : originalObservation δ q = rawObservation δ (fullSourceCoordinates q) :=
      originalObservation_in_coordinates δ q
    rw [hobs]
    exact and_comm
  change μ {q | q ∈ C ∧ observationMeshTag ρ (originalObservation δ q) ∉ F} = 0
  rw [heq, ← Measure.restrict_apply (hB.preimage measurable_fullSourceCoordinates),
    ← Measure.map_apply measurable_fullSourceCoordinates hB, hsource]
  exact hbad

end

end Submission.Obl.k4_scalar_candidate_original_return
