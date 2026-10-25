-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.BoundedOriginalCarriers, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.OriginalParameterEntryPruning
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Basic
import Submission.Lib.K4ContinuousPlanks.Discretization

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Set

/-- Bounded original coefficients give the actual finite coefficient
carrier at every positive mesh; no finite trajectory model is needed. -/
theorem finite_original_parameter_image_of_bounded {Λ : Type*}
    (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ)) {H w : ℝ} (hw : 0<w)
    (hcoeff : ∀ z∈E, ∀ j, |c z.1 j|≤H) :
    ((fun z : Λ × ℝ => parameterCode w (c z.1)) '' E).Finite := by
  have hf := Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
    (fun z : E => c z.val.1) H (fun z j => hcoeff z.val z.property j) hw
  apply hf.subset
  rintro q ⟨z,hz,rfl⟩
  exact ⟨⟨z,hz⟩,rfl⟩

/-- The original scalar physical state has a finite carrier on bounded
unit-time incidences, at every positive physical mesh. -/
theorem finite_original_fine_state_image_of_bounded {Λ : Type*}
    (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ)) {H b : ℝ} (hH : 1≤H) (hb : 0<b)
    (ht : ∀ z∈E, z.2∈Icc (0:ℝ) 1)
    (hcoeff : ∀ z∈E, ∀ j, |c z.1 j|≤H) :
    (originalFineState c b '' E).Finite := by
  have hbound : ∀ z : E, ∀ j, |zpos (c z.val.1) z.val.2 j|≤3*H := by
    intro z j
    fin_cases j
    · change |z.val.2|≤3*H
      rw [abs_of_nonneg (ht z.val z.property).1]
      linarith [(ht z.val z.property).2]
    · exact abs_zx_le (hcoeff z.val z.property) (ht z.val z.property)
    · exact (abs_zy_le (hcoeff z.val z.property) (ht z.val z.property) 0).trans (by linarith)
    · exact (abs_zy_le (hcoeff z.val z.property) (ht z.val z.property) 1).trans (by linarith)
  have hf := Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
    (fun z : E => zpos (c z.val.1) z.val.2) (3*H) hbound hb
  apply hf.subset
  rintro q ⟨z,hz,rfl⟩
  exact ⟨⟨z,hz⟩,rfl⟩

/-- The tagged original zoom carrier is finite on the same actual
incidences; it keeps both the coarse and fine full-original bins. -/
theorem finite_original_zoom_block_image_of_bounded {Λ : Type*}
    (c : Λ → Fin 7 → ℝ) (E : Set (Λ × ℝ)) {H ρ : ℝ} (hρ : 0<ρ)
    (hcoeff : ∀ z∈E, ∀ j, |c z.1 j|≤H) (n : ℕ) :
    ((fun z : Λ × ℝ => originalZoomBlock c ρ (dyadicParameterWidth n) z.1) '' E).Finite := by
  exact original_zoom_blocks_finite_of_fine c E hρ n
    (finite_original_parameter_image_of_bounded c E (mul_pos hρ (dyadicParameterWidth_pos n)) hcoeff)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
