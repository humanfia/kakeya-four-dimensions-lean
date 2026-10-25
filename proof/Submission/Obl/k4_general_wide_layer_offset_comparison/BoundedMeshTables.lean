import Submission.Obl.k4_general_wide_layer_offset_comparison.RawMeshCoupling
import Submission.Lib.K4SignalMeshSupport.Terminal

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/BoundedMeshTables.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set

noncomputable section

/-- Every bounded observed base has a finite literal mesh table, even when
the mesh is larger than the source box. -/
theorem exists_bounded_mesh_table {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) :
    ∃ Q : Finset (Fin 2 → ℤ), ∀ z : Fin 2 → ℝ,
      (∀ i, |z i| ≤ B) → meshCode2 δ z ∈ Q := by
  obtain ⟨Q, hQcard, hQ⟩ := Submission.Lib.K4SignalMeshSupport.planar_moving_mesh_cover
    hδ (by linarith : δ ≤ B + δ) (by norm_num : (0 : ℝ) ≤ 0)
    (by linarith : δ ≤ B + δ) (by nlinarith : 0 * δ ≤ B + δ) 0 0 0 (by norm_num)
  refine ⟨Q, ?_⟩
  intro z hz
  exact hQ z (by simpa only [sub_zero] using (hz 0).trans (by linarith : B ≤ B + δ))
    (by simpa using (hz 1).trans (by linarith : B ≤ B + δ))

/-- A single finite table covers the whole original law; no source event
is chosen or discarded in obtaining it. -/
theorem exists_ae_mesh_table {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (Z : Ω → Fin 2 → ℝ) {δ B : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B)
    (hbound : ∀ᵐ ω ∂μ, ∀ i, |Z ω i| ≤ B) :
    ∃ Q : Finset (Fin 2 → ℤ), ∀ᵐ ω ∂μ, meshCode2 δ (Z ω) ∈ Q := by
  obtain ⟨Q, hQ⟩ := exists_bounded_mesh_table hδ hB
  exact ⟨Q, hbound.mono (fun ω hω => hQ (Z ω) hω)⟩

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
