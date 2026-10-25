import Submission.Obl.k4_directional_jet_path_transfer.Assembly
import Submission.Obl.k4_directional_jet_path_transfer.Tube
open Set Metric
namespace Submission.Obl.k4_directional_jet_path_transfer
lemma small_radius {A : ℝ} (hA : 2 ≤ A) : 0 < (8 * A)⁻¹ ∧ (8 * A)⁻¹ ≤ 1 ∧ (8 * A)⁻¹ < A⁻¹ := by
  have hApos : 0 < A := by linarith
  constructor
  · positivity
  constructor
  · exact inv_le_one_of_one_le₀ (by linarith)
  · exact (inv_lt_inv₀ (show 0 < 8 * A by positivity) hApos).mpr (by linarith)
lemma target_displacement_norm_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : ℝ} (hA : 2 ≤ A) {p d z : E} (hp : ‖p‖ ≤ 1) (hd : ‖d‖ ≤ 1)
    (hz : z ∈ closedBall d ((8 * A)⁻¹)) : ‖z - p‖ ≤ 3 := by
  have hz' : ‖z - d‖ ≤ (8 * A)⁻¹ := by simpa [mem_closedBall, dist_eq_norm] using hz
  calc
    ‖z - p‖ = ‖(z - d) + (d - p)‖ := by congr 1; abel
    _ ≤ ‖z - d‖ + ‖d - p‖ := norm_add_le _ _
    _ ≤ (8 * A)⁻¹ + (‖d‖ + ‖p‖) := add_le_add hz' (norm_sub_le _ _)
    _ ≤ 3 := by linarith [(small_radius hA).2.1]

lemma admissibleStep_of_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {A : ℝ} (hA : 2 ≤ A) {S : Set E} {p d : E}
    (hp : ‖p‖ ≤ 1) (hd : ‖d‖ ≤ 1) (hseg : segment ℝ p d ⊆ S) :
    AdmissibleStep A (thickening A⁻¹ S) p d := by
  intro z hz
  refine ⟨target_displacement_norm_le hA hp hd hz, ?_⟩
  have hw0 : ‖z - d‖ ≤ (8 * A)⁻¹ := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hw : ‖z - d‖ ≤ 2 * (8 * A)⁻¹ := by linarith [(small_radius hA).1]
  simpa using slice_mem_thickening hseg hp hd hA hw

end Submission.Obl.k4_directional_jet_path_transfer
