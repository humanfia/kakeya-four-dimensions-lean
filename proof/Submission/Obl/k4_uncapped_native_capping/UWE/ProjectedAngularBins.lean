/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/ProjectedAngularBins.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/ProjectedAngularBins.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.AngularPairBins
import Submission.Obl.k4_scalar_coefficient_clustering.Geometry
import Submission.Obl.k4_plank_projected_multiplicity.DirectionPacking

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set

/-- A scalar tangent-velocity bin inside the common thin normal strip meets
only polynomially many ORIGINAL two-coordinate angular bins. -/
theorem tangent_velocity_bins
    (e n : EuclideanSpace ℝ (Fin 2)) (he : ‖e‖ = 1) (hn : ‖n‖ = 1)
    (hen : inner ℝ e n = 0) (β : ℝ) {K g a δ : ℝ}
    (hK : 1 ≤ K) (hg : 0 ≤ g) (hga : g ≤ a) (ha : 0 < a) (haδ : a ≤ δ) (j : ℤ) :
    ∃ V : Finset (Fin 2 → ℤ), (V.card : ℝ) ≤ (8 * K + 2) ^ 2 ∧
      ∀ v : EuclideanSpace ℝ (Fin 2), |inner ℝ n v - β| ≤ K * g →
        ⌊inner ℝ e v / a⌋ = j → (fun i => ⌊v i / δ⌋) ∈ V := by
  let S : Set (EuclideanSpace ℝ (Fin 2)) :=
    {v | |inner ℝ n v - β| ≤ K * g ∧ ⌊inner ℝ e v / a⌋ = j}
  have hK0 : 0 ≤ K := by linarith only [hK]
  have hδ : 0 < δ := ha.trans_le haδ
  obtain ⟨V, hV, hmem⟩ := planar_diameter_bins S
    (by positivity : 0 ≤ 4 * K * a) hδ (by
      intro v hv v' hv'
      have hE : |inner ℝ (v - v') e| ≤ a := by
        have h := Submission.Obl.k4_plank_projected_multiplicity.abs_sub_le_mesh_of_floor_eq
          ha (hv.2.trans hv'.2.symm)
        simpa only [inner_sub_left, real_inner_comm] using h
      have hN : |inner ℝ (v - v') n| ≤ 2 * K * g := by
        calc
          _ = |(inner ℝ n v - β) - (inner ℝ n v' - β)| := by
            congr 1
            rw [inner_sub_left, real_inner_comm v n, real_inner_comm v' n]
            ring
          _ ≤ |inner ℝ n v - β| + |inner ℝ n v' - β| := abs_sub _ _
          _ ≤ 2 * K * g := by linarith only [hv.1, hv'.1]
      have hE' : |inner ℝ (v - v') e| ≤ 2 * K * a := hE.trans (by nlinarith)
      have hN' : |inner ℝ (v - v') n| ≤ 2 * K * a := hN.trans (by gcongr)
      have hnorm := Submission.Obl.k4_scalar_coefficient_clustering.plane_norm_le_two_mul
        he hn hen hE' hN'
      rw [dist_eq_norm]
      exact hnorm.trans_eq (by ring))
  refine ⟨V, hV.trans ?_, fun v hv hj => hmem v ⟨hv, hj⟩⟩
  have hratio : 2 * (4 * K * a) / δ + 2 ≤ 8 * K + 2 := by
    have hdiv : 2 * (4 * K * a) / δ ≤ 8 * K := (div_le_iff₀ hδ).2 (by
      nlinarith [mul_le_mul_of_nonneg_left haδ (show 0 ≤ 8 * K by positivity)])
    linarith only [hdiv]
  exact (sq_le_sq₀ (by positivity) (by positivity)).2 hratio

end Submission.Obl.k4_uncapped_native_capping.UWE
