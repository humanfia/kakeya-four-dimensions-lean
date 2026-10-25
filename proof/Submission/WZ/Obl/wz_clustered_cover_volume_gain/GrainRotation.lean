-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.GrainRotation.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.PrismGeometry
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AxisBounds

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate (pd pd_isometry)

def rotatedFrame (R e : V ≃ₗᵢ[ℝ] V) : V ≃ₗᵢ[ℝ] V := R.symm.trans e

lemma rotatedFrame_apply (R e : V ≃ₗᵢ[ℝ] V) (p : V) : rotatedFrame R e (R p) = e p := by
  simp [rotatedFrame]

lemma rotated_boxAxis (R e : V ≃ₗᵢ[ℝ] V) (j : Fin 3) :
    boxAxis (rotatedFrame R e) j = R (boxAxis e j) := rfl

lemma rotated_prism (R e : V ≃ₗᵢ[ℝ] V) (a b c : ℝ) (z : V) :
    R '' P a b c z e = P a b c (R z) (rotatedFrame R e) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simpa only [P, ι, Set.mem_ofPred_eq, ← map_sub, rotatedFrame_apply] using hq
  · intro hp
    refine ⟨R.symm p, ?_, R.apply_symm_apply p⟩
    simpa only [P, ι, Set.mem_ofPred_eq, rotatedFrame, LinearIsometryEquiv.trans_apply,
      map_sub, R.symm_apply_apply] using hp

lemma rotation_volume (R : V ≃ₗᵢ[ℝ] V) (Q : Set V) : volume (R '' Q) = volume Q := by
  have he : R '' Q = R.symm ⁻¹' Q := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      simpa using hq
    · intro hp
      exact ⟨R.symm p, hp, R.apply_symm_apply p⟩
  rw [he]
  exact R.symm.measurePreserving.measure_preimage_emb R.symm.toHomeomorph.measurableEmbedding Q

lemma rotated_local_grain_count {L : ℕ} {a ρ c m : ℝ}
    (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (R : V ≃ₗᵢ[ℝ] V)
    (hlocal : ∀ j W, Convex ℝ W →
      O (q L {j' | P (a / ρ) c c (z j') (e j') ⊆
        P (2 * a / ρ) (2 * c) (2 * c) (z j) (e j) ∧
        P a (ρ * c) c (z j') (e j') ⊆ W} * (a * (ρ * c) * c)) ≤ O m * μ W) :
    ∀ j W, Convex ℝ W →
      O (q L {j' | P (a / ρ) c c (R (z j')) (rotatedFrame R (e j')) ⊆
        P (2 * a / ρ) (2 * c) (2 * c) (R (z j)) (rotatedFrame R (e j)) ∧
        P a (ρ * c) c (R (z j')) (rotatedFrame R (e j')) ⊆ W} * (a * (ρ * c) * c)) ≤ O m * μ W := by
  intro j W hW
  have hh := hlocal j (R ⁻¹' W) (hW.linear_preimage R.toLinearEquiv.toLinearMap)
  have hvol : μ (R ⁻¹' W) = μ W := by
    change volume (R ⁻¹' W) = volume W
    rw [← rotation_volume R (R ⁻¹' W), R.surjective.image_preimage]
  rw [hvol] at hh
  convert hh using 1
  congr 3
  ext k
  simp only [Set.mem_ofPred_eq]
  rw [← rotated_prism, ← rotated_prism, ← rotated_prism]
  simp only [ Set.image_subset_image_iff R.injective, Set.image_subset_iff]

/-- All three normalized axis bounds follow from the frozen alignment
condition and coordinate bounds on the parent direction. -/
lemma frozen_coarse_axis_bounds {θ ρ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hρ : 0 ≤ ρ) (hρθ : ρ ≤ θ) (e : V ≃ₗᵢ[ℝ] V) (w : V)
    (hw : ‖w‖ = 1) (hw0 : |w 0| ≤ θ) (hw1 : |w 1| ≤ θ)
    (halign : (e w 0) ^ 2 + (e w 1) ^ 2 ≤ (10 * ρ) ^ 2) :
    ‖dualLinear θ (boxAxis e 0)‖ ≤ 25 * θ ∧
    ‖dualLinear θ (boxAxis e 1)‖ ≤ 25 * θ ∧
    ‖coarseLinear θ (boxAxis e 2)‖ ≤ 43 := by
  have hangle := grain_axis_close hρ e hw halign
  have h0 := coarse_grain_axis_bounds hθ hθ1 hρθ (boxAxis_norm e 0) (boxAxis_norm e 2)
    hw (by simpa only [← frozenBasis_apply] using (frozenBasis e).orthonormal.inner_eq_zero (by decide : (0 : Fin 3) ≠ 2))
    hangle hw0 hw1
  have h1 := coarse_grain_axis_bounds hθ hθ1 hρθ (boxAxis_norm e 1) (boxAxis_norm e 2)
    hw (by simpa only [← frozenBasis_apply] using (frozenBasis e).orthonormal.inner_eq_zero (by decide : (1 : Fin 3) ≠ 2))
    hangle hw0 hw1
  exact ⟨h0.2, h1.2, h0.1⟩

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
