-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_clustered_cover_volume_gain.RotationRefinement.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainRotation
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.AffineRefinement

noncomputable section

namespace WangZahlLot.Obl.wz_clustered_cover_volume_gain

open Set MeasureTheory Metric
open scoped ENNReal

lemma rotation_ball_inter (R : V ≃ₗᵢ[ℝ] V) (U : Set V) (p : V) (r : ℝ) :
    volume (R '' U ∩ ball (R p) r) = volume (U ∩ ball p r) := by
  have he : R '' U ∩ ball (R p) r = R '' (U ∩ ball p r) := by
    ext q
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hq⟩
      exact ⟨u, ⟨hu, by simpa only [mem_ball, R.dist_map] using hq⟩, rfl⟩
    · rintro ⟨u, ⟨hu, hq⟩, rfl⟩
      exact ⟨⟨u, hu, rfl⟩, by simpa only [mem_ball, R.dist_map] using hq⟩
  rw [he, rotation_volume]

lemma rotation_subset_unit_ball (R : V ≃ₗᵢ[ℝ] V) {U : Set V}
    (hU : U ⊆ ball 0 1) : R '' U ⊆ ball 0 1 := by
  rintro _ ⟨p, hp, rfl⟩
  simpa only [mem_ball, dist_zero_right, R.norm_map] using hU hp

lemma rotation_measurable (R : V ≃ₗᵢ[ℝ] V) {U : Set V} (hU : MeasurableSet U) :
    MeasurableSet (R '' U) := R.toHomeomorph.measurableEmbedding.measurableSet_image.mpr hU

theorem rotation_refinement {n : ℕ} (R : V ≃ₗᵢ[ℝ] V) (Y W : Fin n → Set V)
    {t : ℝ≥0∞} {B : ℝ}
    (hW : ∀ i, MeasurableSet (W i) ∧ W i ⊆ R '' Y i)
    (hmass : t * ∑ i, volume (R '' Y i) ≤ ∑ i, volume (W i))
    (hcount : ∀ p, bodyCount W p ≤ B) :
    ∃ Z : Fin n → Set V, (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      t * ∑ i, volume (Y i) ≤ ∑ i, volume (Z i) ∧
      ∀ p, bodyCount Z p ≤ B := by
  let Z := fun i => R ⁻¹' W i
  refine ⟨Z, fun i => ⟨(hW i).1.preimage R.continuous.measurable, ?_⟩, ?_, ?_⟩
  · intro p hp
    exact R.injective.mem_set_image.mp ((hW i).2 hp)
  · have he (i) : volume (Z i) = volume (W i) := by
      rw [← rotation_volume R (Z i)]
      exact congrArg volume (R.surjective.image_preimage (W i))
    simpa only [rotation_volume, he] using hmass
  · intro p
    exact hcount (R p)

/-- Containment of a unit segment in a box controls its two transverse
direction coordinates, also when the box width is larger than one. -/
lemma parent_direction_coordinates {ρ a b c : ℝ} {y w z : V}
    (R : V ≃ₗᵢ[ℝ] V) (hρ : 0 < ρ) (hab : a ≤ b) (hw : ‖w‖ = 1)
    (hT : T ρ y w ⊆ P a b c z R) :
    |R w 0| ≤ min 1 b ∧ |R w 1| ≤ min 1 b := by
  have hy := hT (self_subset_thickening hρ _ (left_mem_segment ℝ y (y + w)))
  have hyw := hT (self_subset_thickening hρ _ (right_mem_segment ℝ y (y + w)))
  have hcoord (j : Fin 3) : R w j = R (y + w - z) j - R (y - z) j := by
    have he : w = (y + w - z) - (y - z) := by abel
    conv_lhs => rw [he, map_sub]
    rfl
  have hnorm (j : Fin 3) : |R w j| ≤ 1 := by
    simpa only [Real.norm_eq_abs, R.norm_map, hw] using PiLp.norm_apply_le (R w) j
  have hzero : |R w 0| ≤ a := by
    rw [hcoord]
    exact (abs_sub _ _).trans (by linarith [hy.1, hyw.1])
  have hone : |R w 1| ≤ b := by
    rw [hcoord]
    exact (abs_sub _ _).trans (by linarith [hy.2.1, hyw.2.1])
  exact ⟨le_min (hnorm 0) (hzero.trans hab), le_min (hnorm 1) hone⟩

end WangZahlLot.Obl.wz_clustered_cover_volume_gain
