-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_robust_cluster_estimate.Tubes.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_affine_robust_cluster_estimate.Geometry

namespace WangZahlLot.Obl.wz_affine_robust_cluster_estimate
open MeasureTheory Set Metric
open scoped ENNReal
noncomputable section

/-- Extend a segment of length at most one symmetrically about its center. -/
theorem image_segment_extend (F : E ≃ᴬ[ℝ] E) (x v u : E) {l : ℝ}
    (hl : 0 ≤ l) (hl1 : l ≤ 1) (hvec : F.toAffineEquiv.linear v = l • u) :
    F '' segment ℝ x (x + v) ⊆
      segment ℝ (F (x + (1 / 2 : ℝ) • v) - (1 / 2 : ℝ) • u)
        (F (x + (1 / 2 : ℝ) • v) - (1 / 2 : ℝ) • u + u) := by
  rintro _ ⟨p, hp, rfl⟩
  rw [segment_eq_image'] at hp ⊢
  obtain ⟨s, hs, rfl⟩ := hp
  simp only [add_sub_cancel_left]
  refine ⟨1 / 2 + (s - 1 / 2) * l, ⟨?_, ?_⟩, ?_⟩
  · nlinarith [mul_nonneg hs.1 hl]
  · nlinarith [mul_nonneg (show 0 ≤ 1 - s by linarith [hs.2]) hl]
  · have he (t : ℝ) : F (x + t • v) = (t * l) • u + F x := by
      rw [add_comm]
      change F.toAffineEquiv (t • v +ᵥ x) = _
      rw [F.toAffineEquiv.map_vadd, map_smul, hvec]
      simp only [vadd_eq_add, smul_smul]
      rfl
    rw [he, he]
    module

/-- Extending the image segment gives a round tube containing the image of the old tube. -/
theorem image_tube_extend (F : E ≃ᴬ[ℝ] E) (x v u : E) {δ l A : ℝ}
    (hA : 0 < A) (hl : 0 ≤ l) (hl1 : l ≤ 1)
    (hvec : F.toAffineEquiv.linear v = l • u)
    (hLip : ∀ p q, dist (F p) (F q) ≤ A * dist p q) :
    F '' tube δ x v ⊆ tube (A * δ)
      (F (x + (1 / 2 : ℝ) • v) - (1 / 2 : ℝ) • u) u := by
  rintro _ ⟨p, hp, rfl⟩
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  apply mem_thickening_iff.mpr
  refine ⟨F q, image_segment_extend F x v u hl hl1 hvec ⟨q, hq, rfl⟩, ?_⟩
  exact (hLip p q).trans_lt (mul_lt_mul_of_pos_left hpq hA)

/-- A unit tube with center near the origin lies in the unit ball. -/
theorem centered_tube_subset_ball {q u : E} (hu : ‖u‖ = 1) (hq : ‖q‖ ≤ 1 / 4)
    {δ : ℝ} (hδ : δ ≤ 1 / 100) :
    tube δ (q - (1 / 2 : ℝ) • u) u ⊆ ball (0 : E) 1 := by
  intro p hp
  obtain ⟨a, ha, hpa⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at ha
  obtain ⟨s, hs, rfl⟩ := ha
  simp only [add_sub_cancel_left] at hpa
  have hs' : |s - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hnorm : ‖q - (1 / 2 : ℝ) • u + s • u‖ ≤ 3 / 4 := by
    have he : q - (1 / 2 : ℝ) • u + s • u = q + (s - 1 / 2) • u := by module
    rw [he]
    have hn := norm_add_le q ((s - 1 / 2) • u)
    rw [norm_smul, Real.norm_eq_abs, hu, mul_one] at hn
    linarith
  have hn := norm_le_norm_add_norm_sub (q - (1 / 2 : ℝ) • u + s • u) p
  rw [norm_sub_rev, ← dist_eq_norm] at hn
  rw [mem_ball_zero_iff]
  linarith

end
end WangZahlLot.Obl.wz_affine_robust_cluster_estimate
