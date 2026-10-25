-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_coarse_tube_grains.RIS.TubeNormal.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

namespace WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity

open MeasureTheory Set Metric
open LeanEval.Analysis.WangZahlKakeya

/-- Removing the small component along a unit direction and normalizing gives
a nearby unit vector exactly perpendicular to that direction. -/
theorem unit_perpendicular_near {e v : Space} (he : ‖e‖ = 1) (hv : ‖v‖ = 1)
    {q : ℝ} (hq : q < 1) (hinner : |inner ℝ e v| ≤ q) :
    ∃ u : Space, ‖u‖ = 1 ∧ inner ℝ u v = 0 ∧ ‖u - e‖ ≤ 2 * q := by
  let z := e - inner ℝ e v • v
  have hze : ‖z - e‖ ≤ q := by
    rw [show z - e = -(inner ℝ e v • v) by dsimp [z]; abel,
      norm_neg, norm_smul, Real.norm_eq_abs, hv, mul_one]
    exact hinner
  have hnorm : |‖z‖ - 1| ≤ q := by
    rw [← he]
    exact (abs_norm_sub_norm_le z e).trans hze
  have hz : 0 < ‖z‖ := by have := (abs_le.mp hnorm).1; linarith
  let u := ‖z‖⁻¹ • z
  have hu : ‖u‖ = 1 := norm_smul_inv_norm (norm_pos_iff.mp hz)
  have huz : ‖z‖ • u = z := by dsimp [u]; rw [smul_smul, mul_inv_cancel₀ hz.ne', one_smul]
  have hud : ‖u - z‖ ≤ q := by
    rw [show u - z = (1 - ‖z‖) • u by rw [sub_smul, one_smul, huz],
      norm_smul, Real.norm_eq_abs, hu, mul_one, abs_sub_comm]
    exact hnorm
  refine ⟨u, hu, ?_, ?_⟩
  · have hvv : inner ℝ v v = 1 := by rw [real_inner_self_eq_norm_sq, hv]; norm_num
    dsimp [u, z]
    simp only [real_inner_smul_left, inner_sub_left, hvv, mul_one, sub_self, mul_zero]
  · calc
      ‖u - e‖ ≤ ‖u - z‖ + ‖z - e‖ := norm_sub_le_norm_sub_add_norm_sub u z e
      _ ≤ 2 * q := by linarith

/-- A tube with a direction perpendicular to a unit normal is contained in
the corresponding radius-delta slab. -/
theorem tube_subset_normal_slab {δ : ℝ} {x v u : Space}
    (hu : ‖u‖ = 1) (huv : inner ℝ u v = 0) :
    Tube δ x v ⊆ {p | |inner ℝ u p - inner ℝ u x| ≤ δ} := by
  intro p hp
  obtain ⟨q, hq, hpq⟩ := mem_thickening_iff.mp hp
  rw [segment_eq_image'] at hq
  obtain ⟨s, _, rfl⟩ := hq
  simp only [add_sub_cancel_left] at hpq
  have he : inner ℝ u (p - (x + s • v)) = inner ℝ u p - inner ℝ u x := by
    simp only [inner_sub_right, inner_add_right, inner_smul_right, huv, mul_zero, add_zero]
  calc
    |inner ℝ u p - inner ℝ u x| = |inner ℝ u (p - (x + s • v))| := congrArg abs he.symm
    _ ≤ ‖u‖ * ‖p - (x + s • v)‖ := abs_real_inner_le_norm _ _
    _ ≤ δ := by rw [hu, one_mul, ← dist_eq_norm]; exact hpq.le

/-- A unit tube in a thin slab has an exact containing plane close to the
given plane, both in normal and offset. -/
theorem tube_exact_plane_near {δ w t : ℝ} (hδ : 0 < δ) (hw : w < 1 / 2)
    {x v e : Space} (hv : ‖v‖ = 1) (he : ‖e‖ = 1)
    (hball : Tube δ x v ⊆ ball 0 1)
    (hslab : Tube δ x v ⊆ {p | |inner ℝ e p - t| ≤ w}) :
    ∃ (u : Space) (s : ℝ), ‖u‖ = 1 ∧ ‖u - e‖ ≤ 4 * w ∧ |s - t| ≤ 5 * w ∧
      Tube δ x v ⊆ {p | |inner ℝ u p - s| ≤ δ} := by
  have hx : x ∈ Tube δ x v :=
    self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))
  have hxv : x + v ∈ Tube δ x v :=
    self_subset_thickening hδ _ (right_mem_segment ℝ x (x + v))
  have hxw : |inner ℝ e x - t| ≤ w := hslab hx
  have hxvw : |inner ℝ e (x + v) - t| ≤ w := hslab hxv
  have hinner : |inner ℝ e v| ≤ 2 * w := by
    calc
      |inner ℝ e v| = |(inner ℝ e (x + v) - t) - (inner ℝ e x - t)| := by
        rw [inner_add_right]
        congr 1
        ring
      _ ≤ |inner ℝ e (x + v) - t| + |inner ℝ e x - t| := abs_sub _ _
      _ ≤ 2 * w := by linarith
  obtain ⟨u, hu, huv, hue⟩ := unit_perpendicular_near he hv (q := 2 * w) (by linarith) hinner
  have hxnorm : ‖x‖ ≤ 1 := (mem_ball_zero_iff.mp (hball hx)).le
  have hw0 : 0 ≤ w := (abs_nonneg _).trans hxw
  refine ⟨u, inner ℝ u x, hu, by linarith, ?_, tube_subset_normal_slab hu huv⟩
  calc
    |inner ℝ u x - t| = |inner ℝ (u - e) x + (inner ℝ e x - t)| := by
      rw [inner_sub_left]
      congr 1
      ring
    _ ≤ |inner ℝ (u - e) x| + |inner ℝ e x - t| := abs_add_le _ _
    _ ≤ ‖u - e‖ * ‖x‖ + w := add_le_add (abs_real_inner_le_norm _ _) hxw
    _ ≤ (4 * w) * 1 + w := by gcongr <;> linarith
    _ = 5 * w := by ring

/-- Perturbing a containing plane slightly preserves containment in a slab
of twice the tube radius. -/
theorem tube_slab_perturb {δ s t : ℝ} {x v e u : Space}
    (hball : Tube δ x v ⊆ ball 0 1)
    (hslab : Tube δ x v ⊆ {p | |inner ℝ u p - s| ≤ δ})
    (heu : ‖e - u‖ ≤ δ / 4) (hst : |s - t| ≤ δ / 4) :
    Tube δ x v ⊆ {p | |inner ℝ e p - t| ≤ 2 * δ} := by
  intro p hp
  have hpn : ‖p‖ ≤ 1 := (mem_ball_zero_iff.mp (hball hp)).le
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hslab hp)
  calc
    |inner ℝ e p - t| = |inner ℝ (e - u) p + (inner ℝ u p - s) + (s - t)| := by
      rw [inner_sub_left]
      congr 1
      ring
    _ ≤ |inner ℝ (e - u) p| + |inner ℝ u p - s| + |s - t| := abs_add_three _ _ _
    _ ≤ ‖e - u‖ * ‖p‖ + δ + δ / 4 :=
      add_le_add (add_le_add (abs_real_inner_le_norm _ _) (hslab hp)) hst
    _ ≤ (δ / 4) * 1 + δ + δ / 4 := by gcongr
    _ ≤ 2 * δ := by linarith

end WangZahlLot.Obl.wz_coarse_tube_grains.RIS.BrushPlanarity
