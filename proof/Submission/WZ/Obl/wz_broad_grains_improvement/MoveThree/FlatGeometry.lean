-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.FlatGeometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/FlatGeometry.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
/- Adapted from internal o169/x0641, commit 707550d, FlatGeometry.lean
   (x0670 first-filling chain, building on x0551 geometry). -/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.NaturalTubes
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainAxes
import Submission.WZ.Obl.wz_flat_cluster_slab_filling.Geometry

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree

open Set Metric MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (boxAxis boxAxis_norm inner_boxAxis)
open WangZahlLot.Obl.wz_affine_robust_cluster_estimate
  (unit norm_unit norm_smul_unit pd pd_triangle pd_symm pd_isometry)

/-- A chord of definite length inside a slab has a nearly tangential unit direction. -/
theorem chord_unit_inner_bound {r t : ℝ} {u x v : V}
    (hv : (1 / 4 : ℝ) ≤ ‖v‖)
    (hx : |inner ℝ u x - t| ≤ r) (hy : |inner ℝ u (x + v) - t| ≤ r) :
    |inner ℝ u (unit v)| ≤ 8 * r := by
  have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
  have h0 := (abs_le.mp hx)
  have h1 := (abs_le.mp hy)
  simp only [inner_add_right] at h1
  have hdir : |inner ℝ u v| ≤ 2 * r := abs_le.mpr ⟨by linarith, by linarith⟩
  have he : ‖v‖ * |inner ℝ u (unit v)| = |inner ℝ u v| := by
    rw [← abs_of_nonneg (norm_nonneg v), ← abs_mul, ← inner_smul_right, norm_smul_unit hv0]
  have hn := mul_le_mul_of_nonneg_right hv (abs_nonneg (inner ℝ u (unit v)))
  rw [he] at hn
  linarith

/-- Extending a definite chord to unit length only multiplies its containing
slab's half-width by an absolute constant. -/
theorem chord_unit_tube_slab {δ r t : ℝ} {u x v : V}
    (hu : ‖u‖ = 1) (hv : (1 / 4 : ℝ) ≤ ‖v‖)
    (hx : |inner ℝ u x - t| ≤ r) (hy : |inner ℝ u (x + v) - t| ≤ r) :
    T δ (x + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • unit v) (unit v) ⊆
      {p | |inner ℝ u p - t| ≤ δ + 5 * r} := by
  have hr : 0 ≤ r := (abs_nonneg _).trans hx
  have hdir := chord_unit_inner_bound hv hx hy
  have hcenter : |inner ℝ u (x + (1 / 2 : ℝ) • v) - t| ≤ r := by
    rw [abs_le] at hx hy ⊢
    simp only [inner_add_right, inner_smul_right] at hy ⊢
    constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
  intro p hp
  obtain ⟨s, hs, hdist⟩ := WangZahlLot.Obl.wz_flat_cluster_slab_filling.tube_point' hp
  let o := x + (1 / 2 : ℝ) • v
  let q := o + (s - 1 / 2) • unit v
  have heq : x + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • unit v + s • unit v = q := by
    dsimp [q, o]
    module
  rw [heq] at hdist
  have hsabs : |s - 1 / 2| ≤ (1 / 2 : ℝ) := abs_le.mpr ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have herror : |inner ℝ u (p - q)| < δ := by
    calc |inner ℝ u (p - q)| ≤ ‖u‖ * ‖p - q‖ := abs_real_inner_le_norm _ _
      _ = ‖p - q‖ := by rw [hu, one_mul]
      _ < δ := hdist
  have hq : |inner ℝ u q - t| ≤ 5 * r := by
    have he : inner ℝ u q - t = (inner ℝ u o - t) + (s - 1 / 2) * inner ℝ u (unit v) := by
      dsimp [q]
      rw [inner_add_right, inner_smul_right]
      ring
    rw [he]
    calc _ ≤ |inner ℝ u o - t| + |(s - 1 / 2) * inner ℝ u (unit v)| := abs_add_le _ _
      _ = |inner ℝ u o - t| + |s - 1 / 2| * |inner ℝ u (unit v)| := by rw [abs_mul]
      _ ≤ r + (1 / 2 : ℝ) * (8 * r) := by
        exact add_le_add hcenter (mul_le_mul hsabs hdir (abs_nonneg _) (by norm_num))
      _ = 5 * r := by ring
  have he : inner ℝ u p - t = inner ℝ u (p - q) + (inner ℝ u q - t) := by
    rw [inner_sub_right]
    ring
  change |inner ℝ u p - t| ≤ _
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

/-- Unit extensions of chords in one thin prism remain in a common slab. -/
theorem chord_in_prism_slab {δ a b c : ℝ} {x v z : V} (e : V ≃ₗᵢ[ℝ] V)
    (hv : (1 / 4 : ℝ) ≤ ‖v‖) (hx : x ∈ P a b c z e) (hy : x + v ∈ P a b c z e) :
    T δ (x + (1 / 2 : ℝ) • v - (1 / 2 : ℝ) • unit v) (unit v) ⊆
      {p | |inner ℝ (boxAxis e 0) p - inner ℝ (boxAxis e 0) z| ≤ δ + 5 * (a / 2)} := by
  apply chord_unit_tube_slab (boxAxis_norm e 0) hv
  · rw [← inner_sub_right, inner_boxAxis]; exact hx.1
  · rw [← inner_sub_right, inner_boxAxis]; exact hy.1

/-- Chords in one flat prism have unit directions in a cap controlled by the
middle side length. -/
theorem chord_in_prism_angle {a b c : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {x v z : V} (e : V ≃ₗᵢ[ℝ] V) (hv : (1 / 4 : ℝ) ≤ ‖v‖)
    (hx : x ∈ P a b c z e) (hy : x + v ∈ P a b c z e) :
    pd (unit v) (boxAxis e 2) ≤ 12 * b := by
  have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
  have hcoord (j : Fin 3) (d : ℝ) (hxj : |e (x - z) j| ≤ d / 2)
      (hyj : |e (x + v - z) j| ≤ d / 2) : |e (unit v) j| ≤ 4 * d := by
    have hh := chord_unit_inner_bound (x := x) (r := d / 2) hv
      (u := boxAxis e j) (t := inner ℝ (boxAxis e j) z)
      (by rw [← inner_sub_right, inner_boxAxis]; exact hxj)
      (by rw [← inner_sub_right, inner_boxAxis]; exact hyj)
    rw [inner_boxAxis] at hh
    linarith
  have hh := WangZahlLot.Obl.wz_clustered_cover_volume_gain.coordinate_axis_close
    (by linarith : 0 ≤ 4 * b) (by simpa only [e.norm_map] using norm_unit hv0)
    ((hcoord 0 a hx.1 hy.1).trans (by linarith)) (hcoord 1 b hx.2.1 hy.2.1)
  have he : e (boxAxis e 2) = EuclideanSpace.basisFun (Fin 3) ℝ 2 := by simp [boxAxis]
  rw [← he, pd_isometry] at hh
  linarith

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree
