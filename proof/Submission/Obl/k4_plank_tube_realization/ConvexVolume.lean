import Mathlib
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.Parent.FactorBox

namespace Submission.Obl.k4_plank_tube_realization.ConvexGeometry

open Set MeasureTheory
open WangZahlLot.Obl.wz_clustered_cover_volume_gain.Parent.Factor

noncomputable section

abbrev Plane := EuclideanSpace ℝ (Fin 2)
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- A convenient coordinate determinant for three spatial vectors. -/
def spatialDet (v : Fin 3 → Space) : ℝ :=
  v 0 0 * v 1 1 * v 2 2 - v 0 0 * v 2 1 * v 1 2 - v 1 0 * v 0 1 * v 2 2 +
    v 1 0 * v 2 1 * v 0 2 + v 2 0 * v 0 1 * v 1 2 - v 2 0 * v 1 1 * v 0 2

/-- Four points in a convex set contain a small parallelepiped. -/
theorem determinant_le_volume {W : Set Space} (hW : Convex ℝ W)
    (p : Space) (q : Fin 3 → Space) (hp : p ∈ W) (hq : ∀ j, q j ∈ W) :
    ENNReal.ofReal (|spatialDet (fun j => q j - p)| / 27) ≤ volume W := by
  let v : Fin 3 → Space := fun j => (1 / 3 : ℝ) • (q j - p)
  have hsub : (fun x => p + x) '' parallelepiped v ⊆ W := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨t, ht, rfl⟩ := (mem_parallelepiped_iff v x).mp hx
    have h0 : 0 ≤ t 0 := ht.1 0
    have h1 : 0 ≤ t 1 := ht.1 1
    have h2 : 0 ≤ t 2 := ht.1 2
    have h0' : t 0 ≤ 1 := ht.2 0
    have h1' : t 1 ≤ 1 := ht.2 1
    have h2' : t 2 ≤ 1 := ht.2 2
    let wt : Fin 4 → ℝ := ![1 - (t 0 + t 1 + t 2) / 3, t 0 / 3, t 1 / 3, t 2 / 3]
    let pt : Fin 4 → Space := ![p, q 0, q 1, q 2]
    have hmem := hW.sum_mem (t := Finset.univ) (w := wt) (z := pt)
      (by intro i _; fin_cases i <;> simp [wt] <;> linarith [ht.1 0, ht.1 1, ht.1 2,
        ht.2 0, ht.2 1, ht.2 2])
      (by simp [wt, Fin.sum_univ_four]; ring)
      (by intro i _; fin_cases i <;> simp [pt, hp, hq])
    convert hmem using 1
    simp only [Fin.sum_univ_four, Fin.sum_univ_three, wt, pt, v, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
    module
  have hvol := volume_translate_parallelepiped (EuclideanSpace.basisFun (Fin 3) ℝ) p v
  have hdet : (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.det v =
      (1 / 27 : ℝ) * spatialDet (fun j => q j - p) := by
    rw [det_frame]
    simp only [Matrix.det_fin_three, Matrix.of_apply]
    simp only [v, spatialDet, EuclideanSpace.basisFun_apply,
      EuclideanSpace.inner_single_left, map_one, one_mul, inner_smul_right, PiLp.smul_apply,
      smul_eq_mul]
    ring
  rw [hdet, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 27)] at hvol
  calc
    ENNReal.ofReal (|spatialDet (fun j => q j - p)| / 27) =
        volume ((fun x => p + x) '' parallelepiped v) := by rw [hvol]; congr 1; ring
    _ ≤ volume W := measure_mono hsub


/-- Coordinates are ordered as time, first planar coordinate, second planar coordinate. -/
def graphPoint (t : ℝ) (z : Plane) : Space :=
  WithLp.toLp 2 ![t / 10, z 0 / 10, z 1 / 10]

def tail (y : Space) : Plane := WithLp.toLp 2 ![y 1, y 2]

/-- The planar coordinate after subtracting a fixed reference affine trace. -/
def oblique (b u : Plane) (y : Space) : Plane :=
  (10 : ℝ) • tail y - b - (10 * y 0) • u

def rotate (z : Plane) : Plane := WithLp.toLp 2 ![-z 1, z 0]

def cross2 (z w : Plane) : ℝ := z 0 * w 1 - z 1 * w 0

theorem plane_inner (z w : Plane) : inner ℝ z w = z 0 * w 0 + z 1 * w 1 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, Fin.sum_univ_two, mul_comm]

theorem plane_norm_sq (z : Plane) : ‖z‖ ^ 2 = (z 0)^2 + (z 1)^2 := by
  simpa [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq z

theorem rotate_norm (z : Plane) : ‖rotate z‖ = ‖z‖ := by
  have h := plane_norm_sq (rotate z)
  have h' := plane_norm_sq z
  change ‖rotate z‖ ^ 2 = (-z 1)^2 + (z 0)^2 at h
  nlinarith [norm_nonneg (rotate z), norm_nonneg z]

theorem rotate_orthogonal (z : Plane) : inner ℝ (rotate z) z = 0 := by
  rw [plane_inner]
  simp [rotate]
  ring

theorem rotate_smul (a : ℝ) (z : Plane) : rotate (a • z) = a • rotate z := by
  ext k
  fin_cases k <;> simp [rotate] <;> ring

theorem cross2_normalize {p : Plane} (hp : 0 < ‖p‖) (q : Plane) :
    cross2 p q = ‖p‖ * inner ℝ q (rotate (‖p‖⁻¹ • p)) := by
  rw [rotate_smul, inner_smul_right, plane_inner]
  simp [rotate, cross2]
  field_simp
  <;> ring

theorem tail_norm_le (y : Space) : ‖tail y‖ ≤ ‖y‖ := by
  have h := EuclideanSpace.real_norm_sq_eq y
  rw [Fin.sum_univ_three] at h
  have h' := plane_norm_sq (tail y)
  change ‖tail y‖ ^ 2 = (y 1)^2 + (y 2)^2 at h'
  nlinarith [sq_nonneg (y 0), norm_nonneg (tail y), norm_nonneg y]

theorem oblique_graphPoint (b u z : Plane) (t : ℝ) :
    oblique b u (graphPoint t z) = z - b - t • u := by
  ext k
  fin_cases k <;> simp [oblique, graphPoint, tail] <;> ring

theorem oblique_bound {b u : Plane} (hb : ‖b‖ ≤ 1) (hu : ‖u‖ ≤ 1)
    {y : Space} (hy : y ∈ Metric.ball (0 : Space) 1) : ‖oblique b u y‖ ≤ 21 := by
  have hy' : ‖y‖ < 1 := by simpa using hy
  have ht : ‖tail y‖ ≤ 1 := (tail_norm_le y).trans hy'.le
  have hy0 : |y 0| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using (PiLp.norm_apply_le y 0).trans hy'.le
  calc
    ‖oblique b u y‖ ≤ ‖(10 : ℝ) • tail y‖ + ‖b‖ + ‖(10 * y 0) • u‖ :=
      by
        dsimp only [oblique]
        have h := norm_sub_le ((10 : ℝ) • tail y - b) ((10 * y 0) • u)
        have h' := norm_sub_le ((10 : ℝ) • tail y) b
        linarith
    _ ≤ 21 := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 10)]
      nlinarith [norm_nonneg u, norm_nonneg (tail y)]

theorem graph_determinant (b u : Plane) (y z : Space) :
    spatialDet ![graphPoint 1 (b + u) - graphPoint 0 b,
      y - graphPoint 0 b, z - graphPoint 0 b] =
        cross2 (oblique b u y) (oblique b u z) / 1000 := by
  simp [spatialDet, graphPoint, cross2, oblique, tail]
  ring


/-- A convex body containing a reference graph and transverse balls admits a planar
rectangle whose width product is controlled by its volume. -/
theorem exists_graph_rectangle {W : Set Space} (hW : Convex ℝ W)
    (hWb : W ⊆ Metric.ball (0 : Space) 1) {b u : Plane}
    (hb : ‖b‖ ≤ 1) (hu : ‖u‖ ≤ 1) {r : ℝ} (hr : 0 < r)
    (h0 : graphPoint 0 b ∈ W) (h1 : graphPoint 1 (b + u) ∈ W)
    (hpert : ∀ e : Plane, ‖e‖ = 1 → graphPoint 0 (b + r • e) ∈ W) :
    ∃ (e₁ e₂ : Plane) (a β : ℝ), ‖e₁‖ = 1 ∧ ‖e₂‖ = 1 ∧ inner ℝ e₁ e₂ = 0 ∧
      r ≤ a ∧ a ≤ β ∧ β ≤ 21 ∧
      (∀ y ∈ W, |inner ℝ (oblique b u y) e₁| ≤ a ∧
        |inner ℝ (oblique b u y) e₂| ≤ β) ∧
      ENNReal.ofReal (a * β) ≤ ENNReal.ofReal 108000 * volume W := by
  have hshift : ∀ e : Plane, oblique b u (graphPoint 0 (b + r • e)) = r • e := by
    intro e
    rw [oblique_graphPoint]
    module
  let e₀ : Plane := EuclideanSpace.single 0 1
  have he₀ : ‖e₀‖ = 1 := by simp [e₀]
  obtain ⟨R, hRlo, hRhi, hRle, p, hpW, hp⟩ :=
    exists_half_max (W := W) (fun y => ‖oblique b u y‖) hr
      (fun y hy => oblique_bound hb hu (hWb hy))
      ⟨graphPoint 0 (b + r • e₀), hpert e₀ he₀, by
        rw [hshift, norm_smul, he₀, mul_one, Real.norm_eq_abs, abs_of_pos hr]⟩
  have hp_pos : 0 < ‖oblique b u p‖ := by linarith
  let e₂ : Plane := ‖oblique b u p‖⁻¹ • oblique b u p
  let e₁ : Plane := rotate e₂
  have he₂ : ‖e₂‖ = 1 := by
    dsimp only [e₂]
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hp_pos.ne']
  have he₁ : ‖e₁‖ = 1 := by dsimp only [e₁]; rw [rotate_norm, he₂]
  have he12 : inner ℝ e₁ e₂ = 0 := rotate_orthogonal e₂
  have hcoord : ∀ y, |inner ℝ (oblique b u y) e₁| ≤ ‖oblique b u y‖ := by
    intro y
    simpa only [he₁, mul_one] using abs_real_inner_le_norm (oblique b u y) e₁
  obtain ⟨M, hMlo, hMhi, hMle, q, hqW, hq⟩ :=
    exists_half_max (W := W) (fun y => |inner ℝ (oblique b u y) e₁|) hr
      (fun y hy => (hcoord y).trans (hRle y hy))
      ⟨graphPoint 0 (b + r • e₁), hpert e₁ he₁, by
        rw [hshift, inner_smul_left, real_inner_self_eq_norm_sq, he₁]
        simpa [abs_of_pos hr]⟩
  refine ⟨e₁, e₂, M, R, he₁, he₂, he12, hMlo, hMhi, hRhi, ?_, ?_⟩
  · intro y hy
    refine ⟨hMle y hy, ?_⟩
    have hh : |inner ℝ (oblique b u y) e₂| ≤ ‖oblique b u y‖ := by
      simpa only [he₂, mul_one] using abs_real_inner_le_norm (oblique b u y) e₂
    exact hh.trans (hRle y hy)
  · have hcross : |cross2 (oblique b u p) (oblique b u q)| =
        ‖oblique b u p‖ * |inner ℝ (oblique b u q) e₁| := by
      rw [cross2_normalize hp_pos, abs_mul, abs_of_pos hp_pos]
    have hprod : M * R ≤ 4 * |cross2 (oblique b u p) (oblique b u q)| := by
      rw [hcross]
      have hM : 0 < M := hr.trans_le hMlo
      have hR : 0 < R := hr.trans_le hRlo
      have hq_pos : 0 < |inner ℝ (oblique b u q) e₁| := by linarith
      nlinarith [mul_lt_mul_of_pos_left hp hq_pos,
        mul_lt_mul_of_pos_right hq hR]
    have hv := determinant_le_volume hW (graphPoint 0 b)
      ![graphPoint 1 (b + u), p, q] h0 (by intro j; fin_cases j <;> simp [h1, hpW, hqW])
    change ENNReal.ofReal (|spatialDet ![graphPoint 1 (b + u) - graphPoint 0 b,
        p - graphPoint 0 b, q - graphPoint 0 b]| / 27) ≤ volume W at hv
    rw [graph_determinant, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1000)] at hv
    calc
      ENNReal.ofReal (M * R) ≤ ENNReal.ofReal 108000 *
          ENNReal.ofReal (|cross2 (oblique b u p) (oblique b u q)| / 1000 / 27) := by
        rw [← ENNReal.ofReal_mul (by norm_num)]
        apply ENNReal.ofReal_le_ofReal
        nlinarith
      _ ≤ ENNReal.ofReal 108000 * volume W := by gcongr

end
end Submission.Obl.k4_plank_tube_realization.ConvexGeometry
