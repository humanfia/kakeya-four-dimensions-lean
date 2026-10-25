-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_unit_segment_convex_slab_cover.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
import Submission.WZ.Obl.wz_seed_of_balanced_robust_clusters.Geometry

namespace WangZahlLot.Obl.wz_unit_segment_convex_slab_cover

open Module Set Metric MeasureTheory LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal Pointwise

/-- Three displacements, contracted by a quarter, fit in their convex hull. -/
lemma quarter_parallelepiped_subset {W : Set Space} (hW : Convex ℝ W)
    {x v y z : Space} (hx : x ∈ W) (hv : x + v ∈ W) (hy : y ∈ W) (hz : z ∈ W) :
    (fun q : Space => x + (1 / 4 : ℝ) • q) ''
      parallelepiped ![v, y - x, z - x] ⊆ W := by
  rintro _ ⟨q, hq, rfl⟩
  obtain ⟨t, ht, rfl⟩ := (mem_parallelepiped_iff _ _).mp hq
  have hseg (a : Space) (ha : a ∈ W) (i : Fin 3) :
      x + t i • (a - x) ∈ W := by
    have hti0 : (0 : ℝ) ≤ t i := ht.1 i
    have hti1 : t i ≤ (1 : ℝ) := ht.2 i
    have h := hW hx ha (sub_nonneg.mpr hti1) hti0 (by ring)
    convert h using 1
    module
  have h₀ := hseg (x + v) hv 0
  have h₁ := hseg y hy 1
  have h₂ := hseg z hz 2
  have hm₁ := hW h₀ h₁ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hm₂ := hW h₂ hx (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have hm := hW hm₁ hm₂ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  rw [Fin.sum_univ_three]
  change x + (1 / 4 : ℝ) • (t 0 • v + t 1 • (y - x) + t 2 • (z - x)) ∈ W
  convert hm using 1
  module

/-- A determinant controlled by the measure of any convex set containing the four vertices. -/
lemma determinant_le_volume {W : Set Space} (hW : Convex ℝ W)
    {x v y z : Space} (hx : x ∈ W) (hv : x + v ∈ W) (hy : y ∈ W) (hz : z ∈ W)
    (b : OrthonormalBasis (Fin 3) ℝ Space) {s : ℝ} (hs : 0 ≤ s)
    (hvol : volume W ≤ ENNReal.ofReal s) :
    |b.toBasis.det ![v, y - x, z - x]| ≤ 64 * s := by
  have hsub := quarter_parallelepiped_subset hW hx hv hy hz
  have hm := (measure_mono hsub).trans hvol
  have he : (fun q : Space => x + (1 / 4 : ℝ) • q) ''
      parallelepiped ![v, y - x, z - x] =
      (fun q : Space => x + q) '' ((1 / 4 : ℝ) • parallelepiped ![v, y - x, z - x]) := by
    rw [← image_smul, ← image_comp]
    rfl
  rw [he, image_add_left, measure_preimage_add,
    Measure.addHaar_smul, finrank_euclideanSpace_fin,
    ← b.addHaar_eq_volume, Measure.addHaar_parallelepiped] at hm
  norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)] at hm
  rw [← ENNReal.ofReal_mul (by positivity)] at hm
  have hr := (ENNReal.ofReal_le_ofReal_iff hs).mp hm
  norm_num at hr
  linarith

/-- With the first basis direction fixed, the determinant is a transverse area. -/
lemma determinant_first (b : OrthonormalBasis (Fin 3) ℝ Space) (y z : Space) :
    b.toBasis.det ![b 0, y, z] =
      inner ℝ (b 1) y * inner ℝ (b 2) z -
        inner ℝ (b 2) y * inner ℝ (b 1) z := by
  rw [Basis.det_apply, Matrix.det_fin_three]
  simp [Basis.toMatrix_apply, OrthonormalBasis.repr_apply_apply, mul_comm]

/-- A small bound on transverse areas produces a slab of square-root width. -/
lemma slab_of_determinant_bound (b : OrthonormalBasis (Fin 3) ℝ Space)
    (x : Space) (W : Set Space) {r : ℝ} (hr : 0 < r)
    (hdet : ∀ y ∈ W, ∀ z ∈ W,
      |b.toBasis.det ![b 0, y - x, z - x]| ≤ r ^ 2) :
    ∃ u : Space, ‖u‖ = 1 ∧ ∀ p ∈ W, |inner ℝ u p - inner ℝ u x| ≤ r := by
  classical
  by_cases hthin : ∀ p ∈ W, |inner ℝ (b 1) (p - x)| ≤ r
  · exact ⟨b 1, b.norm_eq_one 1, by simpa only [inner_sub_right] using hthin⟩
  push Not at hthin
  obtain ⟨y, hy, hwide⟩ := hthin
  let d : Space := -(inner ℝ (b 2) (y - x)) • b 1 +
    (inner ℝ (b 1) (y - x)) • b 2
  have hdcoord : inner ℝ (b 2) d = inner ℝ (b 1) (y - x) := by
    simp [d, inner_add_right, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal]
  have hdnorm : |inner ℝ (b 1) (y - x)| ≤ ‖d‖ := by
    simpa only [hdcoord, b.norm_eq_one, one_mul] using abs_real_inner_le_norm (b 2) d
  have hdpos : 0 < ‖d‖ := hr.trans (hwide.trans_le hdnorm)
  refine ⟨‖d‖⁻¹ • d, ?_, ?_⟩
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hdpos), inv_mul_cancel₀ hdpos.ne']
  · intro p hp
    have hid : inner ℝ d (p - x) = b.toBasis.det ![b 0, y - x, p - x] := by
      rw [determinant_first]
      simp only [d, inner_add_left, real_inner_smul_left]
      ring
    rw [← inner_sub_right, real_inner_smul_left, abs_mul,
      abs_of_pos (inv_pos.mpr hdpos), hid]
    calc
      ‖d‖⁻¹ * |b.toBasis.det ![b 0, y - x, p - x]| ≤ ‖d‖⁻¹ * r ^ 2 :=
        mul_le_mul_of_nonneg_left (hdet y hy p hp) (inv_nonneg.mpr hdpos.le)
      _ ≤ r := by
        rw [← div_eq_inv_mul, div_le_iff₀ hdpos]
        nlinarith [hwide.trans_le hdnorm]

/-- Convex sets containing a unit segment have width at most eight times the square root
of their volume bound. This also includes sets of zero volume. -/
lemma exists_thin_slab {s : ℝ} (hs : 0 < s) {W : Set Space} (hW : Convex ℝ W)
    (hvol : volume W ≤ ENNReal.ofReal s) {x v : Space}
    (hv : ‖v‖ = 1) (hseg : segment ℝ x (x + v) ⊆ W) :
    ∃ u : Space, ‖u‖ = 1 ∧
      ∀ p ∈ W, |inner ℝ u p - inner ℝ u x| ≤ 8 * Real.sqrt s := by
  obtain ⟨b, hb⟩ :=
    WangZahlLot.Obl.wz_seed_of_balanced_robust_clusters.exists_basis_first hv
  apply slab_of_determinant_bound b x W (mul_pos (by norm_num) (Real.sqrt_pos.mpr hs))
  intro y hy z hz
  rw [hb]
  have h := determinant_le_volume hW (hseg (left_mem_segment ℝ x (x + v)))
    (hseg (right_mem_segment ℝ x (x + v))) hy hz b hs.le hvol
  have he : (8 * Real.sqrt s) ^ 2 = 64 * s := by
    rw [mul_pow, Real.sq_sqrt hs.le]
    norm_num
  simpa only [he] using h

end WangZahlLot.Obl.wz_unit_segment_convex_slab_cover
