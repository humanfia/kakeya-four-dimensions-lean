-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_affine_robust_cluster_estimate.Geometry.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

namespace WangZahlLot.Obl.wz_affine_robust_cluster_estimate

open MeasureTheory Set Metric
open scoped ENNReal

noncomputable section

abbrev E := EuclideanSpace ℝ (Fin 3)

def tube (δ : ℝ) (x v : E) : Set E := thickening δ (segment ℝ x (x + v))

def pd (u v : E) : ℝ := min ‖u - v‖ ‖u + v‖

theorem pd_nonneg (u v : E) : 0 ≤ pd u v := le_min (norm_nonneg _) (norm_nonneg _)

theorem pd_symm (u v : E) : pd u v = pd v u := by
  simp only [pd, norm_sub_rev, add_comm]

@[simp] theorem pd_neg_left (u v : E) : pd (-u) v = pd u v := by
  rw [pd, show -u - v = -(u + v) by abel, show -u + v = -(u - v) by abel]
  simp only [norm_neg]
  exact min_comm _ _

@[simp] theorem pd_neg_right (u v : E) : pd u (-v) = pd u v := by
  rw [pd_symm, pd_neg_left, pd_symm]

theorem pd_triangle (u v w : E) : pd u w ≤ pd u v + pd v w := by
  have h₁ : ‖u - w‖ ≤ ‖u - v‖ + ‖v - w‖ := by
    simpa [dist_eq_norm] using dist_triangle u v w
  have h₂ : ‖u + w‖ ≤ ‖u - v‖ + ‖v + w‖ := by
    simpa [dist_eq_norm] using dist_triangle u v (-w)
  have h₃ : ‖u + w‖ ≤ ‖u + v‖ + ‖v - w‖ := by
    calc
      ‖u + w‖ = ‖(u + v) - (v - w)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have h₄ : ‖u - w‖ ≤ ‖u + v‖ + ‖v + w‖ := by
    calc
      ‖u - w‖ = ‖(u + v) - (v + w)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  unfold pd
  rcases le_total ‖u - v‖ ‖u + v‖ with h | h <;>
    rcases le_total ‖v - w‖ ‖v + w‖ with h' | h'
  · rw [min_eq_left h, min_eq_left h']; exact (min_le_left _ _).trans h₁
  · rw [min_eq_left h, min_eq_right h']; exact (min_le_right _ _).trans h₂
  · rw [min_eq_right h, min_eq_left h']; exact (min_le_right _ _).trans h₃
  · rw [min_eq_right h, min_eq_right h']; exact (min_le_left _ _).trans h₄

theorem norm_sq_coords (u : E) : ‖u‖ ^ 2 = u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2 := by
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_succ, add_assoc]

theorem inner_coords (u v : E) : inner ℝ u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_succ, mul_comm, add_assoc]

/-- Squared Euclidean area of the parallelogram spanned by two vectors. -/
def areaSq (u v : E) : ℝ :=
  (u 0 * v 1 - u 1 * v 0) ^ 2 + (u 0 * v 2 - u 2 * v 0) ^ 2 +
    (u 1 * v 2 - u 2 * v 1) ^ 2

theorem areaSq_nonneg (u v : E) : 0 ≤ areaSq u v := by unfold areaSq; positivity

theorem areaSq_gram (u v : E) :
    areaSq u v = ‖u‖ ^ 2 * ‖v‖ ^ 2 - (inner ℝ u v) ^ 2 := by
  rw [norm_sq_coords, norm_sq_coords, inner_coords]
  unfold areaSq
  ring

theorem areaSq_smul (a b : ℝ) (u v : E) :
    areaSq (a • u) (b • v) = a ^ 2 * b ^ 2 * areaSq u v := by
  simp only [areaSq, PiLp.smul_apply, smul_eq_mul]
  ring

theorem pd_sq_le_areaSq {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    pd u v ^ 2 ≤ 2 * areaSq u v := by
  have hs := norm_sub_sq_real u v
  have ha := norm_add_sq_real u v
  rw [hu, hv] at hs ha
  have hab : |inner ℝ u v| ≤ 1 := by simpa [hu, hv] using abs_real_inner_le_norm u v
  rw [abs_le] at hab
  rw [areaSq_gram, hu, hv]
  rcases le_total 0 (inner ℝ u v) with h | h
  · have hmin : ‖u - v‖ ≤ ‖u + v‖ := by nlinarith [norm_nonneg (u - v), norm_nonneg (u + v)]
    rw [pd, min_eq_left hmin]
    nlinarith [mul_nonneg h (sub_nonneg.mpr hab.2)]
  · have hmin : ‖u + v‖ ≤ ‖u - v‖ := by nlinarith [norm_nonneg (u - v), norm_nonneg (u + v)]
    rw [pd, min_eq_right hmin]
    nlinarith [mul_nonneg (neg_nonneg.mpr h) (show 0 ≤ 1 + inner ℝ u v by linarith)]

theorem areaSq_le_pd_sq {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    areaSq u v ≤ pd u v ^ 2 := by
  have hs := norm_sub_sq_real u v
  have ha := norm_add_sq_real u v
  rw [hu, hv] at hs ha
  rw [areaSq_gram, hu, hv]
  rcases le_total ‖u - v‖ ‖u + v‖ with h | h
  · rw [pd, min_eq_left h]; nlinarith [sq_nonneg (1 - inner ℝ u v)]
  · rw [pd, min_eq_right h]; nlinarith [sq_nonneg (1 + inner ℝ u v)]

/-- Dilation in the two coordinates perpendicular to coordinate zero. -/
def stretch (t : ℝ) : E →ₗ[ℝ] E where
  toFun u := WithLp.toLp 2 ![u 0, t * u 1, t * u 2]
  map_add' u v := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a u := by ext i; fin_cases i <;> simp <;> ring

@[simp] theorem stretch_zero (t : ℝ) (u : E) : stretch t u 0 = u 0 := rfl
@[simp] theorem stretch_one (t : ℝ) (u : E) : stretch t u 1 = t * u 1 := rfl
@[simp] theorem stretch_two (t : ℝ) (u : E) : stretch t u 2 = t * u 2 := rfl

theorem norm_stretch_le {t : ℝ} (ht : 1 ≤ t) (u : E) : ‖stretch t u‖ ≤ t * ‖u‖ := by
  have ht0 : 0 ≤ t := by linarith
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  have hsq : ‖stretch t u‖ ^ 2 ≤ (t * ‖u‖) ^ 2 := by
    rw [mul_pow, norm_sq_coords, norm_sq_coords]
    simp only [stretch_zero, stretch_one, stretch_two]
    nlinarith [mul_nonneg (show 0 ≤ t ^ 2 - 1 by linarith) (sq_nonneg (u 0))]
  nlinarith [norm_nonneg (stretch t u), norm_nonneg u, mul_nonneg ht0 (norm_nonneg u)]

theorem norm_le_stretch {t : ℝ} (ht : 1 ≤ t) (u : E) : ‖u‖ ≤ ‖stretch t u‖ := by
  have ht2 : 1 ≤ t ^ 2 := by nlinarith
  have hsq : ‖u‖ ^ 2 ≤ ‖stretch t u‖ ^ 2 := by
    rw [norm_sq_coords, norm_sq_coords]
    simp only [stretch_zero, stretch_one, stretch_two]
    nlinarith [mul_nonneg (show 0 ≤ t ^ 2 - 1 by linarith) (sq_nonneg (u 1)),
      mul_nonneg (show 0 ≤ t ^ 2 - 1 by linarith) (sq_nonneg (u 2))]
  nlinarith [norm_nonneg (stretch t u), norm_nonneg u]

theorem areaSq_stretch {t : ℝ} (ht : 1 ≤ t) (u v : E) :
    t ^ 2 * areaSq u v ≤ areaSq (stretch t u) (stretch t v) := by
  have h : 0 ≤ (t ^ 2 - 1) * (u 1 * v 2 - u 2 * v 1) ^ 2 :=
    mul_nonneg (by nlinarith) (sq_nonneg _)
  have ht0 : 0 ≤ t ^ 2 := sq_nonneg _
  have := mul_nonneg ht0 h
  simp only [areaSq, stretch_zero, stretch_one, stretch_two] at *
  nlinarith only [this]

noncomputable def unit (u : E) : E := ‖u‖⁻¹ • u

theorem norm_unit {u : E} (hu : u ≠ 0) : ‖unit u‖ = 1 := by
  simp [unit, norm_smul, norm_ne_zero_iff.mpr hu]

theorem norm_smul_unit {u : E} (hu : u ≠ 0) : ‖u‖ • unit u = u := by
  simp [unit, smul_smul, norm_ne_zero_iff.mpr hu]

/-- A transverse dilation expands projective angles by order `t` on vectors
whose dilated lengths are bounded by `L`. -/
theorem pd_stretch {t L : ℝ} (ht : 1 ≤ t) (hL : 0 ≤ L) {u v : E}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (huL : ‖stretch t u‖ ≤ L) (hvL : ‖stretch t v‖ ≤ L) :
    t * pd u v ≤ 2 * L ^ 2 * pd (unit (stretch t u)) (unit (stretch t v)) := by
  have hsu : stretch t u ≠ 0 := by
    have := norm_le_stretch ht u
    rw [hu] at this
    exact norm_ne_zero_iff.mp (by linarith)
  have hsv : stretch t v ≠ 0 := by
    have := norm_le_stretch ht v
    rw [hv] at this
    exact norm_ne_zero_iff.mp (by linarith)
  have he : areaSq (stretch t u) (stretch t v) =
      ‖stretch t u‖ ^ 2 * ‖stretch t v‖ ^ 2 *
        areaSq (unit (stretch t u)) (unit (stretch t v)) := by
    conv_lhs => rw [← norm_smul_unit hsu, ← norm_smul_unit hsv]
    exact areaSq_smul _ _ _ _
  have harea : areaSq (stretch t u) (stretch t v) ≤
      L ^ 4 * pd (unit (stretch t u)) (unit (stretch t v)) ^ 2 := by
    rw [he, show L ^ 4 = L ^ 2 * L ^ 2 by ring]
    have hnarea := areaSq_nonneg (unit (stretch t u)) (unit (stretch t v))
    gcongr
    exact areaSq_le_pd_sq (norm_unit hsu) (norm_unit hsv)
  have hbase := mul_le_mul_of_nonneg_left (pd_sq_le_areaSq hu hv) (sq_nonneg t)
  have hstretch := areaSq_stretch ht u v
  have hp := pd_nonneg u v
  have hp' := pd_nonneg (unit (stretch t u)) (unit (stretch t v))
  have htarget : 0 ≤ 2 * L ^ 2 * pd (unit (stretch t u)) (unit (stretch t v)) := by positivity
  have hsq : (t * pd u v) ^ 2 ≤
      (2 * L ^ 2 * pd (unit (stretch t u)) (unit (stretch t v))) ^ 2 := by
    nlinarith only [hbase, hstretch, harea,
      mul_nonneg (pow_nonneg hL 4) (sq_nonneg (pd (unit (stretch t u)) (unit (stretch t v))))]
  nlinarith only [hsq, htarget]


def axis : E := WithLp.toLp 2 ![1, 0, 0]

theorem norm_axis : ‖axis‖ = 1 := by
  have h : ‖axis‖ ^ 2 = 1 := by rw [norm_sq_coords]; norm_num [axis]
  nlinarith [norm_nonneg axis]

@[simp] theorem stretch_axis (t : ℝ) : stretch t axis = axis := by
  ext i
  fin_cases i <;> simp [axis]

theorem pd_isometry (e : E ≃ₗᵢ[ℝ] E) (u v : E) : pd (e u) (e v) = pd u v := by
  simp only [pd, ← map_sub, ← map_add, e.norm_map]

theorem norm_stretch_cap {t r : ℝ} (ht : 1 ≤ t) {u : E} (hu : pd u axis ≤ r) :
    ‖stretch t u‖ ≤ 1 + t * r := by
  have ht0 : 0 ≤ t := by linarith
  rcases min_le_iff.mp hu with h | h
  · calc
      ‖stretch t u‖ = ‖stretch t (u - axis) + axis‖ := by rw [map_sub, stretch_axis]; simp
      _ ≤ ‖stretch t (u - axis)‖ + ‖axis‖ := norm_add_le _ _
      _ ≤ t * ‖u - axis‖ + 1 := by rw [norm_axis]; gcongr; exact norm_stretch_le ht _
      _ ≤ 1 + t * r := by nlinarith
  · calc
      ‖stretch t u‖ = ‖stretch t (u + axis) - axis‖ := by rw [map_add, stretch_axis]; simp
      _ ≤ ‖stretch t (u + axis)‖ + ‖axis‖ := norm_sub_le _ _
      _ ≤ t * ‖u + axis‖ + 1 := by rw [norm_axis]; gcongr; exact norm_stretch_le ht _
      _ ≤ 1 + t * r := by nlinarith

/-- Rotate a specified unit vector onto coordinate zero. -/
theorem exists_rotation {w : E} (hw : ‖w‖ = 1) :
    ∃ e : E ≃ₗᵢ[ℝ] E, e w = axis := by
  exact ⟨(ℝ ∙ (w - axis))ᗮ.reflection, Submodule.reflection_sub (hw.trans norm_axis.symm)⟩

theorem det_stretch (t : ℝ) : LinearMap.det (stretch t) = t ^ 2 := by
  let b := (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
  have he : LinearMap.toMatrix b b (stretch t) = Matrix.diagonal ![1, t, t] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [LinearMap.toMatrix_apply, b, EuclideanSpace.basisFun_apply,
        OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_repr, Matrix.diagonal,
        EuclideanSpace.single, stretch]
  rw [← LinearMap.det_toMatrix b, he, Matrix.det_diagonal]
  simp [Fin.prod_univ_succ, pow_two]

/-- The transverse dilation is invertible whenever its factor is nonzero. -/
def stretchEquiv (t : ℝ) (ht : t ≠ 0) : E ≃ₗ[ℝ] E :=
  (stretch t).equivOfDetNeZero (by rw [det_stretch]; exact pow_ne_zero _ ht)

@[simp] theorem stretchEquiv_apply (t : ℝ) (ht : t ≠ 0) (u : E) :
    stretchEquiv t ht u = stretch t u := rfl

end

end WangZahlLot.Obl.wz_affine_robust_cluster_estimate
