/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarPlaneRotation.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarPlaneRotation.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! A signed forty-five-degree plane isometry for scalar collision graphs.
The first graph is rotated about its actual anchor, without translation
afterwards; only the second graph may be translated into the unit square. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open scoped RealInnerProductSpace

abbrev ScalarPlane := EuclideanSpace ℝ (Fin 2)

noncomputable def signedPlaneIsometry (e : ℝ) (he : e ^ 2 = 1) :
    ScalarPlane →ₗᵢ[ℝ] ScalarPlane where
  toFun x := !₂[(e * x 0 + x 1) / Real.sqrt 2, (e * x 0 - x 1) / Real.sqrt 2]
  map_add' := by
    intro x y
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro a x
    ext i
    fin_cases i <;> simp [smul_eq_mul] <;> ring
  norm_map' := by
    intro x
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq,
      Fin.sum_univ_two, Fin.sum_univ_two]
    change ((e * x 0 + x 1) / Real.sqrt 2) ^ 2 +
      ((e * x 0 - x 1) / Real.sqrt 2) ^ 2 = (x 0) ^ 2 + (x 1) ^ 2
    rw [div_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have hesq : (e * x 0) ^ 2 = (x 0) ^ 2 := by rw [mul_pow, he, one_mul]
    nlinarith only [hesq]

noncomputable def signedPlaneRotation (e : ℝ) (he : e ^ 2 = 1) :
    ScalarPlane ≃ₗᵢ[ℝ] ScalarPlane :=
  LinearIsometryEquiv.ofSurjective (signedPlaneIsometry e he)
    (LinearMap.injective_iff_surjective.mp (signedPlaneIsometry e he).injective)

theorem signedPlaneRotation_apply (e : ℝ) (he : e ^ 2 = 1) (x : ScalarPlane) :
    signedPlaneRotation e he x =
      !₂[(e * x 0 + x 1) / Real.sqrt 2, (e * x 0 - x 1) / Real.sqrt 2] := rfl

noncomputable def diagonalPoint (e x y : ℝ) : ScalarPlane :=
  !₂[(e * x + y) / 2, (e * x - y) / 2]

theorem diagonalPoint_eq_scale (e : ℝ) (he : e ^ 2 = 1) (x y : ℝ) :
    diagonalPoint e x y = (Real.sqrt 2)⁻¹ • signedPlaneRotation e he !₂[x, y] := by
  have hmul (z : ℝ) : (Real.sqrt 2)⁻¹ * (z / Real.sqrt 2) = z / 2 := by
    calc
      _ = z / (Real.sqrt 2 * Real.sqrt 2) := by ring
      _ = _ := by rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  ext i
  fin_cases i <;> simp [diagonalPoint, signedPlaneRotation_apply, smul_eq_mul, hmul]

theorem diagonalPoint_dist (e : ℝ) (he : e ^ 2 = 1) (x y x' y' : ℝ) :
    dist (diagonalPoint e x y) (diagonalPoint e x' y') =
      (Real.sqrt 2)⁻¹ * dist (!₂[x, y] : ScalarPlane) !₂[x', y'] := by
  rw [diagonalPoint_eq_scale e he, diagonalPoint_eq_scale e he,
    dist_smul₀, LinearIsometryEquiv.dist_map]
  simp only [Real.norm_eq_abs, abs_inv, abs_of_nonneg (Real.sqrt_nonneg (2 : ℝ))]

theorem diagonalPoint_original_dist_le (e : ℝ) (he : e ^ 2 = 1) (x y x' y' : ℝ) :
    dist (!₂[x, y] : ScalarPlane) !₂[x', y'] ≤ 2 * dist (diagonalPoint e x y) (diagonalPoint e x' y') := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsle : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have heq : dist (!₂[x, y] : ScalarPlane) !₂[x', y'] =
      Real.sqrt 2 * dist (diagonalPoint e x y) (diagonalPoint e x' y') := by
    rw [diagonalPoint_dist e he, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  rw [heq]
  exact mul_le_mul_of_nonneg_right hsle dist_nonneg

theorem diagonalPoint_unit {e x y : ℝ} (he : |e| = 1) (hx : |x| ≤ 1)
    (hy : |y| ≤ |x|) (hex : 0 ≤ e * x) :
    ∀ i : Fin 2, 0 ≤ diagonalPoint e x y i ∧ diagonalPoint e x y i ≤ 1 := by
  have hEx : e * x = |x| := by
    calc
      e * x = |e * x| := (abs_of_nonneg hex).symm
      _ = |x| := by rw [abs_mul, he, one_mul]
  obtain ⟨hy₁, hy₂⟩ := abs_le.mp hy
  intro i
  fin_cases i
  · change 0 ≤ (e * x + y) / 2 ∧ (e * x + y) / 2 ≤ 1
    constructor <;> linarith
  · change 0 ≤ (e * x - y) / 2 ∧ (e * x - y) / 2 ≤ 1
    constructor <;> linarith

theorem diagonalPoint_inner (e : ℝ) (he : e ^ 2 = 1) (x y u v : ℝ) :
    ⟪diagonalPoint e x y, diagonalPoint e u v⟫ = (x * u + y * v) / 2 := by
  simp only [PiLp.inner_apply, Fin.sum_univ_two, diagonalPoint,
    PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one, RCLike.inner_apply, conj_trivial]
  ring_nf
  simp only [he, one_mul, mul_one]

/-- Translating the second graph cancels exactly in its difference. -/
theorem diagonalPoint_translated_dot (e : ℝ) (he : e ^ 2 = 1)
    (x y u v u' v' scale : ℝ) (c : ScalarPlane) :
    ⟪diagonalPoint e x y, (scale • diagonalPoint e u v + c) -
      (scale • diagonalPoint e u' v' + c)⟫ = (scale / 2) * (x * (u - u') + y * (v - v')) := by
  rw [inner_sub_right, inner_add_right, inner_add_right, inner_smul_right, inner_smul_right,
    diagonalPoint_inner e he, diagonalPoint_inner e he]
  ring

theorem diagonalPoint_inner_right (e : ℝ) (he : e ^ 2 = 1) (x y : ℝ) (n : ScalarPlane) :
    ⟪diagonalPoint e x y, n⟫ = (Real.sqrt 2)⁻¹ *
      ⟪(!₂[x, y] : ScalarPlane), (signedPlaneRotation e he).symm n⟫ := by
  have hm := (signedPlaneRotation e he).inner_map_map (!₂[x, y] : ScalarPlane)
    ((signedPlaneRotation e he).symm n)
  simp only [LinearIsometryEquiv.apply_symm_apply] at hm
  rw [diagonalPoint_eq_scale e he, inner_smul_left, hm]
  simp only [conj_trivial]

/-- A strip for the normalized rotated graph is a strip for the original
centered row graph, with its exact square-root scale loss. -/
theorem diagonalPoint_strip_transfer (e : ℝ) (he : e ^ 2 = 1)
    (x y c δ : ℝ) (n : ScalarPlane)
    (h : |⟪diagonalPoint e x y, n⟫ - c| ≤ δ) :
    |⟪(!₂[x, y] : ScalarPlane), (signedPlaneRotation e he).symm n⟫ - Real.sqrt 2 * c| ≤
      Real.sqrt 2 * δ := by
  have hs : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have heq : ⟪(!₂[x, y] : ScalarPlane), (signedPlaneRotation e he).symm n⟫ - Real.sqrt 2 * c =
      Real.sqrt 2 * (⟪diagonalPoint e x y, n⟫ - c) := by
    rw [diagonalPoint_inner_right e he, mul_sub, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
  rw [heq, abs_mul, abs_of_pos hs]
  exact mul_le_mul_of_nonneg_left h hs.le

noncomputable def boxedDiagonalPoint (e B u v : ℝ) : ScalarPlane :=
  (2 * B)⁻¹ • diagonalPoint e u v + !₂[1 / 2, 1 / 2]

theorem boxedDiagonalPoint_unit {e B u v : ℝ} (he : |e| = 1) (hB : 0 < B)
    (hu : |u| ≤ B) (hv : |v| ≤ B) :
    ∀ i : Fin 2, 0 ≤ boxedDiagonalPoint e B u v i ∧ boxedDiagonalPoint e B u v i ≤ 1 := by
  have heu : |e * u| ≤ B := by simpa only [abs_mul, he, one_mul] using hu
  have hplus : |e * u + v| ≤ 2 * B := (abs_add_le _ _).trans (by linarith)
  have hminus : |e * u - v| ≤ 2 * B := (abs_sub _ _).trans (by linarith)
  have hbound (z : ℝ) (hz : |z| ≤ 2 * B) : 0 ≤ z / (4 * B) + 1 / 2 ∧
      z / (4 * B) + 1 / 2 ≤ 1 := by
    have hden : 0 < 4 * B := mul_pos (by norm_num) hB
    have hlo : -(1 / 2 : ℝ) ≤ z / (4 * B) :=
      (le_div_iff₀ hden).mpr (by linarith [(abs_le.mp hz).1])
    have hhi : z / (4 * B) ≤ (1 / 2 : ℝ) :=
      (div_le_iff₀ hden).mpr (by linarith [(abs_le.mp hz).2])
    constructor <;> linarith
  have heq (z : ℝ) : (2 * B)⁻¹ * (z / 2) = z / (4 * B) := by
    field_simp
    <;> ring
  intro i
  fin_cases i
  · change 0 ≤ (2 * B)⁻¹ * ((e * u + v) / 2) + 1 / 2 ∧
      (2 * B)⁻¹ * ((e * u + v) / 2) + 1 / 2 ≤ 1
    rw [heq]
    exact hbound _ hplus
  · change 0 ≤ (2 * B)⁻¹ * ((e * u - v) / 2) + 1 / 2 ∧
      (2 * B)⁻¹ * ((e * u - v) / 2) + 1 / 2 ≤ 1
    rw [heq]
    exact hbound _ hminus

theorem boxedDiagonalPoint_dot (e : ℝ) (he : e ^ 2 = 1) (B : ℝ) (hB : B ≠ 0)
    (x y u v u' v' : ℝ) :
    ⟪diagonalPoint e x y, boxedDiagonalPoint e B u v - boxedDiagonalPoint e B u' v'⟫ =
      (1 / (4 * B)) * (x * (u - u') + y * (v - v')) := by
  unfold boxedDiagonalPoint
  rw [diagonalPoint_translated_dot e he]
  field_simp [hB] <;> ring

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
