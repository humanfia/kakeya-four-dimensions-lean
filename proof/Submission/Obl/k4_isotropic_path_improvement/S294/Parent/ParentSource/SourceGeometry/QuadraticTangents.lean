-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourceGeometry.QuadraticTangents, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourceGeometry/QuadraticTangents.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourceGeometry/QuadraticTangents.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceGeometry/QuadraticTangents.lean.
-- Existing source attributions are preserved below.

/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o106,
   session x0352, commit b976e86c1df62f72f3fa9d42b0a0c928d33ecc7d;
   original file Submission/Obl/k4_isotropic_path_improvement/QuadraticTangents.lean.
   Existing source comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry.PlaneGraph
import Submission.Obl.k4_eligibility_sign_description.Families

/-!
Native quadratic trajectories have uniform affine tangent approximations.
Only their whole-unit-time value bound is used, so no polynomial coefficient
or original line-parameter bounds enter the tangent error.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry

open Set
open Submission.Obl.k4_eligibility_sign_description

noncomputable section

/-- Three time evaluations bound all scalar quadratic coefficients. -/
theorem bounded_quadratic_coefficients (a b c K : ℝ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |a * t ^ 2 + b * t + c| ≤ K) :
    |a| ≤ 8 * K ∧ |b| ≤ 10 * K ∧ |c| ≤ K := by
  have h0 := abs_le.mp (h 0 ⟨le_rfl, zero_le_one⟩)
  have hhalf := abs_le.mp (h (1 / 2) ⟨by norm_num, by norm_num⟩)
  have h1 := abs_le.mp (h 1 ⟨zero_le_one, le_rfl⟩)
  norm_num at h0 hhalf h1
  refine ⟨abs_le.mpr ⟨by linarith, by linarith⟩,
    abs_le.mpr ⟨by linarith, by linarith⟩, abs_le.mpr h0⟩

theorem quadratic_hasDerivAt (a b c t : ℝ) :
    HasDerivAt (fun t => a * t ^ 2 + b * t + c) (2 * a * t + b) t := by
  convert ((((hasDerivAt_id t).pow 2).const_mul a).add
    ((hasDerivAt_id t).const_mul b)).add_const c using 1
  · funext x
    simp only [Pi.add_apply, Pi.pow_apply, id_eq]
  · simp only [id_eq]
    ring

/-- The scalar affine tangent error and derivative change are explicit. -/
theorem quadratic_tangent_bounds (a b c K : ℝ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |a * t ^ 2 + b * t + c| ≤ K) :
    (∀ s t : ℝ,
      |(a * t ^ 2 + b * t + c) - (a * s ^ 2 + b * s + c) -
        (t - s) * (2 * a * s + b)| ≤ 8 * K * |t - s| ^ 2) ∧
    (∀ s t : ℝ, |(2 * a * t + b) - (2 * a * s + b)| ≤ 16 * K * |t - s|) ∧
    (∀ t ∈ Icc (0 : ℝ) 1, |2 * a * t + b| ≤ 26 * K) := by
  obtain ⟨ha, hb, _⟩ := bounded_quadratic_coefficients a b c K h
  refine ⟨?_, ?_, ?_⟩
  · intro s t
    rw [show (a * t ^ 2 + b * t + c) - (a * s ^ 2 + b * s + c) -
      (t - s) * (2 * a * s + b) = a * (t - s) ^ 2 by ring, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right ha (sq_nonneg _)
  · intro s t
    rw [show (2 * a * t + b) - (2 * a * s + b) = (2 * a) * (t - s) by ring,
      abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul_of_nonneg_right ha (abs_nonneg (t - s))]
  · intro t ht
    have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    calc
      |2 * a * t + b| ≤ |2 * a * t| + |b| := abs_add_le _ _
      _ = 2 * |a| * |t| + |b| := by rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      _ ≤ 26 * K := by nlinarith [mul_le_mul_of_nonneg_left ht1 (abs_nonneg a)]

/-- The full lifted trajectory is affine in its first three coordinates. -/
def quadraticLift (p v : Fin 3 → ℝ) (a b c t : ℝ) : EuclideanSpace ℝ (Fin 4) :=
  liftedVector (fun j => p j + t * v j) (a * t ^ 2 + b * t + c)

theorem quadraticLift_tangent_remainder (p v : Fin 3 → ℝ) (a b c s t : ℝ) :
    quadraticLift p v a b c t - quadraticLift p v a b c s -
      (t - s) • liftedVector v (2 * a * s + b) =
        (a * (t - s) ^ 2) • EuclideanSpace.single (3 : Fin 4) (1 : ℝ) := by
  ext j
  fin_cases j <;> simp [quadraticLift, liftedVector] <;> ring

theorem quadraticLift_tangent_bound (p v : Fin 3 → ℝ) (a b c K : ℝ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |a * t ^ 2 + b * t + c| ≤ K) (s t : ℝ) :
    ‖quadraticLift p v a b c t - quadraticLift p v a b c s -
      (t - s) • liftedVector v (2 * a * s + b)‖ ≤ 8 * K * |t - s| ^ 2 := by
  rw [quadraticLift_tangent_remainder, norm_smul]
  simpa [abs_mul, abs_pow] using
    mul_le_mul_of_nonneg_right (bounded_quadratic_coefficients a b c K h).1
      (sq_nonneg |t - s|)

/-- Native tests along actual affine lines inherit these tangent bounds from
the accepted quadratic line-pullback theorem. -/
theorem native_quadratic_tangents (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (p v : Fin 4 → ℝ) (K : ℝ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (fun j => p j + t * v j) P| ≤ K) :
    ∃ a b c : ℝ,
      (∀ t : ℝ, MvPolynomial.eval (fun j => p j + t * v j) P = a * t ^ 2 + b * t + c) ∧
      |a| ≤ 8 * K ∧ |b| ≤ 10 * K ∧ |c| ≤ K ∧
      (∀ s t : ℝ,
        |MvPolynomial.eval (fun j => p j + t * v j) P -
          MvPolynomial.eval (fun j => p j + s * v j) P -
          (t - s) * (2 * a * s + b)| ≤ 8 * K * |t - s| ^ 2) ∧
      (∀ s t : ℝ, |(2 * a * t + b) - (2 * a * s + b)| ≤ 16 * K * |t - s|) := by
  obtain ⟨a, b, c, hquad⟩ := Quadratic.mv_line P hP p v
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, |a * t ^ 2 + b * t + c| ≤ K := by
    intro t ht
    simpa only [hquad] using h t ht
  obtain ⟨ha, hb, hc⟩ := bounded_quadratic_coefficients a b c K hbound
  obtain ⟨htan, hdir, _⟩ := quadratic_tangent_bounds a b c K hbound
  exact ⟨a, b, c, hquad, ha, hb, hc, by simpa only [hquad] using htan, hdir⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry
