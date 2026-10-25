-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.SourceGeometry.NativeCurveCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/SourceGeometry/NativeCurveCells.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/SourceGeometry/NativeCurveCells.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/SourceGeometry/NativeCurveCells.lean.
-- Existing source attributions are preserved below.

/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o106,
   session x0352, commit b976e86c1df62f72f3fa9d42b0a0c928d33ecc7d;
   original file Submission/Obl/k4_isotropic_path_improvement/NativeCurveCells.lean.
   Existing source comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry.QuadraticTangents
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry.CurveCells
import Submission.Obl.k4_scalar_coefficient_clustering.Evaluation

/-!
The physical curve determined by a native quadratic test visits O(1/q)
q-cubes, with a fixed polynomial loss in the native whole-time bound.
-/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry

open Set

noncomputable section

/-- Reuse the accepted coefficient-Lipschitz estimate after bounding the
three coefficients from whole-time values. -/
theorem bounded_quadratic_value_lipschitz (a b c K : ℝ)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |a * t ^ 2 + b * t + c| ≤ K)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    |(a * s ^ 2 + b * s + c) - (a * t ^ 2 + b * t + c)| ≤ 57 * K * |s - t| := by
  obtain ⟨ha, hb, hc⟩ := bounded_quadratic_coefficients a b c K h
  let coeff : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2 ![c, b, a]
  have hnorm : ‖coeff‖ ≤ |c| + |b| + |a| := by
    simpa [coeff, Fin.sum_univ_three] using
      Submission.Obl.k4_adapted_oscillation_tests.norm_apply_le_sum_abs
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3))) (fun i => by simp) coeff
  have hcoeff : ‖coeff‖ ≤ 19 * K := by linarith
  have h' := Submission.Obl.k4_scalar_coefficient_clustering.quadratic_time_lipschitz
    hcoeff hs ht
  norm_num [Submission.Obl.k4_scalar_coefficient_clustering.quadratic, coeff,
    mul_comm, mul_left_comm, mul_assoc, add_comm, add_left_comm, add_assoc] at h' ⊢
  exact h'

theorem quadraticLift_cell_count (p v : Fin 3 → ℝ) (a b c K q : ℝ)
    (hK : 0 ≤ K) (hq : 0 < q) (hv : ∀ j, |v j| ≤ K)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |a * t ^ 2 + b * t + c| ≤ K)
    (C : Finset (Fin 4 → ℤ)) (t : (Fin 4 → ℤ) → ℝ)
    (ht : ∀ c ∈ C, t c ∈ Icc (0 : ℝ) 1)
    (hcode : ∀ cell ∈ C, ∀ j, ⌊quadraticLift p v a b c (t cell) j / q⌋ = cell j) :
    (C.card : ℝ) ≤ (2 / q + 3) * (114 * K + 5) ^ 4 := by
  have hcoord : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, ∀ j,
      |quadraticLift p v a b c s j - quadraticLift p v a b c t j| ≤ 57 * K * |s - t| := by
    intro s hs t ht j
    have hbase (i : Fin 3) : |(p i + s * v i) - (p i + t * v i)| ≤ 57 * K * |s - t| := by
      rw [show (p i + s * v i) - (p i + t * v i) = (s - t) * v i by ring, abs_mul]
      nlinarith [mul_le_mul_of_nonneg_left (hv i) (abs_nonneg (s - t)),
        mul_nonneg hK (abs_nonneg (s - t))]
    fin_cases j
    · simpa [quadraticLift, liftedVector] using hbase 0
    · simpa [quadraticLift, liftedVector] using hbase 1
    · simpa [quadraticLift, liftedVector] using hbase 2
    · simpa [quadraticLift, liftedVector] using bounded_quadratic_value_lipschitz a b c K h hs ht
  have hcount := trajectory_cell_count (fun s j => quadraticLift p v a b c s j)
    C t (57 * K) q (by positivity) hq hcoord ht hcode
  simpa only [Fintype.card_fin, show 2 * (57 * K) + 5 = 114 * K + 5 by ring] using hcount

/-- The native physical coordinates are the three base coordinates and the
evaluated native quadratic. -/
def nativePhysicalCurve (P : MvPolynomial (Fin 4) ℝ) (p v : Fin 4 → ℝ) (t : ℝ) :
    EuclideanSpace ℝ (Fin 4) :=
  liftedVector (fun j => p j.castSucc + t * v j.castSucc)
    (MvPolynomial.eval (fun j => p j + t * v j) P)

/-- Whole-time native bounds suffice for the trajectory/cube count; no
original coefficient envelope appears in the constant. -/
theorem native_curve_cell_count (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (p v : Fin 4 → ℝ) (K q : ℝ) (hK : 0 ≤ K) (hq : 0 < q)
    (hv : ∀ j : Fin 3, |v j.castSucc| ≤ K)
    (h : ∀ t ∈ Icc (0 : ℝ) 1, |MvPolynomial.eval (fun j => p j + t * v j) P| ≤ K)
    (C : Finset (Fin 4 → ℤ)) (t : (Fin 4 → ℤ) → ℝ)
    (ht : ∀ c ∈ C, t c ∈ Icc (0 : ℝ) 1)
    (hcode : ∀ cell ∈ C, ∀ j, ⌊nativePhysicalCurve P p v (t cell) j / q⌋ = cell j) :
    (C.card : ℝ) ≤ (2 / q + 3) * (114 * K + 5) ^ 4 := by
  obtain ⟨a, b, c, hquad, _⟩ := native_quadratic_tangents P hP p v K h
  have hbound : ∀ t ∈ Icc (0 : ℝ) 1, |a * t ^ 2 + b * t + c| ≤ K := by
    intro t ht
    simpa only [hquad] using h t ht
  apply quadraticLift_cell_count (fun j => p j.castSucc) (fun j => v j.castSucc)
    a b c K q hK hq hv hbound C t ht
  intro cell hcell j
  simpa only [nativePhysicalCurve, quadraticLift, hquad] using hcode cell hcell j

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry
