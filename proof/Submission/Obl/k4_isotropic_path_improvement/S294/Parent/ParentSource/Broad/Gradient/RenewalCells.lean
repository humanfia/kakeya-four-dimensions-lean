-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.RenewalCells, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/RenewalCells.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/RenewalCells.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit b13a9e17a6c8;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/RenewalCells.lean. Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/RenewalCells.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.RenewalCellScale
import Submission.Lib.K4MovingMeshBoxes.Geometry
import Submission.Lib.K4QuadraticSheets.JetBins

/-! # Explicit measurable fine-base cells for gradient renewal -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set

noncomputable section

def renewalCellMesh (K : ℝ) (J q : ℕ) : ℝ := (K ^ (4 * J + q + 14))⁻¹

def renewalCellCode (K : ℝ) (J q : ℕ) (z : EuclideanSpace ℝ (Fin 3)) : Fin 3 → ℤ :=
  fun j => ⌊z j / renewalCellMesh K J q⌋

theorem measurable_renewalCellCode (K : ℝ) (J q : ℕ) : Measurable (renewalCellCode K J q) := by
  apply measurable_pi_iff.mpr
  intro j
  exact Int.measurable_floor.comp (((PiLp.continuous_apply 2 _ j).measurable).div_const _)

/-- The actual global floor code has diameter at most the concrete
renewal radius. No center witness or geometry certificate is supplied. -/
theorem renewalCellCode_diameter {K : ℝ} (hK : 2 ≤ K) (J q : ℕ)
    {z w : EuclideanSpace ℝ (Fin 3)} (hcode : renewalCellCode K J q z = renewalCellCode K J q w) :
    ‖z - w‖ ≤ renewalCellRadius K J q := by
  have hKp : 0 < K := by linarith
  have hm : 0 < renewalCellMesh K J q := by dsimp only [renewalCellMesh]; positivity
  have hcoord (j : Fin 3) : |z j - w j| ≤ renewalCellMesh K J q :=
    (Submission.Lib.K4QuadraticSheets.abs_sub_lt_of_floor_eq hm (congrFun hcode j)).le
  have hK2 : (4 : ℝ) ≤ K ^ 2 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hK 2
    norm_num at hh
    exact hh
  have hsmall : 3 * (K ^ 2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv]
    exact (div_le_one (pow_pos hKp 2)).mpr (by linarith)
  have hpow : K ^ (4 * J + q + 14) = K ^ (4 * J + q + 12) * K ^ 2 := by rw [← pow_add]
  calc
    ‖z - w‖ ≤ ∑ j, |(z - w) j| := Native.euclidean_norm_le_sum_abs _
    _ ≤ ∑ _j : Fin 3, renewalCellMesh K J q := Finset.sum_le_sum (fun j _ => hcoord j)
    _ = 3 * renewalCellMesh K J q := by simp
    _ = (3 * (K ^ 2)⁻¹) * renewalCellRadius K J q := by
      dsimp only [renewalCellMesh, renewalCellRadius]
      rw [hpow, mul_inv_rev]
      ring
    _ ≤ 1 * renewalCellRadius K J q := mul_le_mul_of_nonneg_right hsmall
      (by dsimp only [renewalCellRadius]; positivity)
    _ = _ := one_mul _

/-- A fine comparison core meets at most one explicit fixed power of K
geometric states. The exponent is independent of path formats. -/
theorem renewalCellCode_finite_core {K : ℝ} (hK : 2 ≤ K) (J q : ℕ)
    (E : Set (EuclideanSpace ℝ (Fin 3)))
    (hE : E ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ∃ Codes : Finset (Fin 3 → ℤ), (Codes.card : ℝ) ≤ K ^ (12 * J + 3 * q + 51) ∧
      ∀ z ∈ E, renewalCellCode K J q z ∈ Codes := by
  classical
  have hKp : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hm : 0 < renewalCellMesh K J q := by dsimp only [renewalCellMesh]; positivity
  obtain ⟨B, hB, hcover⟩ := Submission.Lib.K4MovingMeshBoxes.interval_mesh_cover
    hm (by norm_num : (0 : ℝ) ≤ 1) 0
  have h6 : (6 : ℝ) ≤ K ^ 3 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hK 3
    norm_num at hh
    linarith
  have hBpower : (B.card : ℝ) ≤ K ^ ((4 * J + q + 14) + 3) := by
    calc
      _ ≤ 4 / renewalCellMesh K J q + 2 := by simpa only [mul_one] using hB
      _ = 4 * K ^ (4 * J + q + 14) + 2 := by dsimp only [renewalCellMesh]; rw [div_inv_eq_mul]
      _ ≤ 6 * K ^ (4 * J + q + 14) := by
        have hh := one_le_pow₀ hK1 (n := 4 * J + q + 14)
        linarith
      _ ≤ K ^ 3 * K ^ (4 * J + q + 14) := mul_le_mul_of_nonneg_right h6 (by positivity)
      _ = _ := by rw [pow_add]; ring
  let Codes : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun _ => B)
  refine ⟨Codes, ?_, ?_⟩
  · calc
      (Codes.card : ℝ) = (B.card : ℝ) ^ 3 := by simp [Codes, Fintype.card_piFinset]
      _ ≤ (K ^ ((4 * J + q + 14) + 3)) ^ 3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hBpower 3
      _ = _ := by rw [← pow_mul]; congr 1; omega
  · intro z hz
    apply Fintype.mem_piFinset.mpr
    intro j
    have hnorm : ‖z‖ ≤ 1 := by simpa only [Metric.mem_closedBall, dist_zero_right] using hE hz
    exact hcover (z j) (by simpa only [sub_zero, Real.norm_eq_abs] using
      (PiLp.norm_apply_le z j).trans hnorm)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
