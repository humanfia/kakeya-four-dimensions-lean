-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.NativeCube, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/NativeCube.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/NativeCube.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeCube.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeCube.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.LocalNativeCoordinates

/-! # Native hidden units and a unit base cube -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

open MvPolynomial Set
open k4_quadratic_atlas_normalization

noncomputable section

def nativeCubeCenter (κ : ℝ) : Fin 3 → ℝ := ![0, -κ, -κ]

def nativeCubeMatrix (κ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal ![1, 2 * κ, 2 * κ]

/-- The actual base is sent to the unit cube; only the hidden coordinate
uses the native derivative unit B/a. -/
def nativeCubePoint (κ B a : ℝ) (x : Fin 4 → ℝ) : Fin 4 → ℝ :=
  ![x 0, (x 1 + κ) / (2 * κ), (x 2 + κ) / (2 * κ), (B / a) * x 3]

/-- Pull back a frame-normalized polynomial through the exact inverse
of nativeCubePoint. -/
def nativeCubeTest (κ B a : ℝ) (P : Poly) : Poly :=
  transportPolynomial (nativeCubeCenter κ) (nativeCubeMatrix κ) (a / B) P

theorem nativeCubeTest_totalDegree (κ B a : ℝ) (P : Poly) :
    (nativeCubeTest κ B a P).totalDegree ≤ P.totalDegree :=
  totalDegree_transportPolynomial_le _ _ _ _

theorem nativeCube_coordinate_identity {κ B a : ℝ}
    (hκ : κ ≠ 0) (hB : B ≠ 0) (ha : a ≠ 0) (x : Fin 4 → ℝ) :
    coordinateMap (nativeCubeCenter κ) (nativeCubeMatrix κ) (a / B)
      (nativeCubePoint κ B a x) = x := by
  funext i
  fin_cases i <;>
    simp [coordinateMap, nativeCubeCenter, nativeCubeMatrix, nativeCubePoint,
      Matrix.diagonal] <;> field_simp <;> ring

theorem nativeCubeTest_eval {κ B a : ℝ}
    (hκ : κ ≠ 0) (hB : B ≠ 0) (ha : a ≠ 0) (P : Poly) (x : Fin 4 → ℝ) :
    eval (nativeCubePoint κ B a x) (nativeCubeTest κ B a P) = eval x P := by
  rw [nativeCubeTest, eval_transportPolynomial, nativeCube_coordinate_identity hκ hB ha]

theorem nativeCubeTest_derivatives {κ B a : ℝ}
    (hκ : κ ≠ 0) (hB : B ≠ 0) (ha : a ≠ 0) (P : Poly) (x : Fin 4 → ℝ) :
    eval (nativeCubePoint κ B a x) (pderiv 3 (nativeCubeTest κ B a P)) =
        (a / B) * eval x (pderiv 3 P) ∧
      eval (nativeCubePoint κ B a x) (pderiv 3 (pderiv 3 (nativeCubeTest κ B a P))) =
        (a / B) ^ 2 * eval x (pderiv 3 (pderiv 3 P)) := by
  simpa only [nativeCubeTest, nativeCube_coordinate_identity hκ hB ha] using
    eval_transport_hidden_derivatives (nativeCubeCenter κ) (nativeCubeMatrix κ) (a / B) P
      (nativeCubePoint κ B a x)

/-- The unit-base requirement is a consequence of actual bounded native
coordinates, with no bound on the hidden value. -/
theorem nativeCube_base_mem_unit {κ B a : ℝ} (hκ : 0 < κ) (x : Fin 4 → ℝ)
    (ht : x 0 ∈ Icc (0 : ℝ) 1) (hy1 : |x 1| ≤ κ) (hy2 : |x 2| ≤ κ) :
    (fun j : Fin 3 => nativeCubePoint κ B a x j.castSucc) ∈ Icc 0 1 := by
  have hden : 0 < 2 * κ := by positivity
  have hcoord (t : ℝ) (ht : |t| ≤ κ) : 0 ≤ (t + κ) / (2 * κ) ∧
      (t + κ) / (2 * κ) ≤ 1 := by
    have hh := abs_le.mp ht
    constructor
    · exact div_nonneg (by linarith) hden.le
    · exact (div_le_one hden).mpr (by linarith)
  constructor <;> intro j <;> fin_cases j
  · exact ht.1
  · exact (hcoord _ hy1).1
  · exact (hcoord _ hy2).1
  · exact ht.2
  · exact (hcoord _ hy1).2
  · exact (hcoord _ hy2).2

/-- Normalizing the hidden derivative cancels B/a in BOTH derivative
bounds, and preserves the selected original derivative floor. -/
theorem nativeCubeTest_native_bounds {κ B a : ℝ}
    (hκ : 0 < κ) (hB : 0 < B) (ha : 0 < a) (P : Poly) (x : Fin 4 → ℝ)
    (hfirst : |eval x (pderiv 3 P)| ≤ κ * (B / a))
    (hsecond : |eval x (pderiv 3 (pderiv 3 P))| ≤ κ * (B / a) ^ 2)
    (hfloor : B / a / κ ≤ |eval x (pderiv 3 P)|) :
    κ⁻¹ ≤ |eval (nativeCubePoint κ B a x) (pderiv 3 (nativeCubeTest κ B a P))| ∧
      |eval (nativeCubePoint κ B a x) (pderiv 3 (nativeCubeTest κ B a P))| ≤ κ ∧
      |eval (nativeCubePoint κ B a x)
        (pderiv 3 (pderiv 3 (nativeCubeTest κ B a P)))| ≤ κ := by
  obtain ⟨h1, h2⟩ := nativeCubeTest_derivatives hκ.ne' hB.ne' ha.ne' P x
  simp only [h1, h2, abs_mul, abs_pow, abs_of_pos (div_pos ha hB)]
  refine ⟨?_, ?_, ?_⟩
  · have hh := mul_le_mul_of_nonneg_left hfloor (div_pos ha hB).le
    convert hh using 1 <;> field_simp
  · have hh := mul_le_mul_of_nonneg_left hfirst (div_pos ha hB).le
    convert hh using 1 <;> field_simp
  · have hh := mul_le_mul_of_nonneg_left hsecond (sq_nonneg (a / B))
    convert hh using 1 <;> field_simp


end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
