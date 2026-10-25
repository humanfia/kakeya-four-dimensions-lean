-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripPolynomials, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripPolynomials.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripPolynomials.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripPolynomials.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripPolynomials.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripFormat
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripObservation
import Submission.Obl.k4_eligibility_sign_description.Signs

/-! Affine polynomial tests for the actual parent-normalized strip assignments. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MvPolynomial
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open Submission.Obl.k4_eligibility_sign_description
open scoped RealInnerProductSpace BigOperators

def stripPositionPolys (t : ℝ) : Fin 2 → MvPolynomial (Fin 6) ℝ :=
  ![X 0 + C t * X 3, X 1 + C t * X 4]

def stripVelocityPolys : Fin 2 → MvPolynomial (Fin 6) ℝ := ![X 3, X 4]

private theorem stripPositionPolys_degree (t : ℝ) (j : Fin 2) :
    (stripPositionPolys t j).totalDegree ≤ 1 := by
  fin_cases j <;>
    exact degree_add_le (by simp) ((degree_C_mul_le _ _).trans (by simp))

private theorem stripVelocityPolys_degree (j : Fin 2) :
    (stripVelocityPolys j).totalDegree ≤ 1 := by
  fin_cases j <;> simp [stripVelocityPolys]

def packetNormalPositionPoly (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u n : StripSpace)
    (t : ℝ) : MvPolynomial (Fin 6) ℝ :=
  ∑ i, C (n i) * (∑ j, C (Q⁻¹ i j) *
    (stripPositionPolys t j - C (c j) - C (t * u j)))

def packetNormalVelocityPoly (q : ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ) (u n : StripSpace)
    (β : ℝ) : MvPolynomial (Fin 6) ℝ :=
  C q * (∑ i, C (n i) * (∑ j, C (Q⁻¹ i j) * (stripVelocityPolys j - C (u j)))) - C β

def packetMidpointBinPoly (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u n : StripSpace)
    (t₀ q r : ℝ) : MvPolynomial (Fin 6) ℝ :=
  C r⁻¹ * packetNormalPositionPoly Q c u n (t₀ + q / 2)

theorem packetNormalPositionPoly_degree (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u n : StripSpace)
    (t : ℝ) : (packetNormalPositionPoly Q c u n t).totalDegree ≤ 1 := by
  apply degree_sum_le
  intro i _
  apply (degree_C_mul_le _ _).trans
  apply degree_sum_le
  intro j _
  apply (degree_C_mul_le _ _).trans
  exact degree_sub_le (degree_sub_le (stripPositionPolys_degree t j) (by simp))
    (by rw [totalDegree_C]; omega)

theorem packetNormalVelocityPoly_degree (q : ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (u n : StripSpace) (β : ℝ) :
    (packetNormalVelocityPoly q Q u n β).totalDegree ≤ 1 := by
  apply degree_sub_le _ (by simp)
  apply (degree_C_mul_le _ _).trans
  apply degree_sum_le
  intro i _
  apply (degree_C_mul_le _ _).trans
  apply degree_sum_le
  intro j _
  apply (degree_C_mul_le _ _).trans
  exact degree_sub_le (stripVelocityPolys_degree j) (by simp)

theorem packetMidpointBinPoly_degree (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u n : StripSpace)
    (t₀ q r : ℝ) : (packetMidpointBinPoly Q c u n t₀ q r).totalDegree ≤ 1 :=
  (degree_C_mul_le _ _).trans (packetNormalPositionPoly_degree _ _ _ _ _)

theorem eval_packetNormalPositionPoly (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u n : StripSpace)
    (t : ℝ) (copy : ℕ) (z : Fin 6 → ℝ) :
    MvPolynomial.eval z (packetNormalPositionPoly Q c u n t) =
      inner ℝ (packetPosition Q c u (copy, z) t) n := by
  simp [packetNormalPositionPoly, stripPositionPolys, packetPosition, gy, gx,
    PiLp.inner_apply, Fin.sum_univ_two, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]

theorem eval_packetNormalVelocityPoly (q : ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (u n : StripSpace) (β : ℝ) (copy : ℕ) (z : Fin 6 → ℝ) :
    MvPolynomial.eval z (packetNormalVelocityPoly q Q u n β) =
      inner ℝ (packetVelocity q Q u (copy, z)) n - β := by
  simp [packetNormalVelocityPoly, stripVelocityPolys, packetVelocity, gv,
    PiLp.inner_apply, Fin.sum_univ_two, Matrix.toLpLin_apply, Matrix.vecHead, Matrix.vecTail]
  ring

theorem eval_packetMidpointBinPoly (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u n : StripSpace)
    (t₀ q r : ℝ) (copy : ℕ) (z : Fin 6 → ℝ) :
    MvPolynomial.eval z (packetMidpointBinPoly Q c u n t₀ q r) =
      inner ℝ (packetPosition Q c u (copy, z) (t₀ + q / 2)) n / r := by
  rw [packetMidpointBinPoly, map_mul, eval_C,
    eval_packetNormalPositionPoly Q c u n (t₀ + q / 2) copy z]
  ring

/-- The actual normalized trajectory pieces meet the frozen Boolean format
with a fixed degree and a test count linear in the representative family. -/
theorem packetStripAssignment_format {m D : ℕ} {H w r : ℝ}
    (A : Set (Fin 6 → ℝ)) (copy : ℕ) (Q : Matrix (Fin 2) (Fin 2) ℝ) (c u : StripSpace)
    (t₀ q : ℝ) (n : Fin m → StripSpace) (β : Fin m → ℝ) (i : Fin m) (z : ℤ)
    (hA : gfmt 6 H D A) :
    gfmt 6 (H + 2 * (m : ℝ) + 2) (max D 1)
      (stripAssignment A (fun a => packetVelocity q Q u (copy, a))
        (fun a => packetPosition Q c u (copy, a) (t₀ + q / 2)) n β w r i z) := by
  apply stripAssignment_format A _ _ n β i z
    (fun j => packetNormalVelocityPoly q Q u (n j) (β j))
    (packetMidpointBinPoly Q c u (n i) t₀ q r)
    (fun j => packetNormalVelocityPoly_degree _ _ _ _ _)
    (packetMidpointBinPoly_degree _ _ _ _ _ _ _) _ _ hA
  · intro a j
    exact eval_packetNormalVelocityPoly _ _ _ _ _ _ _
  · intro a
    exact eval_packetMidpointBinPoly _ _ _ _ _ _ _ _ _

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
