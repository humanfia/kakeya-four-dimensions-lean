-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.NativeCoreCoordinates, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/NativeCoreCoordinates.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/NativeCoreCoordinates.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 7287edefaa58;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeCoreCoordinates.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeCoreCoordinates.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.LocalNativeCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.QuarterCoreGeometry

/-! # Original signal values on a coherently chosen local native branch -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic

open MvPolynomial
open k4_stable_native_signal_oscillation

noncomputable section

theorem power_core_rootLift_coordinates (P : Poly) {K : ℝ} (hK : 0 < K) (R : ℕ)
    (c : EuclideanSpace ℝ (Fin 3)) (p : EuclideanSpace ℝ (Fin 4)) :
    Fin.snoc (fun j => c j + (K ^ R)⁻¹ * ((K ^ R) • (nativeBase p - c)) j)
        (rootLift P p 3) = fun j => rootLift P p j := by
  have hr := power_chart_reconstruction hK R (nativeBase p) c
  have hrj (j : Fin 3) : c j + (K ^ R)⁻¹ * ((K ^ R) • (nativeBase p - c)) j = nativeBase p j :=
    congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x j) hr
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rfl
  · rw [Fin.snoc_castSucc, hrj]
    have hb := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x j) (nativeBase_rootLift P p)
    rw [← hb]
    fin_cases j <;> rfl

/-- Exact corrected-root matching identifies the locally pulled-back
ORIGINAL signal with its value at that corrected root. No bound on the
signal value, coefficient height or local branch size is used. -/
theorem local_core_signal_value_eq_rootLift (P S : Poly)
    {K : ℝ} (hK : 0 < K) (R : ℕ) (c : EuclideanSpace ℝ (Fin 3))
    (p : EuclideanSpace ℝ (Fin 4)) (f : EuclideanSpace ℝ (Fin 3) → ℝ)
    (hmatch : rootLift P p 3 = f ((K ^ R) • (nativeBase p - c))) :
    let x := (K ^ R) • (nativeBase p - c)
    eval (Fin.snoc (fun j => x j) (f x)) (localNativePolynomial (fun j => c j) (K ^ R)⁻¹ S) =
      value S (rootLift P p) := by
  let x := (K ^ R) • (nativeBase p - c)
  have hlist : Fin.snoc (fun j => x j) (f x) = ![x 0, x 1, x 2, f x] := by
    ext j
    fin_cases j <;> rfl
  change eval (Fin.snoc (fun j => x j) (f x)) (localNativePolynomial _ _ _) = _
  rw [hlist, localNativePolynomial_eval]
  have heq : Fin.snoc (fun j => c j + (K ^ R)⁻¹ * x j) (f x) = fun j => rootLift P p j := by
    rw [← hmatch]
    exact power_core_rootLift_coordinates P hK R c p
  rw [heq]
  rfl

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
