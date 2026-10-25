-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.NativeEquation, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/NativeEquation.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/NativeEquation.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit 111b78d1fe6b;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeEquation.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o204,
   session x0747, commit 6bac7a735eff217ed0d1bc0b350cf47156162ca4, file Submission/Obl/k4_uniform_sampled_isotropic_branches/NativeEquation.lean.
   Any earlier attribution is retained below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.DiscriminantPreparation
import Submission.Obl.k4_stable_native_signal_oscillation.ExactRootBasic
import Submission.Obl.k4_stable_native_signal_oscillation.RootCorrection

/-! # Matching exact signed sheets to the original native equation -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MvPolynomial MeasureTheory
open k4_stable_native_signal_oscillation k4_quadratic_atlas_normalization

noncomputable section

/-- The discriminant controlled by the original law is exactly the
three-variable discriminant of the hidden quadratic equation. -/
theorem native_equation_discriminant (P : MvPolynomial (Fin 4) ℝ) :
    baseDiscriminant P = (restrictBase (pderiv 3 P)) ^ 2 -
      C (4 * (curvature P 3 / 2)) * restrictBase P := by
  have hscalar : 4 * (curvature P 3 / 2) = 2 * curvature P 3 := by ring
  change restrictBase ((pderiv 3 P) ^ 2 - C (2 * curvature P 3) * P) = _
  simp [hscalar, restrictBase]

/-- Two real roots whose derivatives have the same strict sign coincide,
including the case of a vanishing quadratic coefficient. -/
theorem quadratic_roots_unique_of_common_derivative_sign
    (a b c x y σ : ℝ) (hx : a * x ^ 2 + b * x + c = 0)
    (hy : a * y ^ 2 + b * y + c = 0)
    (hsx : 0 < (2 * a * x + b) * σ)
    (hsy : 0 < (2 * a * y + b) * σ) : x = y := by
  by_contra hne
  have hfactor : (x - y) * (a * (x + y) + b) = 0 := by
    linear_combination hx - hy
  have hsum : a * (x + y) + b = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne)
  have hz : (2 * a * x + b) * σ + (2 * a * y + b) * σ = 0 := by
    linear_combination 2 * σ * hsum
  linarith

/-- The actual hidden derivative in the base-polynomial coordinates. -/
theorem native_equation_derivative
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc z w) (pderiv 3 P) =
      2 * (curvature P 3 / 2) * w + eval z (restrictBase (pderiv 3 P)) := by
  have hder := quadratic_coordinate_derivative P hP (Fin.snoc z 0) 3 w
  change eval (Function.update (Fin.snoc z 0) (Fin.last 3) (0 + w)) (pderiv 3 P) =
    eval (Fin.snoc z 0) (pderiv 3 P) + curvature P 3 * w at hder
  rw [zero_add, update_snoc_hidden, ← eval_restrictBase] at hder
  convert hder using 1 <;> ring

/-- Signed branches of the decomposed equation are the actual roots of
P. This is a pointwise identity and requires no choice of approximate root. -/
theorem native_equation_signed_root_unique
    (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) (w f σ : ℝ)
    (hw : eval (Fin.snoc z w) P = 0)
    (hf : (curvature P 3 / 2) * f ^ 2 +
      eval z (restrictBase (pderiv 3 P)) * f + eval z (restrictBase P) = 0)
    (hsw : 0 < eval (Fin.snoc z w) (pderiv 3 P) * σ)
    (hsf : 0 < (2 * (curvature P 3 / 2) * f +
      eval z (restrictBase (pderiv 3 P))) * σ) : w = f := by
  have hsw' : 0 < (2 * (curvature P 3 / 2) * w +
      eval z (restrictBase (pderiv 3 P))) * σ := by
    simpa only [native_equation_derivative P hP] using hsw
  apply quadratic_roots_unique_of_common_derivative_sign (curvature P 3 / 2)
    (eval z (restrictBase (pderiv 3 P))) (eval z (restrictBase P)) w f σ ?_ hf hsw' hsf
  rw [eval_snoc_quadratic P hP] at hw
  change eval z (restrictBase P) + eval z (restrictBase (pderiv 3 P)) * w +
    curvature P 3 * w ^ 2 / 2 = 0 at hw
  convert hw using 1 <;> ring

/-- A branch with the corrected root's sign predicts the OLD native
signal on the original point. The error is the imported scale-invariant
root-correction estimate, not a coefficient-envelope estimate. -/
theorem native_root_signal_prediction
    (P S : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (hS : S.totalDegree ≤ 2) {K a : ℝ} (hK : 2 ≤ K)
    (ha : 0 < a) (ha1 : a ≤ 1) (hc : |curvature P 3| ≤ (K ^ 5 * a)⁻¹)
    (p : EuclideanSpace ℝ (Fin 4))
    (hr : |value P p| ≤ K * a) (hd : K⁻¹ ≤ |value (pderiv 3 P) p|)
    (hS1 : |value (pderiv 3 S) p| ≤ K) (hS2 : |curvature S 3| ≤ K)
    (f σ : ℝ)
    (hf : (curvature P 3 / 2) * f ^ 2 +
      eval (fun i => nativeBase p i) (restrictBase (pderiv 3 P)) * f +
      eval (fun i => nativeBase p i) (restrictBase P) = 0)
    (hsf : 0 < (2 * (curvature P 3 / 2) * f +
      eval (fun i => nativeBase p i) (restrictBase (pderiv 3 P))) * σ)
    (hsp : 0 < value (pderiv 3 P) (rootLift P p) * σ) :
    |eval (Fin.snoc (fun i => nativeBase p i) f) S - value S p| ≤ K ^ 14 * a := by
  obtain ⟨hroot, _, herror⟩ := rootLift_spec P S hP hS hK ha ha1 hc p hr hd hS1 hS2
  have hcoords : (Fin.snoc (fun i => nativeBase p i) (rootLift P p 3) : Fin 4 → ℝ) =
      fun i => rootLift P p i := by
    have he := nativeBase_rootLift P p
    rw [← he]
    funext i
    fin_cases i <;> rfl
  have hw := native_equation_signed_root_unique P hP (fun i => nativeBase p i)
    (rootLift P p 3) f σ (by simpa only [hcoords, value] using hroot) hf
    (by simpa only [hcoords, value] using hsp) hsf
  rw [← hw, hcoords]
  exact herror

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
