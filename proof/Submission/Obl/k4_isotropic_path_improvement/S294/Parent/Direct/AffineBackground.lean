-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Direct.AffineBackground, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/Direct/AffineBackground.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Lib.K4ContactNormalization.ResidualNormalization
import Submission.Lib.K4GlobalParentSignal
import Submission.Obl.k4_stable_native_signal_oscillation.Hidden

/-!
Subtracting an affine hidden sheet from the physical parent signal.

The resulting signal is still a quadratic polynomial, has the SAME two
hidden derivatives as the original parent, and is small on an old block
whenever the original hidden coordinate is close to the affine sheet.
These facts do not construct a common velocity palette.
-/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Direct

open MvPolynomial Set
open Submission.Lib.K4ChartLifting
open Submission.Lib.K4ContactNormalization
open Submission.Lib.K4GlobalParentSignal

noncomputable section

/-- Replace only the hidden coordinate by the affine sheet. -/
def affineSheetSubst (L : Fin 4 → ℝ) (i : Fin 4) : MvPolynomial (Fin 4) ℝ :=
  if i = 3 then affineBase L else X i

/-- The physical parent restricted to the affine sheet, still in four
variables and independent of the last variable. -/
def affineBackground (L : Fin 4 → ℝ) (P : Po) : Po :=
  bind₁ (affineSheetSubst L) P

/-- The physical signal minus its known conservative background. -/
def affineResidual (L : Fin 4 → ℝ) (P : Po) : Po := P - affineBackground L P

theorem affineBackground_degree (L : Fin 4 → ℝ) (P : Po) :
    (affineBackground L P).totalDegree ≤ P.totalDegree := by
  apply Submission.Lib.K4ChartLifting.totalDegree_bind₁_le_of_le_one
  intro i
  by_cases hi : i = 3
  · simpa only [affineSheetSubst, ite_eq_left hi] using affineBase_degree L
  · simp only [affineSheetSubst, ite_eq_right hi]
    exact (totalDegree_X _).le

theorem affineResidual_degree (L : Fin 4 → ℝ) (P : Po) :
    (affineResidual L P).totalDegree ≤ P.totalDegree :=
  (totalDegree_sub _ _).trans (max_le le_rfl (affineBackground_degree L P))

theorem eval_affineBackground (L : Fin 4 → ℝ) (P : Po) (z : Fin 4 → ℝ) :
    eval z (affineBackground L P) =
      eval (Function.update z 3 (L 0 + L 1*z 0 + L 2*z 1 + L 3*z 2)) P := by
  rw [affineBackground, eval_bind₁']
  have hz : (fun i => eval z (affineSheetSubst L i)) =
      Function.update z 3 (L 0 + L 1*z 0 + L 2*z 1 + L 3*z 2) := by
    funext i
    by_cases hi : i = 3
    · subst i
      simp [affineSheetSubst, affineBase]
    · simp [affineSheetSubst, hi]
  rw [hz]

theorem pderiv_affineBackground (L : Fin 4 → ℝ) (P : Po) :
    pderiv (3 : Fin 4) (affineBackground L P) = 0 := by
  have hs (i : Fin 4) : pderiv (3 : Fin 4) (affineSheetSubst L i) = 0 := by
    fin_cases i <;> simp [affineSheetSubst, affineBase, pderiv_X]
  simp [affineBackground, pderiv_bind₁, hs]

theorem pderiv_affineResidual (L : Fin 4 → ℝ) (P : Po) :
    pderiv (3 : Fin 4) (affineResidual L P) = pderiv (3 : Fin 4) P := by
  simp [affineResidual, pderiv_affineBackground]

theorem second_pderiv_affineResidual (L : Fin 4 → ℝ) (P : Po) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (affineResidual L P)) =
      pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P) := by
  rw [pderiv_affineResidual]

/-- Native hidden jets retain their original units; no derivative of the
old chart test appears in this assertion. -/
theorem affineResidual_hidden_jets (L : Fin 4 → ℝ) (P : Po)
    (z : Fin 4 → ℝ) {K B : ℝ}
    (hfirst : |eval z (pderiv (3 : Fin 4) P)| ≤ K*B)
    (hsecond : |eval z (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K*B^2) :
    |eval z (pderiv (3 : Fin 4) (affineResidual L P))| ≤ K*B ∧
      |eval z (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (affineResidual L P)))| ≤
        K*B^2 := by
  simpa only [pderiv_affineResidual] using And.intro hfirst hsecond

/-- Exact physical-height bound after subtracting the affine sheet.
The original parent jets are evaluated on the actual original point. -/
theorem affineResidual_value_bound (L : Fin 4 → ℝ) (P : Po)
    (hP : P.totalDegree ≤ 2) (z : Fin 4 → ℝ)
    {K B a C : ℝ} (hK : 0 ≤ K) (hB : 0 < B) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hfirst : |eval z (pderiv (3 : Fin 4) P)| ≤ K*B)
    (hsecond : |Submission.Obl.k4_quadratic_atlas_normalization.curvature P 3| ≤ K*B^2)
    (hclose : |z 3 - (L 0 + L 1*z 0 + L 2*z 1 + L 3*z 2)| ≤ C*a/B) :
    |eval z (affineResidual L P)| ≤ K*C*a + K*C^2*a^2/2 := by
  let d := L 0 + L 1*z 0 + L 2*z 1 + L 3*z 2 - z 3
  have hd : |d| ≤ C*a/B := by simpa only [d, abs_sub_comm] using hclose
  have ht := Submission.Obl.k4_stable_native_signal_oscillation.quadratic_coordinate_taylor
    P hP z (3 : Fin 4) d
  have heq : eval z (affineResidual L P) =
      -(eval z (pderiv (3 : Fin 4) P)*d +
        Submission.Obl.k4_quadratic_atlas_normalization.curvature P 3*d^2/2) := by
    rw [affineResidual, map_sub, eval_affineBackground]
    have hz : z 3+d = L 0 + L 1*z 0 + L 2*z 1 + L 3*z 2 := by dsimp [d]; ring
    rw [hz] at ht
    rw [ht]
    ring
  rw [heq, abs_neg]
  calc
    _ ≤ |eval z (pderiv (3 : Fin 4) P)*d| +
        |Submission.Obl.k4_quadratic_atlas_normalization.curvature P 3*d^2/2| :=
      abs_add_le _ _
    _ = |eval z (pderiv (3 : Fin 4) P)| * |d| +
        |Submission.Obl.k4_quadratic_atlas_normalization.curvature P 3| * |d| ^ 2/2 := by
      rw [abs_mul, abs_div, abs_mul, abs_pow]
      norm_num
    _ ≤ (K*B)*(C*a/B) + (K*B^2)*(C*a/B)^2/2 := by
      gcongr
    _ = _ := by field_simp

theorem affineResidual_value_scale (L : Fin 4 → ℝ) (P : Po)
    (hP : P.totalDegree ≤ 2) (z : Fin 4 → ℝ)
    {K B a C : ℝ} (hK : 0 ≤ K) (hB : 0 < B) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hC : 0 ≤ C)
    (hfirst : |eval z (pderiv (3 : Fin 4) P)| ≤ K*B)
    (hsecond : |Submission.Obl.k4_quadratic_atlas_normalization.curvature P 3| ≤ K*B^2)
    (hclose : |z 3 - (L 0 + L 1*z 0 + L 2*z 1 + L 3*z 2)| ≤ C*a/B) :
    |eval z (affineResidual L P)| ≤ K*(C+C^2)*a := by
  have h := affineResidual_value_bound L P hP z hK hB ha hC hfirst hsecond hclose
  have ha2 : a^2 ≤ a := by nlinarith
  have hka : K*C^2*a^2 ≤ K*C^2*a :=
    mul_le_mul_of_nonneg_left ha2 (by positivity)
  have hn : 0 ≤ K*C^2*a^2 := by positivity
  nlinarith only [h, hka, hn]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Direct
