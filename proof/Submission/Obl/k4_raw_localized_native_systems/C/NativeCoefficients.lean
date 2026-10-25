import Submission.Obl.k4_raw_localized_native_systems.C.PacketInterfaces
import Submission.Obl.k4_raw_localized_native_systems.C.ScalarAssignments

/-
Adapted from this LOT tree, o178, session x0596, `NativeCoefficients.lean` (commit ec5e1086),
renamed from `Submission.Obl.k4_unbounded_geometric_packet_reduction` into `Submission.Obl.k4_raw_localized_native_systems.C`.
-/

namespace Submission.Obl.k4_raw_localized_native_systems.C

open MvPolynomial
open Submission.Lib.K4XInterface
open Submission.Obl.k4_finite_width_output_exclusion

noncomputable section

/-- The explicit interpolation coefficients in the geometric interface are
the polynomial coefficient map used by the scalar recovery implementation. -/
theorem nativeCoeff_eq_clipped (P : MvPolynomial (Fin 4) ℝ)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) (A : Set Traj) :
    nativeCoeff P t₀ q a v A = clippedScalarCoeff P t₀ q a v A := by
  classical
  funext l
  by_cases hl : l ∈ A
  · rw [clippedScalarCoeff_eq P t₀ q a v hl]
    ext i
    fin_cases i <;>
      simp [nativeCoeff, hl, scalarCoeff, scalarCoeffPoly, eval_nativeAt,
        eval_tangentAt, tangentBase, Function.comp_def, gx, x]
  · simp [nativeCoeff, clippedScalarCoeff, hl]

/-- Clipping the polynomial native interpolation to a measurable full
assignment gives the globally measurable scalar coefficient map. -/
theorem nativeCoeff_measurable (P : MvPolynomial (Fin 4) ℝ)
    (t₀ q a : ℝ) (v : Fin 3 → ℝ) {A : Set Traj} (hA : MeasurableSet A) :
    Measurable (nativeCoeff P t₀ q a v A) := by
  rw [nativeCoeff_eq_clipped]
  exact clippedScalarCoeff_measurable P t₀ q a v hA

end
end Submission.Obl.k4_raw_localized_native_systems.C
