/-
Adapted from: here:o062
Original proof: x0511, branch x0511, commit bf52299; retained source-credit comment follows.
Owned source: Submission/Obl/k4_scalar_mesh_projection/SwitchSlice.lean.
-/

/- From o062 session x0511, branch x0511, commit bf52299;
original file Submission/Obl/k4_scalar_mesh_projection/SwitchSlice.lean. -/

import Submission.Lib.K4ScalarSwitching.SwitchPath

namespace Submission.Lib.K4ScalarSwitching.Switching

open MvPolynomial

def selectedControl (last : Fin 2) (i : Fin 3) : Fin 4 :=
  (![0, 1, Fin.natAdd 2 last] : Fin 3 → Fin 4) i

noncomputable def sliceValues (last : Fin 2) (w : ℝ) (k : Fin 4) :
    MvPolynomial (Fin 3) ℝ :=
  if k = 0 then X 0 else if k = 1 then X 1 else
    if k = Fin.natAdd 2 last then X 2 else C w

noncomputable def endpointSlice (last : Fin 2) (w : ℝ) :
    MvPolynomial (Fin 4) ℝ →ₐ[ℝ] MvPolynomial (Fin 3) ℝ :=
  aeval (sliceValues last w)

def slicePoint (last : Fin 2) (w : ℝ) (δ : Fin 3 → ℝ) (k : Fin 4) : ℝ :=
  if k = 0 then δ 0 else if k = 1 then δ 1 else
    if k = Fin.natAdd 2 last then δ 2 else w

theorem eval_endpointSlice (R : MvPolynomial (Fin 4) ℝ) (last : Fin 2)
    (w : ℝ) (δ : Fin 3 → ℝ) :
    eval δ (endpointSlice last w R) = eval (slicePoint last w δ) R := by
  rw [endpointSlice, eval_substitution]
  apply congrArg (fun f : Fin 4 → ℝ => eval f R)
  funext k
  fin_cases last <;> fin_cases k <;> simp [slicePoint, sliceValues]

/-- Freezing the complementary increment commutes with each of the three
selected coordinate derivatives. -/
theorem partial_endpointSlice (R : MvPolynomial (Fin 4) ℝ) (last : Fin 2)
    (w : ℝ) (i : Fin 3) :
    pderiv i (endpointSlice last w R) =
      endpointSlice last w (pderiv (selectedControl last i) R) := by
  unfold endpointSlice
  rw [partial_aeval]
  fin_cases last <;> fin_cases i <;>
    simp [sliceValues, selectedControl, Fin.sum_univ_succ, pderiv_X, Pi.single_apply]

/-- The three-variable endpoint Jacobian is exactly the selected maximal
minor of the four-variable switched endpoint. This is the determinant used
by the polynomial endpoint-volume estimate. -/
theorem slice_endpoint_jacobian (R : MvPolynomial (Fin 4) ℝ)
    (v : Fin 4 → ℝ) (last : Fin 2) (w : ℝ) (δ : Fin 3 → ℝ) :
    eval δ (endpointSlice last w (endpointMinor R v (Fin.natAdd 2 last))) =
      Matrix.det !![1, 1, 1; v 0, v 1, v (Fin.natAdd 2 last);
        eval δ (pderiv 0 (endpointSlice last w R)),
        eval δ (pderiv 1 (endpointSlice last w R)),
        eval δ (pderiv 2 (endpointSlice last w R))] := by
  rw [eval_endpointSlice, eval_endpointMinor]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [partial_endpointSlice, selectedControl, eval_endpointSlice]

end Submission.Lib.K4ScalarSwitching.Switching
