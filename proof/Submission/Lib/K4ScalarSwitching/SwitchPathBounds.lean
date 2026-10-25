/-
Adapted from: here:o062
Original proof: x0511, branch x0511, commit bf52299; retained source-credit comment follows.
Owned source: Submission/Obl/k4_scalar_mesh_projection/SwitchPathBounds.lean.
-/

/- From o062 session x0511, branch x0511, commit bf52299;
original file Submission/Obl/k4_scalar_mesh_projection/SwitchPathBounds.lean. -/

import Submission.Lib.K4ScalarSwitching.SwitchSlice
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

namespace Submission.Lib.K4ScalarSwitching.Switching

open MvPolynomial
open Submission.Lib.K4PolynomialPotential
open Submission.Lib.K4ScalarSwitching.PolynomialDegree

theorem legPoint_degree (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (j : Fin 4) (d : Fin 2) :
    (legPoint x v j d).totalDegree ≤ 1 := by
  unfold legPoint
  apply degree_add_le
  · apply degree_add_le
    · simp
    · apply degree_sum_le
      intro k hk
      split_ifs
      · exact (degree_C_mul_le _ _).trans (by simp)
      · simp
  · exact (degree_C_mul_le _ _).trans (by simp)

theorem legField_degree (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (j : Fin 4) :
    (legField A B x v j).totalDegree ≤ max A.totalDegree B.totalDegree := by
  unfold legField
  apply (totalDegree_add _ _).trans
  exact max_le_max (degree_aeval_le _ _ (legPoint_degree x v j))
    ((degree_C_mul_le _ _).trans (degree_aeval_le _ _ (legPoint_degree x v j)))

theorem upperSubst_degree {σ : Type*} (j : σ) (P : MvPolynomial (σ ⊕ Unit) ℝ) :
    (upperSubst j P).totalDegree ≤ P.totalDegree := by
  apply degree_aeval_le
  intro k
  cases k <;> simp

theorem upperPrimitive_degree {σ : Type*} (j : σ) (P : MvPolynomial (σ ⊕ Unit) ℝ) :
    (upperPrimitive j P).totalDegree ≤ P.totalDegree + 1 :=
  (upperSubst_degree j _).trans (polynomialPrimitive_totalDegree _ P)

/-- The simulated height has fixed degree one more than the row field,
independently of the start and of all four velocities. -/
theorem brokenHeight_degree (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) :
    (brokenHeight A B x v).totalDegree ≤ max A.totalDegree B.totalDegree + 1 := by
  unfold brokenHeight
  apply totalDegree_finsetSum_le
  intro j hj
  exact (upperPrimitive_degree _ _).trans (Nat.add_le_add_right (legField_degree A B x v j) 1)

theorem brokenHeight_minor_degree (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v : Fin 4 → ℝ) (j : Fin 4) :
    (endpointMinor (brokenHeight A B x v) v j).totalDegree ≤ max A.totalDegree B.totalDegree := by
  have hp (i : Fin 4) : (pderiv i (brokenHeight A B x v)).totalDegree ≤
      max A.totalDegree B.totalDegree := by
    exact (totalDegree_pderiv_le _ _).trans (by have := brokenHeight_degree A B x v; omega)
  unfold endpointMinor
  apply degree_add_le
  · apply degree_add_le
    · exact (degree_C_mul_le _ _).trans (hp j)
    · exact (degree_C_mul_le _ _).trans (hp 1)
  · exact (degree_C_mul_le _ _).trans (hp 0)

theorem endpointSlice_degree (R : MvPolynomial (Fin 4) ℝ) (last : Fin 2) (w : ℝ) :
    (endpointSlice last w R).totalDegree ≤ R.totalDegree := by
  apply degree_aeval_le
  intro k
  unfold sliceValues
  split_ifs <;> simp

end Submission.Lib.K4ScalarSwitching.Switching
