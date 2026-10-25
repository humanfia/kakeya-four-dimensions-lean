/-
Adapted from: here:o062
Original proof: session x0511, branch x0511, commit fe7a5f4,
Submission/Obl/k4_scalar_mesh_projection/SwitchPathError.lean.
-/

import Submission.Lib.K4ScalarSwitching.SwitchPath

namespace Submission.Lib.K4ScalarSwitching.Switching

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4PolynomialPotential

/-- Integrating a row error along either orientation of one leg costs its
absolute duration. The simulated height is the actual polynomial primitive. -/
theorem signed_leg_error {σ : Type*} [Fintype σ] [DecidableEq σ]
    (P : MvPolynomial (σ ⊕ Unit) ℝ) (j : σ) (δ : σ → ℝ)
    (S : Polynomial ℝ) (E : ℝ)
    (hrow : ∀ s ∈ uIcc (0 : ℝ) (δ j),
      |S.derivative.eval s - eval (Sum.elim δ (fun _ : Unit => s)) P| ≤ E) :
    |S.eval (δ j) - S.eval 0 - eval δ (upperPrimitive j P)| ≤ E * |δ j| := by
  have hcont : Continuous (fun s : ℝ => eval (Sum.elim δ (fun _ : Unit => s)) P) :=
    (MvPolynomial.continuous_eval P).comp (continuous_pi fun k => by
      cases k
      · exact continuous_const
      · exact continuous_id)
  have hftc : (∫ s in (0 : ℝ)..δ j, S.derivative.eval s) = S.eval (δ j) - S.eval 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun s _ => S.hasDerivAt s) (S.derivative.continuous.intervalIntegrable _ _)
  rw [eval_upperPrimitive_integral, ← hftc,
    ← intervalIntegral.integral_sub (S.derivative.continuous.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := δ j)
    (f := fun s => S.derivative.eval s - eval (Sum.elim δ (fun _ : Unit => s)) P)
    (C := E) (fun s hs => by
      simpa only [Real.norm_eq_abs] using hrow s (uIoc_subset_uIcc hs))
  simpa only [Real.norm_eq_abs, sub_zero] using h

/-- Four line increments with controlled row residual have the endpoint
height predicted by brokenHeight, with the sum of their signed-duration
error bounds. -/
theorem broken_height_error (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v δ : Fin 4 → ℝ) (S : Fin 4 → Polynomial ℝ) (E : ℝ)
    (hrow : ∀ j, ∀ s ∈ uIcc (0 : ℝ) (δ j),
      |(S j).derivative.eval s -
        eval (Sum.elim δ (fun _ : Unit => s)) (legField A B x v j)| ≤ E) :
    |(∑ j : Fin 4, ((S j).eval (δ j) - (S j).eval 0)) -
        eval δ (brokenHeight A B x v)| ≤ E * ∑ j : Fin 4, |δ j| := by
  rw [brokenHeight, map_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ j : Fin 4, ((S j).eval (δ j) - (S j).eval 0 -
        eval δ (upperPrimitive j (legField A B x v j)))| ≤
      ∑ j : Fin 4, |(S j).eval (δ j) - (S j).eval 0 -
        eval δ (upperPrimitive j (legField A B x v j))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin 4, E * |δ j| :=
      Finset.sum_le_sum fun j _ => signed_leg_error _ j δ (S j) E (hrow j)
    _ = E * ∑ j : Fin 4, |δ j| := (Finset.mul_sum _ _ _).symm

theorem broken_height_error_in_cube (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v δ : Fin 4 → ℝ) (S : Fin 4 → Polynomial ℝ) (E q : ℝ)
    (hE : 0 ≤ E) (hδ : ∀ j, |δ j| ≤ q)
    (hrow : ∀ j, ∀ s ∈ uIcc (0 : ℝ) (δ j),
      |(S j).derivative.eval s -
        eval (Sum.elim δ (fun _ : Unit => s)) (legField A B x v j)| ≤ E) :
    |(∑ j : Fin 4, ((S j).eval (δ j) - (S j).eval 0)) -
        eval δ (brokenHeight A B x v)| ≤ 4 * q * E := by
  apply (broken_height_error A B x v δ S E hrow).trans
  have hsum : (∑ j : Fin 4, |δ j|) ≤ 4 * q := by
    calc
      _ ≤ ∑ _ : Fin 4, q := Finset.sum_le_sum fun j _ => hδ j
      _ = 4 * q := by simp
  nlinarith [mul_le_mul_of_nonneg_left hsum hE]

/-- Small discontinuities at the line switches add to the integrated row
error. The last line's endpoint is compared with the initial line's start. -/
theorem broken_height_error_with_switches (A B : MvPolynomial (Fin 2) ℝ)
    (x : Fin 2 → ℝ) (v δ : Fin 4 → ℝ) (S : Fin 4 → Polynomial ℝ) (E q b : ℝ)
    (hE : 0 ≤ E) (hδ : ∀ j, |δ j| ≤ q)
    (hrow : ∀ j, ∀ s ∈ uIcc (0 : ℝ) (δ j),
      |(S j).derivative.eval s -
        eval (Sum.elim δ (fun _ : Unit => s)) (legField A B x v j)| ≤ E)
    (hswitch : ∀ j : Fin 3,
      |(S j.succ).eval 0 - (S j.castSucc).eval (δ j.castSucc)| ≤ b) :
    |(S 3).eval (δ 3) - (S 0).eval 0 - eval δ (brokenHeight A B x v)| ≤
      4 * q * E + 3 * b := by
  let H : ℝ := ∑ j : Fin 4, ((S j).eval (δ j) - (S j).eval 0)
  have htel : (S 3).eval (δ 3) - (S 0).eval 0 - H =
      ∑ j : Fin 3, ((S j.succ).eval 0 - (S j.castSucc).eval (δ j.castSucc)) := by
    dsimp only [H]
    norm_num [Fin.sum_univ_succ]
    ring
  have hgap : |(S 3).eval (δ 3) - (S 0).eval 0 - H| ≤ 3 * b := by
    rw [htel]
    calc
      _ ≤ ∑ j : Fin 3, |(S j.succ).eval 0 - (S j.castSucc).eval (δ j.castSucc)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin 3, b := Finset.sum_le_sum fun j _ => hswitch j
      _ = 3 * b := by simp
  have hrowSum := broken_height_error_in_cube A B x v δ S E q hE hδ hrow
  have htriangle := abs_add_le
    ((S 3).eval (δ 3) - (S 0).eval 0 - H) (H - eval δ (brokenHeight A B x v))
  have heq : (S 3).eval (δ 3) - (S 0).eval 0 - H +
      (H - eval δ (brokenHeight A B x v)) =
        (S 3).eval (δ 3) - (S 0).eval 0 - eval δ (brokenHeight A B x v) := by ring
  rw [heq] at htriangle
  linarith

end Submission.Lib.K4ScalarSwitching.Switching
