/-
Adapted from: here:o062
Original source: o062/x0212, d293fdb3, Submission/Obl/k4_scalar_mesh_projection/PolynomialWitnessTransfer.lean.
Uses the unchanged general CoreTools primitives; no pending proof is treated as accepted.
-/

import Submission.Lib.K4ScalarCoreAssembly.BinnedFiberFits
import Submission.Lib.K4ScalarCoreAssembly.Support
import Submission.Lib.K4ScalarCoreAssembly.Support

namespace Submission.Lib.K4ScalarCoreAssembly


open Submission.Lib.K4ScalarCoreTools.Finalization
open Submission.Lib.K4ScalarCoreTools.Simulation.Switching
open Submission.Lib.K4ScalarCoreTools.HeavyGroups.Switching
open Submission.Lib.K4ScalarActualSwitching
open Submission.Lib.K4ScalarSwitching.Switching

open Set

/-- The original coefficient bound controls the change from witness time
to mesh-cell time. The power estimate is imported from accepted o070. -/
theorem polynomial_eval_lipschitz_of_coefficients (D : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ D) (H B : ℝ) (hH : 0 ≤ H) (hB : 1 ≤ B)
    (hcoeff : ∀ k ≤ D, |p.coeff k| ≤ H)
    (s t : ℝ) (hs : |s| ≤ B) (ht : |t| ≤ B) :
    |p.eval s-p.eval t| ≤ ((D : ℝ)+1)*(D : ℝ)*H*B^D*|s-t| := by
  classical
  have hdeg : p.natDegree < D+1 := Nat.lt_succ_of_le hp
  rw [Polynomial.eval_eq_sum_range' hdeg s, Polynomial.eval_eq_sum_range' hdeg t,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _k ∈ Finset.range (D+1), H*((D : ℝ)*B^D*|s-t|) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkD : k ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [← mul_sub, abs_mul]
      exact mul_le_mul (hcoeff k hkD)
        (Submission.Lib.K4ScalarCoreAssembly.bounded_pow_difference
          hB hs ht hkD) (abs_nonneg _) hH
    _ = _ := by simp [nsmul_eq_mul]; ring

/-- A qualifying fit at the original source time remains a fit at the
nearby mesh time, with an explicit coefficient-controlled mesh error. -/
theorem polynomial_fit_at_nearby_time (D : ℕ) (p : Polynomial ℝ)
    (hp : p.natDegree ≤ D) (H B : ℝ) (hH : 0 ≤ H) (hB : 1 ≤ B)
    (hcoeff : ∀ k ≤ D, |p.coeff k| ≤ H)
    (G s t ρ δ : ℝ) (hs : |s| ≤ B) (ht : |t| ≤ B)
    (hfit : |G-p.eval s| ≤ ρ) (hshift : |s-t| ≤ δ) :
    |G-p.eval t| ≤ ρ+((D : ℝ)+1)*(D : ℝ)*H*B^D*δ := by
  have hLip := polynomial_eval_lipschitz_of_coefficients D p hp H B hH hB hcoeff s t hs ht
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  exact (abs_sub_le G (p.eval s) (p.eval t)).trans
    (add_le_add hfit (hLip.trans (mul_le_mul_of_nonneg_left hshift (by positivity))))

end Submission.Lib.K4ScalarCoreAssembly
