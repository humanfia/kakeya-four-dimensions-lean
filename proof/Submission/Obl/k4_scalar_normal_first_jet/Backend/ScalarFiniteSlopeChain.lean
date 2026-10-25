/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarFiniteSlopeChain.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarFiniteSlopeChain.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarAffineCoherence
import Mathlib.Data.Fin.Basic

/-! Telescope the finite stored scalar slopes from any parent to the finest row. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

theorem finite_scalar_slope_chain {n : ℕ} (v : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : ∀ j : Fin n, i.val ≤ j.val → |v j.castSucc - v j.succ| ≤ C) :
    |v i - v (Fin.last n)| ≤ (n : ℝ) * C := by
  let m := n - i.val
  let f : ℕ → ℝ := fun j => v ⟨min (i.val + j) n, Nat.lt_succ_of_le (min_le_right _ _)⟩
  have hi : i.val ≤ n := Nat.le_of_lt_succ i.isLt
  have hf0 : f 0 = v i := by
    dsimp [f]
    congr 1
    apply Fin.ext
    simp only [Nat.add_zero, Nat.min_eq_left hi]
  have hfm : f m = v (Fin.last n) := by
    dsimp [f, m]
    congr 1
    apply Fin.ext
    simp only [Nat.add_sub_of_le hi, Nat.min_self, Fin.val_last]
  have hlink {j : ℕ} (hj : j < m) : dist (f j) (f (j + 1)) ≤ C := by
    have hij : i.val + j < n := by dsimp [m] at hj; omega
    let r : Fin n := ⟨i.val + j, hij⟩
    have hfj : f j = v r.castSucc := by
      dsimp [f, r]
      congr 1
      apply Fin.ext
      exact Nat.min_eq_left hij.le
    have hfj' : f (j + 1) = v r.succ := by
      dsimp [f, r]
      congr 1
      apply Fin.ext
      simp only [Nat.add_assoc, Nat.min_eq_left (by omega : i.val + (j + 1) ≤ n)]
    rw [hfj, hfj', Real.dist_eq]
    exact hstep r (by dsimp [r]; omega)
  have hh := dist_le_range_sum_of_dist_le (f := f) m (d := fun _ => C) hlink
  rw [hf0, hfm, Real.dist_eq] at hh
  calc
    _ ≤ ∑ _j ∈ Finset.range m, C := hh
    _ = (m : ℝ) * C := by simp
    _ ≤ (n : ℝ) * C := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le n i.val) hC

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
