/- Adapted from this LOT tree o222, session x0774, commit 1823dd94,
   Submission/Obl/k4_projected_parent_contact_reduction/TerminalBudgetPowers.lean. -/
import Submission.Obl.k4_general_parent_projected_layers.Support.PreparedTerminalSupport
import Submission.Obl.k4_profile_density_bounds.Asymptotics
import Submission.Obl.k4_general_parent_projected_layers.NativeMesh.RootMeshTransport

/-! The total original-world terminal-list cost is subpower in the resolution. -/

namespace Submission.Obl.k4_general_parent_projected_layers

open Submission.Obl.k4_general_parent_projected_layers.NativeMesh
open Submission.Lib.K4AffineMeshCaps

open Filter

theorem terminalBudgetConstant_mul_le {K : ℝ} (hK : 1 ≤ K) :
    terminalBudgetConstant K * K ≤ 2000000000000 * K ^ 20 := by
  have hK0 : 0 ≤ K := (zero_le_one : (0 : ℝ) ≤ 1).trans hK
  have hpow : 1 ≤ K ^ 14 := one_le_pow₀ hK
  have hinner : 2 * (2 * (2 * K) ^ 14 + 1) + 2 ≤ 65540 * K ^ 14 := by
    rw [mul_pow]
    norm_num
    linarith
  calc
    _ = (25920000 * K ^ 6) * (2 * (2 * (2 * K) ^ 14 + 1) + 2) := by
      unfold terminalBudgetConstant terminalAreaConstant
      ring
    _ ≤ (25920000 * K ^ 6) * (65540 * K ^ 14) := mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = 1698796800000 * K ^ 20 := by ring
    _ ≤ _ := by nlinarith [pow_nonneg hK0 20]

theorem eventually_terminalBudget_le (p : Parameters) (hp : p.Valid) {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ k in atTop, terminalBudgetConstant (p.K k) * p.K k ≤ p.N k ^ eps := by
  have hN (k : ℕ) : 1 ≤ p.N k := by linarith [hp.1 k]
  have hsmall := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
    hN hp.2.1 hp.2.2.1.1 hp.2.2.1.2 20 (a := 0) (b := eps) heps
    (A := 2000000000000) (by norm_num)
  filter_upwards [hsmall] with k hk
  exact (terminalBudgetConstant_mul_le (hp.2.2.1.1 k)).trans
    (by simpa only [Real.rpow_zero, mul_one] using hk.le)

end Submission.Obl.k4_general_parent_projected_layers
