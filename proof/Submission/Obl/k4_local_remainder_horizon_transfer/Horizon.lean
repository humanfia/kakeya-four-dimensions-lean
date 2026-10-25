import Submission.Obl.k4_local_remainder_horizon_transfer.Definitions
import Submission.Obl.k4_scalar_linear_critical_extremizers.Horizon

/-!
The horizon is the infimum of genuine terminal costs. Its defining set is
bounded below by zero; the initial-horizon hypothesis supplies nonemptiness.
-/

namespace Submission.Obl.k4_local_remainder_horizon_transfer

open Filter

noncomputable def horizon (p : Data) : ℝ := sInf {h : ℝ | Terminal p h}

-- Adapted from this LOT tree, o118/x0400, commit 58dfa42,
-- Submission/Obl/k4_extremal_profile_setup/Horizon.lean; originally
-- o105/x0351, commit 735310f, k4_critical_path_framework/Horizon.lean.
theorem Terminal.nonneg {p : Data} (hp : p.Valid) {h : ℝ} (ha : Terminal p h) : 0 ≤ h := by
  obtain ⟨M, D, ha⟩ := ha
  obtain ⟨k, a, _, _, _, hT, _⟩ := (ha 1 (by norm_num)).exists
  have hone : (1 : ℝ) ≤ 2 ^ a.T := one_le_pow₀ (by norm_num)
  have hNh : 1 ≤ p.N k ^ h := hone.trans hT
  have hN : 1 < p.N k := lt_of_lt_of_le (by norm_num) (hp.1 k)
  have hzero : p.N k ^ (0 : ℝ) ≤ p.N k ^ h := by simpa using hNh
  exact (Real.rpow_le_rpow_left_iff hN).mp hzero

theorem terminal_bddBelow {p : Data} (hp : p.Valid) : BddBelow {h : ℝ | Terminal p h} :=
  ⟨0, fun _ hh => hh.nonneg hp⟩

theorem terminal_nonempty (hi : InitialHorizon) {p : Data} (hp : p.Valid) :
    Set.Nonempty {h : ℝ | Terminal p h} :=
  ⟨p.L + 1, hi p hp _ (by linarith)⟩

theorem horizon_nonneg (hi : InitialHorizon) {p : Data} (hp : p.Valid) : 0 ≤ horizon p :=
  Submission.Obl.k4_scalar_linear_critical_extremizers.horizon_nonneg
    (terminal_nonempty hi hp) (fun _ hh => hh.nonneg hp)

theorem horizon_le {p : Data} (hp : p.Valid) {h : ℝ} (ha : Terminal p h) : horizon p ≤ h :=
  csInf_le (terminal_bddBelow hp) ha

/-- A tolerance in the lifted time budget disappears after taking the infimum. -/
theorem horizon_composition (hi : InitialHorizon) {p q : Data}
    (hp : p.Valid) (hq : q.Valid) {h : ℝ}
    (hlift : ∀ b : ℝ, Terminal q b → ∀ ε : ℝ, 0 < ε → Terminal p (h + b + ε)) :
    horizon p ≤ h + horizon q := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hbound := Submission.Obl.k4_scalar_linear_critical_extremizers.horizon_composition
    (terminal_bddBelow hp) (terminal_nonempty hi hq)
    (h := h + ε) (fun b hb => by
      change Terminal p (h + ε + b)
      rw [show h + ε + b = h + b + ε by ring]
      exact hlift b hb ε hε)
  change horizon p ≤ h + ε + horizon q at hbound
  linarith

end Submission.Obl.k4_local_remainder_horizon_transfer
