/- Adapted from same-tree o105, session x0351, commit 735310f,
   Submission/Obl/k4_critical_path_framework/Horizon.lean. -/
import Submission.Obl.k4_finite_width_critical_contradiction.Definitions

/-! The minimum horizon, retaining the fixed-format quantifier order. -/

namespace Submission.Obl.k4_finite_width_critical_contradiction

open Filter

theorem Data.Valid.N_ge {p : Data} (hp : p.Valid) (k : ℕ) : 2 ≤ p.N k := hp.1 k

theorem Data.Valid.L_pos {p : Data} (hp : p.Valid) : 0 < p.L := hp.2.2.2.1

theorem TerminalAt.mono {p : Data} (hp : p.Valid) {M D : ℕ} {h h' ε : ℝ} {k : ℕ}
    (ha : TerminalAt p M D h ε k) (hh : h ≤ h') : TerminalAt p M D h' ε k := by
  obtain ⟨a, hκ, hK, hε, hT, htrue⟩ := ha
  refine ⟨a, hκ, hK, hε, hT.trans ?_, htrue⟩
  exact Real.rpow_le_rpow_of_exponent_le (le_trans (by norm_num) (hp.N_ge k)) hh

theorem Terminal.mono {p : Data} (hp : p.Valid) {h h' : ℝ}
    (ha : Terminal p h) (hh : h ≤ h') : Terminal p h' := by
  obtain ⟨M, D, ha⟩ := ha
  exact ⟨M, D, fun ε hε => (ha ε hε).mono fun _ hk => hk.mono hp hh⟩

theorem TerminalAt.nonneg {p : Data} (hp : p.Valid) {M D : ℕ} {h ε : ℝ} {k : ℕ}
    (ha : TerminalAt p M D h ε k) : 0 ≤ h := by
  obtain ⟨a, _, _, _, hT, _⟩ := ha
  have hone : (1 : ℝ) ≤ 2 ^ a.T := one_le_pow₀ (by norm_num)
  have hNh : 1 ≤ p.N k ^ h := hone.trans hT
  have hN : 1 < p.N k := lt_of_lt_of_le (by norm_num) (hp.N_ge k)
  have hzero : p.N k ^ (0 : ℝ) ≤ p.N k ^ h := by simpa using hNh
  exact (Real.rpow_le_rpow_left_iff hN).mp hzero

theorem Terminal.nonneg {p : Data} (hp : p.Valid) {h : ℝ} (ha : Terminal p h) : 0 ≤ h := by
  obtain ⟨M, D, ha⟩ := ha
  obtain ⟨k, hk⟩ := (ha 1 (by norm_num)).exists
  exact hk.nonneg hp

/-- The infimum is taken over genuine attainable costs. -/
noncomputable def horizon (p : Data) : ℝ := sInf {h : ℝ | Terminal p h}

theorem terminal_bddBelow {p : Data} (hp : p.Valid) : BddBelow {h : ℝ | Terminal p h} :=
  ⟨0, fun _ hh => hh.nonneg hp⟩

theorem terminal_nonempty (hi : InitialHorizon) {p : Data} (hp : p.Valid) :
    Set.Nonempty {h : ℝ | Terminal p h} :=
  ⟨p.L + 1, hi p hp _ (by linarith)⟩

theorem horizon_nonneg (hi : InitialHorizon) {p : Data} (hp : p.Valid) : 0 ≤ horizon p := by
  exact le_csInf (terminal_nonempty hi hp) (fun _ hh => hh.nonneg hp)

theorem horizon_le {p : Data} (hp : p.Valid) {h : ℝ} (ha : Terminal p h) : horizon p ≤ h :=
  csInf_le (terminal_bddBelow hp) ha

theorem terminal_of_horizon_lt (hi : InitialHorizon) {p : Data} (hp : p.Valid)
    {h : ℝ} (hh : horizon p < h) : Terminal p h := by
  obtain ⟨h', hmem, hlt⟩ := (csInf_lt_iff (terminal_bddBelow hp)
    (terminal_nonempty hi hp)).mp hh
  exact hmem.mono hp hlt.le

theorem horizon_le_length (hi : InitialHorizon) {p : Data} (hp : p.Valid) :
    horizon p ≤ p.L := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro h hh
  exact horizon_le hp (hi p hp h hh)

theorem horizon_eq_zero_iff (hi : InitialHorizon) {p : Data} (hp : p.Valid) :
    horizon p = 0 ↔ ∀ h : ℝ, 0 < h → Terminal p h := by
  constructor
  · intro hh h hpos
    exact terminal_of_horizon_lt hi hp (by simpa [hh] using hpos)
  · intro hh
    apply le_antisymm _ (horizon_nonneg hi hp)
    apply le_of_forall_gt_imp_ge_of_dense
    intro h hpos
    exact horizon_le hp (hh h hpos)

end Submission.Obl.k4_finite_width_critical_contradiction
