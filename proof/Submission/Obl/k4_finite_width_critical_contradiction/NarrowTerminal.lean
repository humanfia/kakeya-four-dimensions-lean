import Submission.Obl.k4_finite_width_critical_contradiction.Horizon
import Submission.Obl.k4_finite_width_critical_contradiction.Narrowness

/-! Terminal systems with an explicit logarithmic narrowness threshold. -/

namespace Submission.Obl.k4_finite_width_critical_contradiction

open Filter

/-- One sample and tolerance of the exact narrow-terminal assertion. -/
def NarrowTerminalAt (p : Data) (M D : ℕ) (h w ε : ℝ) (k : ℕ) : Prop :=
  ∃ a : Atlas p k, 1 ≤ a.κ ∧ p.K k ≤ a.κ ∧ a.κ ≤ p.N k ^ ε ∧
    (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) ∧
    (∀ b, |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T ≤ p.N k ^ (-w + ε)) ∧
    a.TrueAt M D p.L

/-- The format bounds are fixed before the tolerance and sample selection. -/
def NarrowTerminal (p : Data) (h w : ℝ) : Prop :=
  ∃ M D : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, NarrowTerminalAt p M D h w ε k

theorem NarrowTerminalAt.mono {p : Data} (hp : p.Valid) {M D k : ℕ}
    {h h' w w' ε : ℝ} (ha : NarrowTerminalAt p M D h w ε k)
    (hh : h ≤ h') (hw : w' ≤ w) : NarrowTerminalAt p M D h' w' ε k := by
  obtain ⟨a, hκ, hK, hε, hT, hwidth, htrue⟩ := ha
  have hN : 1 ≤ p.N k := le_trans (by norm_num) (hp.N_ge k)
  refine ⟨a, hκ, hK, hε, hT.trans ?_, fun b => (hwidth b).trans ?_, htrue⟩
  · exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)

theorem NarrowTerminal.mono {p : Data} (hp : p.Valid) {h h' w w' : ℝ}
    (ha : NarrowTerminal p h w) (hh : h ≤ h') (hw : w' ≤ w) :
    NarrowTerminal p h' w' := by
  obtain ⟨M, D, ha⟩ := ha
  exact ⟨M, D, fun ε hε => (ha ε hε).mono fun _ hk => hk.mono hp hh hw⟩

/-- Every genuine terminal system has nonnegative logarithmic narrowness,
up to the arbitrarily small tolerance in the definition. -/
theorem Terminal.narrowZero {p : Data} (hp : p.Valid) {h : ℝ}
    (ha : Terminal p h) : NarrowTerminal p h 0 := by
  obtain ⟨M, D, ha⟩ := ha
  refine ⟨M, D, fun ε hε => ?_⟩
  apply (ha (ε / 2) (by positivity)).mono
  intro k hk
  obtain ⟨a, hκ, hK, hκN, hT, htrue⟩ := hk
  have hN : 1 ≤ p.N k := le_trans (by norm_num) (hp.N_ge k)
  refine ⟨a, hκ, hK, hκN.trans ?_, hT.trans ?_, fun b => ?_, htrue⟩
  · exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · have hwidth := Chart.narrowness_bound_rpow (le_trans zero_le_one hN)
      (le_trans zero_le_one hκ) hκN (htrue.2.2.1 b)
    simpa only [neg_zero, zero_add, show 2 * (ε / 2) = ε by ring] using hwidth

/-- Arbitrarily small exponent errors can be absorbed into a fixed positive
horizon margin, without changing the format bounds. -/
theorem NarrowTerminal.terminal_of_lt {p : Data} (hp : p.Valid) {h h' w : ℝ}
    (ha : NarrowTerminal p h w) (hh : h < h') : Terminal p h' := by
  obtain ⟨M, D, ha⟩ := ha
  refine ⟨M, D, fun ε hε => ?_⟩
  let δ := min ε ((h' - h) / 2)
  have hδ : 0 < δ := lt_min hε (by linarith)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδh : h + δ ≤ h' := by
    have := min_le_right ε ((h' - h) / 2)
    dsimp [δ]
    linarith
  apply (ha δ hδ).mono
  intro k hk
  obtain ⟨a, hκ, hK, hκN, hT, _, htrue⟩ := hk
  have hN : 1 ≤ p.N k := le_trans (by norm_num) (hp.N_ge k)
  exact ⟨a, hκ, hK, hκN.trans (Real.rpow_le_rpow_of_exponent_le hN hδε),
    hT.trans (Real.rpow_le_rpow_of_exponent_le hN hδh), htrue⟩

theorem NarrowTerminal.horizon_le {p : Data} (hp : p.Valid) {h w : ℝ}
    (ha : NarrowTerminal p h w) : horizon p ≤ h := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro h' hh
  exact csInf_le (terminal_bddBelow hp) (ha.terminal_of_lt hp hh)

end Submission.Obl.k4_finite_width_critical_contradiction
