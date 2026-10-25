import Submission.Obl.k4_scalar_initial_true_horizon.Basic
import Submission.Obl.k4_scalar_initial_true_horizon.Raw

/-! Readable versions of the two Mathlib-only frozen child statements. -/

namespace Submission.Obl.k4_scalar_initial_true_horizon

open Filter

noncomputable def RawInitial : Prop :=
  ∀ p : Data, Exact p → ∃ B : ℕ, 1 ≤ B ∧
    ∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop,
      RawChart p B (L p) (L p) (L p + ε) ε true k

noncomputable def TerminalRecovery : Prop :=
  ∀ p : Data, Exact p → ∀ B : ℕ, 1 ≤ B → ∃ B₂ : ℕ, 1 ≤ B₂ ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ δ ≤ 1 ∧
      ∀ᶠ k in atTop, ∀ h : ℝ,
        RawChart p B (L p) (L p) h δ true k →
          Chart p B₂ (L p) (L p) h ε true k

/-- Enlarging only the time exponent preserves all original atlas data. -/
theorem RawChart.mono_time {p : Data} {B k : ℕ} {r b h h' ε : ℝ}
    {isTrue : Bool} (hc : RawChart p B r b h ε isTrue k)
    (hN : 1 ≤ N p k) (hh : h ≤ h') :
    RawChart p B r b h' ε isTrue k := by
  obtain ⟨T, n, γ, j, A, C, u, v, J, P, hT, hrest⟩ := hc
  refine ⟨T, n, γ, j, A, C, u, v, J, P, ?_, hrest⟩
  exact hT.trans (Real.rpow_le_rpow_of_exponent_le hN hh)

/-- The construction loss is chosen after recovery's density-tail cutoff;
the complexity exponents are chosen before the requested output loss. -/
theorem initial_of_raw_recovery (hraw : RawInitial) (hrec : TerminalRecovery) : Initial := by
  intro p hp
  obtain ⟨B, hB, hraw⟩ := hraw p hp
  obtain ⟨B₂, hB₂, hrec⟩ := hrec p hp B hB
  refine ⟨hp.length_pos.le, B₂, hB₂, ?_⟩
  intro ε hε
  obtain ⟨δ, hδ, hδε, _hδ1, hconv⟩ := hrec ε hε
  apply ((hraw δ hδ).and_eventually hconv).mono
  intro k hk
  exact hk.2 (L p + ε) (hk.1.mono_time
    (by linarith [hp.resolution_ge k]) (by linarith))

end Submission.Obl.k4_scalar_initial_true_horizon
