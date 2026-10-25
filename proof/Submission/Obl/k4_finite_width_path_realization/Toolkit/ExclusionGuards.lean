/- Adapted from same-tree o119, session x0401, commit 19d6f4b3eda81f6d7228948a9996d889733ab672,
   Submission/Obl/k4_finite_width_critical_contradiction/ExclusionGuards.lean (namespace renamed; any
   earlier provenance is kept below). -/
import Submission.Obl.k4_finite_width_path_realization.Toolkit.NarrowTerminal

/-! Finite-format guards, within one fixed exact problem. -/

namespace Submission.Obl.k4_finite_width_path_realization

open Filter

theorem NarrowTerminalAt.mono_tolerance {p : Data} (hp : p.Valid) {M D k : ℕ}
    {h w ε ε' : ℝ} (ha : NarrowTerminalAt p M D h w ε k) (hε : ε ≤ ε') :
    NarrowTerminalAt p M D h w ε' k := by
  obtain ⟨a, hκ, hK, hκN, hT, hwidth, htrue⟩ := ha
  have hN : 1 ≤ p.N k := le_trans (by norm_num) (hp.N_ge k)
  exact ⟨a, hκ, hK, hκN.trans (Real.rpow_le_rpow_of_exponent_le hN hε),
    hT.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)),
    fun b => (hwidth b).trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith)),
    htrue⟩

theorem not_narrowTerminal_iff (p : Data) (h w : ℝ) :
    ¬ NarrowTerminal p h w ↔ ∀ M D : ℕ, ∃ ε : ℝ, 0 < ε ∧
      ∀ᶠ k in atTop, ¬ NarrowTerminalAt p M D h w ε k := by
  classical
  simp [NarrowTerminal, not_forall, Filter.not_frequently]

/-- Failure of NT gives, for each fixed format, a positive slack threshold and
an eventual guard against every smaller tolerance in the original resolution. -/
theorem finite_narrowness_guard {p : Data} (hp : p.Valid) {h w : ℝ}
    (hnt : ¬ NarrowTerminal p h w) (M D : ℕ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ᶠ k in atTop, ∀ ε : ℝ, ε ≤ ε₀ →
      ¬ NarrowTerminalAt p M D h w ε k := by
  obtain ⟨ε₀, hε₀, hguard⟩ := (not_narrowTerminal_iff p h w).mp hnt M D
  exact ⟨ε₀, hε₀, hguard.mono fun _ hk _ hε ha => hk (ha.mono_tolerance hp hε)⟩

/-- The horizon guard also fixes format before choosing its tolerance and
before taking a sufficiently late sample. -/
theorem finite_horizon_guard {p : Data} (hp : p.Valid) {h : ℝ}
    (hh : h < horizon p) (M D : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k in atTop, ¬ TerminalAt p M D h ε k := by
  have hn : ¬ Terminal p h := fun ha => (not_lt_of_ge (horizon_le hp ha)) hh
  classical
  simp only [Terminal, not_exists, not_forall, Filter.not_frequently] at hn
  simpa only [exists_prop] using hn M D

/-- Every sufficiently regular true terminal atlas must pay the specified
subcritical time cost at all late samples. -/
theorem finite_horizon_atlas_guard {p : Data} (hp : p.Valid) {h : ℝ}
    (hh : h < horizon p) (M D : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k in atTop, ∀ a : Atlas p k,
      1 ≤ a.κ → p.K k ≤ a.κ → a.κ ≤ p.N k ^ ε → a.TrueAt M D p.L →
        p.N k ^ h < (2 : ℝ) ^ a.T := by
  obtain ⟨ε, hε, hguard⟩ := finite_horizon_guard hp hh M D
  refine ⟨ε, hε, hguard.mono fun k hk a hκ hK hκN htrue => ?_⟩
  by_contra hn
  exact hk ⟨a, hκ, hK, hκN, le_of_not_gt hn, htrue⟩

/-- At a forbidden width, every true terminal atlas within the fixed time
budget has a chart that is wider than that threshold. -/
theorem finite_narrowness_atlas_guard {p : Data} (hp : p.Valid) {h w : ℝ}
    (hnt : ¬ NarrowTerminal p h w) (M D : ℕ) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ k in atTop, ∀ a : Atlas p k,
      1 ≤ a.κ → p.K k ≤ a.κ → a.κ ≤ p.N k ^ ε →
      (2 : ℝ) ^ a.T ≤ p.N k ^ (h + ε) → a.TrueAt M D p.L →
        ∃ b, p.N k ^ (-w + ε) < |Matrix.det (a.Q b)| * (4 : ℝ) ^ a.T := by
  obtain ⟨ε, hε, hguard⟩ := (not_narrowTerminal_iff p h w).mp hnt M D
  refine ⟨ε, hε, hguard.mono fun k hk a hκ hK hκN hT htrue => ?_⟩
  by_contra! hn
  exact hk ⟨a, hκ, hK, hκN, hT, hn, htrue⟩

end Submission.Obl.k4_finite_width_path_realization
