import Submission.Obl.k4_local_remainder_horizon_transfer.AtlasSequence

/-! Exact subsequences and pointwise polynomial bounds for an atlas sequence. -/

namespace Submission.Obl.k4_local_remainder_horizon_transfer

open Filter

/-- Every subsequent cofinal extraction retains the same chart formats. -/
def KnownSequence.reindex {p : Data} {M D : ℕ} {r h : ℝ}
    (s : KnownSequence p M D r h) (ψ : ℕ → ℕ) (hψ : StrictMono ψ) :
    KnownSequence p M D r h where
  index := s.index ∘ ψ
  strictMono := s.strictMono.comp hψ
  atlas := fun k => s.atlas (ψ k)
  slack_one := fun k => s.slack_one (ψ k)
  slack_ambient := fun k => s.slack_ambient (ψ k)
  slack_subpower := fun ε hε => hψ.tendsto_atTop.eventually (s.slack_subpower ε hε)
  time_upper := fun ε hε => hψ.tendsto_atTop.eventually (s.time_upper ε hε)
  valid := fun k => s.valid (ψ k)

/-- A finite initial segment can be discarded to make fixed power bounds pointwise. -/
theorem KnownSequence.exists_bounded {p : Data} {M D : ℕ} {r h : ℝ}
    (s : KnownSequence p M D r h) :
    ∃ s' : KnownSequence p M D r h,
      (∀ k, (s'.atlas k).κ ≤ p.N (s'.index k)) ∧
      (∀ k, (2 : ℝ) ^ (s'.atlas k).T ≤ p.N (s'.index k) ^ (h + 1)) := by
  have he := (s.slack_subpower 1 (by norm_num)).and (s.time_upper 1 (by norm_num))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp he
  let ψ : ℕ → ℕ := fun k => k + k₀
  have hψ : StrictMono ψ := by intro i j hij; dsimp [ψ]; omega
  refine ⟨s.reindex ψ hψ, ?_, ?_⟩
  · intro k
    simpa only [KnownSequence.reindex, Function.comp_apply, Real.rpow_one] using
      (hk₀ (ψ k) (by dsimp [ψ]; omega)).1
  · intro k
    exact (hk₀ (ψ k) (by dsimp [ψ]; omega)).2

/-- Enlarge the fixed format bounds by importing the accepted chart monotonicity. -/
theorem Atlas.KnownAt.mono_format {p : Data} {k M D M' D' : ℕ} {a : Atlas p k} {r : ℝ}
    (ha : a.KnownAt M D r) (hN : 1 ≤ p.N k) (hκ : 0 < a.κ)
    (hB : ∀ γ, 0 ≤ p.B k γ) (hM : M ≤ M') (hD : D ≤ D') :
    a.KnownAt M' D' r := by
  obtain ⟨lst, hC, hsep, hlist, hchart, hmass⟩ := ha
  refine ⟨lst, hC.trans (pow_le_pow_right₀ hN hM), hsep, hlist, fun b => ?_, hmass⟩
  exact Submission.Obl.k4_quadratic_atlas_normalization.chart_mono
    hN hM hD hκ le_rfl (hB _) (hchart b) id

end Submission.Obl.k4_local_remainder_horizon_transfer
