/-
Adapted from this LOT tree, o147, session x0498, commit 5dd59d875729,
Submission/Obl/k4_local_remainder_horizon_transfer/Preparation.lean.
Earlier provenance is preserved below.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.LightCharts
import Submission.Obl.k4_remainder_pure_profile_normalization.SequenceBounds

/-! Extract known atlases and remove only polynomially light full assignments. -/

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open Filter MeasureTheory

/-- Every retained prior can be conditioned at one fixed polynomial cost. -/
theorem Known.exists_prepared_sequence {p : Data} (hp : p.Valid) {r h : ℝ}
    (hk : Known p r h) :
    ∃ M D : ℕ, ∃ s : KnownSequence p M D r h,
      (∀ k, (2 : ℝ) ^ (s.atlas k).T ≤ p.N (s.index k) ^ (h + 1)) ∧
      (∀ k c, (p.N (s.index k) ^ (M + 2))⁻¹ ≤
        (p.ν (s.index k) ((s.atlas k).γ c) ((s.atlas k).A c)).toReal) := by
  classical
  obtain ⟨M, D, ⟨s₀⟩⟩ := hk.exists_sequence hp
  obtain ⟨s, hsκ, hstime⟩ := s₀.exists_bounded
  obtain ⟨Mₚ, Dₚ, hsample⟩ := hp.sampleProblem
  have hkeep := fun k => (s.valid k).discard_light (hsample (s.index k))
    (hp.1 (s.index k)) (s.slack_one k) (hsκ k)
  choose S hS hν using hkeep
  let atlas : (k : ℕ) → Atlas p (s.index k) :=
    fun k => (((s.atlas k).select (S k)).withSlack (2 * (s.atlas k).κ))
  have hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, (atlas k).κ ≤ p.N (s.index k) ^ ε := by
    intro ε hε
    have hNt := hp.2.1.comp s.strictMono.tendsto_atTop
    have htwo : ∀ᶠ k in atTop, 2 ≤ p.N (s.index k) ^ (ε / 2) :=
      ((tendsto_rpow_atTop (half_pos hε)).comp hNt).eventually_ge_atTop 2
    filter_upwards [s.slack_subpower (ε / 2) (half_pos hε), htwo] with k hk htwo
    change 2 * (s.atlas k).κ ≤ p.N (s.index k) ^ ε
    calc 2 * (s.atlas k).κ ≤ p.N (s.index k) ^ (ε / 2) * p.N (s.index k) ^ (ε / 2) :=
          mul_le_mul htwo hk (by linarith [s.slack_one k]) (by positivity)
      _ = p.N (s.index k) ^ ε := by
        rw [← Real.rpow_add (by linarith [hp.1 (s.index k)])]
        congr 1
        ring
  let s' : KnownSequence p M D r h := {
    index := s.index
    strictMono := s.strictMono
    atlas := atlas
    slack_one := fun k => by change 1 ≤ 2 * (s.atlas k).κ; linarith [s.slack_one k]
    slack_ambient := fun k => by
      change p.K (s.index k) ≤ 2 * (s.atlas k).κ
      linarith [s.slack_ambient k, s.slack_one k]
    slack_subpower := hsub
    time_upper := fun ε hε => s.time_upper ε hε
    valid := hS }
  exact ⟨M, D, s', hstime, hν⟩

end Submission.Obl.k4_remainder_pure_profile_normalization
