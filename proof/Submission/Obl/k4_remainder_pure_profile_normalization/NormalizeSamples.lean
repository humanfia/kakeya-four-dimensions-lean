/-
Adapted from this LOT tree, o147, session x0498, commit 5dd59d875729,
Submission/Obl/k4_local_remainder_horizon_transfer/NormalizeSamples.lean.
Earlier provenance is preserved below.
-/
import Submission.Obl.k4_remainder_pure_profile_normalization.Preparation
import Submission.Obl.k4_remainder_pure_profile_normalization.RemainderData

/-! The prepared atlas gives a uniform tempered sequence of normalized samples. -/

namespace Submission.Obl.k4_remainder_pure_profile_normalization

open MeasureTheory Filter

theorem delta_inv_le_ceil {N : ℝ} (hN : 1 ≤ N) (r : ℝ) :
    (δ N r)⁻¹ ≤ N ^ Nat.ceil r := by
  have hN0 : 0 < N := by linarith
  have h := Submission.Obl.k4_quadratic_atlas_normalization.delta_bounds hN0 r
  calc (δ N r)⁻¹ ≤ (N ^ (-r))⁻¹ := inv_anti₀ (Real.rpow_pos_of_pos hN0 _) h.1
    _ = N ^ r := by rw [Real.rpow_neg hN0.le, inv_inv]
    _ ≤ N ^ Nat.ceil r := by
      rw [← Real.rpow_natCast]
      exact Real.rpow_le_rpow_of_exponent_le hN (Nat.le_ceil r)

/-- Every finite hypothesis of normalization is supplied by the actual known chart. -/
theorem Atlas.KnownAt.normalize_sample {p : Data} {k M D Mₚ Dₚ M₁ : ℕ}
    {a : Atlas p k} {r : ℝ} (ha : a.KnownAt M D r)
    (hp : Normalization.SampleProblem (p.N k) (p.K k) Mₚ Dₚ
      (p.W k) (p.ω k) (p.ν k) (p.E k) (p.P k) (p.B k))
    (hN : 2 ≤ p.N k) (hr : 0 ≤ r) (hκ : 1 ≤ a.κ)
    (hT : (2 : ℝ) ^ a.T ≤ p.N k ^ M)
    (hprior : ∀ c, 1 ≤ p.N k ^ M₁ * (p.ν k (a.γ c) (a.A c)).toReal) :
    Normalization.SampleProblem (p.N k) (3 * a.κ)
      (Mₚ + 7 * M + M₁ + Nat.ceil r + 20) (max (max Dₚ D) 1) a.C
      (a.system.normWeight (p.ω k) (p.ν k)) (a.system.normPrior (p.ν k))
      a.system.normEventOf (a.system.normNative (δ (p.N k) r))
      (a.system.normScale (p.B k) (δ (p.N k) r)) := by
  have hgeo := ha.geometry
  obtain ⟨_, _, _, _, hchart, hmass⟩ := ha
  apply hp.normalize a.system hgeo
  · intro c l hl t ht
    exact ((hchart c).2.2.2.2.2.2.2.2.2.1 l hl).2.2 t ht
  · intro c q hq
    exact (hchart c).2.2.2.2.2.2.2.2.2.2.1 q hq
  · intro c
    exact (hchart c).2.2.2.2.2.2.2.1
  · intro c i
    exact ((hchart c).2.2.2.2.2.2.2.2.1 i).2
  · intro c
    exact (hchart c).2.2.2.2.1
  · intro c
    exact (hchart c).2.2.2.2.2.1
  · exact hprior
  · exact hmass
  · exact hN
  · exact hT
  · unfold δ; positivity
  · exact Submission.Obl.k4_quadratic_atlas_normalization.delta_le_one (by linarith) hr
  · exact delta_inv_le_ceil (by linarith) r
  · exact hκ

/-- The finite format bounds of the normalized sequence precede every tolerance. -/
structure NormalizedSamples (p : Data) (r h : ℝ) where
  atlasM : ℕ
  atlasD : ℕ
  sequence : KnownSequence p atlasM atlasD r h
  priorPower : ℕ
  prior_lower : ∀ k c,
    (p.N (sequence.index k) ^ priorPower)⁻¹ ≤
      (p.ν (sequence.index k) ((sequence.atlas k).γ c) ((sequence.atlas k).A c)).toReal
  formatM : ℕ
  formatD : ℕ
  sample : ∀ k, Normalization.SampleProblem (p.N (sequence.index k)) (3 * (sequence.atlas k).κ)
    formatM formatD (sequence.atlas k).C
    ((sequence.atlas k).system.normWeight (p.ω (sequence.index k)) (p.ν (sequence.index k)))
    ((sequence.atlas k).system.normPrior (p.ν (sequence.index k)))
    (sequence.atlas k).system.normEventOf
    ((sequence.atlas k).system.normNative (δ (p.N (sequence.index k)) r))
    ((sequence.atlas k).system.normScale (p.B (sequence.index k)) (δ (p.N (sequence.index k)) r))

/-- Uniform finite normalization after the one-time extraction and light-chart deletion. -/
theorem Known.exists_normalized_samples {p : Data} (hp : p.Valid) {r h : ℝ}
    (hk : Known p r h) (hr : 0 ≤ r) : Nonempty (NormalizedSamples p r h) := by
  classical
  obtain ⟨M, D, s, htime, hprior⟩ := hk.exists_prepared_sequence hp
  obtain ⟨Mₚ, Dₚ, hsample⟩ := hp.sampleProblem
  let M₀ := M + Nat.ceil (h + 1)
  let s' : KnownSequence p M₀ D r h := {
    index := s.index
    strictMono := s.strictMono
    atlas := s.atlas
    slack_one := s.slack_one
    slack_ambient := s.slack_ambient
    slack_subpower := s.slack_subpower
    time_upper := s.time_upper
    valid := fun k => (s.valid k).mono_format
      (by linarith [hp.1 (s.index k)]) (by linarith [s.slack_one k])
      (fun γ => ((hsample (s.index k)).scale_pos γ).le) (by dsimp [M₀]; omega) le_rfl }
  refine ⟨⟨M₀, D, s', M + 2, hprior,
    Mₚ + 7 * M₀ + (M + 2) + Nat.ceil r + 20, max (max Dₚ D) 1, fun k => ?_⟩⟩
  have hN : 2 ≤ p.N (s.index k) := hp.1 _
  have hN1 : 1 ≤ p.N (s.index k) := by linarith
  apply (s'.valid k).normalize_sample (hsample (s.index k)) hN hr (s.slack_one k)
  · refine (htime k).trans ?_
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le hN1
    have hceil : h + 1 ≤ (Nat.ceil (h + 1) : ℝ) := Nat.le_ceil _
    have hle : (Nat.ceil (h + 1) : ℝ) ≤ M₀ := by
      exact_mod_cast (show Nat.ceil (h + 1) ≤ M₀ by dsimp [M₀]; omega)
    linarith
  · intro c
    have hpow : 0 < p.N (s.index k) ^ (M + 2) := by positivity
    simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ hpow).mp (hprior k c)

end Submission.Obl.k4_remainder_pure_profile_normalization
