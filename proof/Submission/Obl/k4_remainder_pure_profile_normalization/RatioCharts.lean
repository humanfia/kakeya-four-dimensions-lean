import Submission.Obl.k4_remainder_pure_profile_normalization.NormalizeSamples
import Submission.Obl.k4_remainder_pure_profile_normalization.Determinants
import Submission.Obl.k4_remainder_pure_profile_normalization.RatioSelection
import Submission.Obl.k4_tempered_grid_selection.SelectionMass

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter

/-- Finite normalized samples whose chart Jacobians have one common logarithmic
ratio to the full assignment masses. -/
structure RatioSamples (p : Data) (r h : ℝ) where
  samples : NormalizedSamples p r h
  exponent : ℝ
  ratios : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ b,
    p.N (samples.sequence.index k) ^ (exponent - ε) ≤
      |((samples.sequence.atlas k).Q b).det| /
        (p.ν (samples.sequence.index k) ((samples.sequence.atlas k).γ b)
          ((samples.sequence.atlas k).A b)).toReal ∧
    |((samples.sequence.atlas k).Q b).det| /
        (p.ν (samples.sequence.index k) ((samples.sequence.atlas k).γ b)
          ((samples.sequence.atlas k).A b)).toReal ≤
      p.N (samples.sequence.index k) ^ (exponent + ε)

/-- Deleting only whole charts makes the exact affine density multipliers
asymptotically uniform while retaining prepared full assignment priors. -/
theorem Known.exists_ratio_samples {p : Data} (hp : p.Valid) {r h : ℝ}
    (hk : Known p r h) (hr : 0 ≤ r) : Nonempty (RatioSamples p r h) := by
  classical
  obtain ⟨M, D, s, htime, hprior⟩ := hk.exists_prepared_sequence hp
  obtain ⟨Mₚ, Dₚ, hsample⟩ := hp.sampleProblem
  let M₀ := M + Nat.ceil (h + 1)
  let A₀ := M + 2
  let s₀ : KnownSequence p M₀ D r h := {
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
  let ratio (k : ℕ) (b : Fin (s.atlas k).C) : ℝ :=
    |((s.atlas k).Q b).det| /
      (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal
  let weight (k : ℕ) (b : Fin (s.atlas k).C) : ENNReal :=
    ENNReal.ofReal (p.ω (s.index k) ((s.atlas k).γ b)) *
      ((p.ν (s.index k) ((s.atlas k).γ b)).prod volume) ((s.atlas k).F b)
  let bound : ℕ := 2 * M₀ + 1 + A₀
  have hrat : ∀ k b, p.N (s.index k) ^ (-(bound : ℝ)) ≤ ratio k b ∧
      ratio k b ≤ p.N (s.index k) ^ (bound : ℝ) := by
    intro k b
    have hN : 2 ≤ p.N (s.index k) := hp.1 _
    have hN0 : 0 < p.N (s.index k) := by linarith
    letI : IsProbabilityMeasure (p.ν (s.index k) ((s.atlas k).γ b)) :=
      (hsample (s.index k)).prob _
    have hlo : (p.N (s.index k) ^ A₀)⁻¹ ≤
        (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal := hprior k b
    have hpos : 0 < (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal :=
      (inv_pos.mpr (pow_pos hN0 _)).trans_le hlo
    have hle1 : (p.ν (s.index k) ((s.atlas k).γ b) ((s.atlas k).A b)).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal (by norm_num) (by
        simpa using (measure_mono (μ := p.ν (s.index k) ((s.atlas k).γ b))
          (Set.subset_univ ((s.atlas k).A b))))
    obtain ⟨_, _, _, _, hchart, _⟩ := s₀.valid k
    have hframe := hchart b
    have hb := jacobian_prior_ratio_bounds ((s.atlas k).Q b) hN hframe.1
      hframe.2.2.1 hpos hle1 hlo
    refine ⟨?_, ?_⟩
    · refine (Real.rpow_le_rpow_of_exponent_le (by linarith : 1 ≤ p.N (s.index k)) ?_).trans hb.1
      have hh : ((2 * M₀ + 1 : ℕ) : ℝ) ≤ (bound : ℝ) := by
        exact_mod_cast (show 2 * M₀ + 1 ≤ bound by dsimp [bound]; omega)
      linarith
    · simpa only [Real.rpow_natCast] using hb.2
  obtain ⟨ψ, S, loss, α, hψ, hloss, hretain, hfit⟩ :=
    select_finite_ratios (fun k => p.N (s.index k)) (fun k => hp.1 _)
      (hp.2.1.comp s.strictMono.tendsto_atTop) (fun k => (s.atlas k).C)
      weight ratio bound (Nat.cast_nonneg _) hrat
  let κ (k : ℕ) := (s.atlas (ψ k)).κ * loss k
  let a (k : ℕ) := ((s.atlas (ψ k)).select (S k)).withSlack (κ k)
  have hslack : Submission.Obl.k4_tempered_grid_selection.Subpower
      (fun k => p.N (s.index (ψ k))) κ :=
    Submission.Obl.k4_tempered_grid_selection.subpower_mul
      (fun k => by linarith [hp.1 (s.index (ψ k))])
      ⟨fun k => s.slack_one (ψ k), fun ε hε =>
        hψ.tendsto_atTop.eventually (s.slack_subpower ε hε)⟩ hloss
  have hmass (k : ℕ) : ENNReal.ofReal (κ k)⁻¹ ≤ ((s.atlas (ψ k)).select (S k)).mass := by
    have hκ : 0 < (s.atlas (ψ k)).κ := by linarith [s.slack_one (ψ k)]
    have hl : 0 < loss k := by linarith [hloss.1 k]
    have hret : (s.atlas (ψ k)).mass ≤ ENNReal.ofReal (loss k) *
        ((s.atlas (ψ k)).select (S k)).mass := by
      rw [Atlas.select_mass]
      exact hretain k
    have hlow : ENNReal.ofReal ((s.atlas (ψ k)).κ)⁻¹ ≤ (s.atlas (ψ k)).mass := by
      obtain ⟨_, _, _, _, _, hm⟩ := s.valid (ψ k)
      exact hm
    calc
      ENNReal.ofReal (κ k)⁻¹ = (ENNReal.ofReal (loss k))⁻¹ *
          ENNReal.ofReal ((s.atlas (ψ k)).κ)⁻¹ := by
        dsimp only [κ]
        rw [mul_inv_rev, ENNReal.ofReal_mul (inv_nonneg.mpr hl.le),
          ENNReal.ofReal_inv_of_pos hl]
      _ ≤ (ENNReal.ofReal (loss k))⁻¹ * (ENNReal.ofReal (loss k) *
          ((s.atlas (ψ k)).select (S k)).mass) := mul_le_mul' le_rfl (hlow.trans hret)
      _ = _ := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hl))
          ENNReal.ofReal_ne_top, one_mul]
  let s₁ : KnownSequence p M₀ D r h := {
    index := s.index ∘ ψ
    strictMono := s.strictMono.comp hψ
    atlas := a
    slack_one := hslack.1
    slack_ambient := fun k => by
      change p.K (s.index (ψ k)) ≤ (s.atlas (ψ k)).κ * loss k
      exact (s.slack_ambient _).trans (le_mul_of_one_le_right
        (by linarith [s.slack_one (ψ k)]) (hloss.1 k))
    slack_subpower := hslack.2
    time_upper := fun ε hε => hψ.tendsto_atTop.eventually (s.time_upper ε hε)
    valid := fun k => (s₀.valid (ψ k)).select (S k)
      (by linarith [hp.1 (s.index (ψ k))]) (by linarith [s.slack_one (ψ k)])
      (le_mul_of_one_le_right (by linarith [s.slack_one (ψ k)]) (hloss.1 k))
      (fun γ => ((hsample (s.index (ψ k))).scale_pos γ).le) (hmass k) }
  have hprior₁ (k : ℕ) (b : Fin (s₁.atlas k).C) :
      (p.N (s₁.index k) ^ A₀)⁻¹ ≤
        (p.ν (s₁.index k) ((s₁.atlas k).γ b) ((s₁.atlas k).A b)).toReal :=
    hprior (ψ k) ((s.atlas (ψ k)).selectIndex (S k) b)
  have htime₁ (k : ℕ) : (2 : ℝ) ^ (s₁.atlas k).T ≤ p.N (s₁.index k) ^ M₀ := by
    refine (htime (ψ k)).trans ?_
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [hp.1 (s.index (ψ k))])
    have hc : h + 1 ≤ (Nat.ceil (h + 1) : ℝ) := Nat.le_ceil _
    have hm : (Nat.ceil (h + 1) : ℝ) ≤ M₀ := by exact_mod_cast
      (show Nat.ceil (h + 1) ≤ M₀ by dsimp [M₀]; omega)
    linarith
  let t : NormalizedSamples p r h := {
    atlasM := M₀
    atlasD := D
    sequence := s₁
    priorPower := A₀
    prior_lower := hprior₁
    formatM := Mₚ + 7 * M₀ + A₀ + Nat.ceil r + 20
    formatD := max (max Dₚ D) 1
    sample := fun k => (s₁.valid k).normalize_sample (hsample (s₁.index k)) (hp.1 _)
      hr (s₁.slack_one k) (htime₁ k) (fun b => by
        have hpow : 0 < p.N (s₁.index k) ^ A₀ := by
          exact pow_pos (by linarith [hp.1 (s₁.index k)]) _
        simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ hpow).mp (hprior₁ k b)) }
  refine ⟨⟨t, α, fun ε hε => ?_⟩⟩
  filter_upwards [hfit ε hε] with k hk b
  exact hk ((s.atlas (ψ k)).selectIndex (S k) b) (((S k).equivFin.symm b).property)

end Submission.Obl.k4_remainder_pure_profile_normalization
