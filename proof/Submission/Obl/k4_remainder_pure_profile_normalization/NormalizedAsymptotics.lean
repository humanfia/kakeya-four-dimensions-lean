import Submission.Obl.k4_remainder_pure_profile_normalization.RawNormalized
import Submission.Obl.k4_remainder_pure_profile_normalization.AsymptoticTransfer
import Submission.Obl.k4_remainder_pure_profile_normalization.ParentTails
import Submission.Obl.k4_native_grid_profile_extension.Profiles.ExponentLimit

namespace Submission.Obl.k4_remainder_pure_profile_normalization
open MeasureTheory Filter Set
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open scoped ENNReal

noncomputable def NormalizedSamples.transportLoss {p : Data} {r h : ℝ}
    (t : NormalizedSamples p r h) (k : ℕ) : ℝ :=
  ((t.sequence.atlas k).system.normZ (p.ω (t.sequence.index k)) (p.ν (t.sequence.index k)))⁻¹ *
    (t.sequence.atlas k).κ

theorem NormalizedSamples.normalizer_pos {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : NormalizedSamples p r h) (k : ℕ) :
    0 < (t.sequence.atlas k).system.normZ (p.ω (t.sequence.index k)) (p.ν (t.sequence.index k)) := by
  obtain ⟨_, _, hsample⟩ := hp.sampleProblem
  exact (inv_pos.mpr (by linarith [t.sequence.slack_one k])).trans_le
    ((t.sequence.valid k).normalizer_lower (hsample _).prob (hsample _).weight_nonneg
      (by linarith [t.sequence.slack_one k]))

theorem NormalizedSamples.ofReal_transportLoss {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : NormalizedSamples p r h) (k : ℕ) :
    ENNReal.ofReal (t.transportLoss k) =
      ENNReal.ofReal ((t.sequence.atlas k).system.normZ
        (p.ω (t.sequence.index k)) (p.ν (t.sequence.index k)))⁻¹ *
        ENNReal.ofReal (t.sequence.atlas k).κ :=
  ENNReal.ofReal_mul (inv_nonneg.mpr (t.normalizer_pos hp k).le)

theorem NormalizedSamples.transportLoss_subpower {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : NormalizedSamples p r h) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      t.transportLoss k ≤ p.N (t.sequence.index k) ^ ε := by
  intro ε hε
  filter_upwards [t.sequence.normalizer_subpower hp (ε / 2) (half_pos hε),
    t.sequence.slack_subpower (ε / 2) (half_pos hε)] with k hZ hκ
  calc
    t.transportLoss k ≤ p.N (t.sequence.index k) ^ (ε / 2) *
        p.N (t.sequence.index k) ^ (ε / 2) := by
      exact mul_le_mul hZ hκ (by linarith [t.sequence.slack_one k]) (Real.rpow_nonneg (by linarith [hp.1 (t.sequence.index k)]) _)
    _ = p.N (t.sequence.index k) ^ ε := by
      rw [← Real.rpow_add (by linarith [hp.1 (t.sequence.index k)])]
      congr 1
      ring

/-- Every intermediate normalized upper tail has the original shifted exponent. -/
theorem RatioSamples.rawData_upper_tail {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : RatioSamples p r h) (cap : ℝ) (hr : 0 ≤ r) {σ : ℝ} (hσ : 0 ≤ σ)
    (hσL : σ ≤ p.L - r) :
    ∀ τ : ℝ, 0 < τ → IsPowerSmall (t.samples.rawData hp cap).N (fun k =>
      ∑ b, ENNReal.ofReal ((t.samples.rawData hp cap).ω k b) *
        (t.samples.rawData hp cap).incidenceMeasure k b {z |
          ENNReal.ofReal ((t.samples.rawData hp cap).N k ^ (-(p.f (r + σ) - t.exponent) + τ)) <
            (t.samples.rawData hp cap).g k b σ
              (obs ((t.samples.rawData hp cap).B k b) (δ ((t.samples.rawData hp cap).N k) σ) z)}) := by
  let q := t.samples.rawData hp cap
  let s := t.samples.sequence
  have hL : r + σ ≤ p.L := by linarith
  let old (k : ℕ) (hi : ℝ) : ENNReal :=
    ∑ γ, ENNReal.ofReal (p.ω (s.index k) γ) * p.incidenceMeasure (s.index k) γ {z |
      ENNReal.ofReal hi < p.g (s.index k) γ (composedDepth (p.N (s.index k)) r σ)
        (obs (p.B (s.index k) γ) (δ (p.N (s.index k)) (composedDepth (p.N (s.index k)) r σ)) z)}
  apply upper_tail_of_ratio q.N (fun k => by change 1 ≤ p.N (s.index k); linarith [hp.1 (s.index k)]) q.W
    (fun k b => ENNReal.ofReal (q.ω k b)) q.incidenceMeasure
    (fun k b z => q.g k b σ (obs (q.B k b) (δ (q.N k) σ) z))
    (fun k => (s.atlas k).densityRatio) t.samples.transportLoss t.exponent (p.f (r + σ))
    (t.samples.transportLoss_subpower hp)
    (fun ε hε => (t.ratios ε hε).mono fun k hk b => (hk b).2) old
  · intro ε hε
    have hh := hp.composed_depth_typical hr hσ hL ε hε
    have hu : IsPowerSmall p.N (fun n => ∑ γ, ENNReal.ofReal (p.ω n γ) *
        p.incidenceMeasure n γ {z | ENNReal.ofReal (p.N n ^ (-p.f (r + σ) + ε)) <
          p.g n γ (composedDepth (p.N n) r σ)
            (obs (p.B n γ) (δ (p.N n) (composedDepth (p.N n) r σ)) z)}) := by
      apply hh.mono
      exact Eventually.of_forall fun n => Finset.sum_le_sum fun γ _ =>
        mul_le_mul' le_rfl (measure_mono fun z hz => Or.inr hz)
    exact hu.comp s.index s.strictMono.tendsto_atTop
  · intro k hi
    rw [t.samples.ofReal_transportLoss hp k]
    exact (s.knownSystem_valid k).normalized_upper_tail hp hr hσ hL
      (fun b => t.samples.prior_pos hp k b) (by change 0 < (s.atlas k).κ; linarith [s.slack_one k]) hi

/-- Original terminal list refinement gives the matching normalized lower tail. -/
theorem RatioSamples.rawData_terminal_lower {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : RatioSamples p r h) (cap : ℝ) (hr : 0 ≤ r) (hrL : r ≤ p.L) :
    ∀ τ : ℝ, 0 < τ → IsPowerSmall (t.samples.rawData hp cap).N (fun k =>
      ∑ b, ENNReal.ofReal ((t.samples.rawData hp cap).ω k b) *
        (t.samples.rawData hp cap).incidenceMeasure k b {z |
          (t.samples.rawData hp cap).g k b (p.L - r)
              (obs ((t.samples.rawData hp cap).B k b)
                (δ ((t.samples.rawData hp cap).N k) (p.L - r)) z) <
            ENNReal.ofReal ((t.samples.rawData hp cap).N k ^ (-(p.f p.L - t.exponent) - τ))}) := by
  let q := t.samples.rawData hp cap
  let s := t.samples.sequence
  let old (k : ℕ) (lo : ℝ) : ENNReal :=
    ∑ γ, ENNReal.ofReal (p.ω (s.index k) γ) * p.incidenceMeasure (s.index k) γ {z |
      p.g (s.index k) γ p.L (obs (p.B (s.index k) γ) (δ (p.N (s.index k)) p.L) z) < ENNReal.ofReal lo}
  apply lower_tail_of_ratio q.N (fun k => by change 1 ≤ p.N (s.index k); linarith [hp.1 (s.index k)])
    (hp.2.1.comp s.strictMono.tendsto_atTop) q.W
    (fun k b => ENNReal.ofReal (q.ω k b)) q.incidenceMeasure
    (fun k b z => q.g k b (p.L - r) (obs (q.B k b) (δ (q.N k) (p.L - r)) z))
    (fun k => (s.atlas k).densityRatio) t.samples.transportLoss t.exponent (p.f p.L)
    (t.samples.transportLoss_subpower hp)
    (fun ε hε => (t.ratios ε hε).mono fun k hk b => (hk b).1) old
  · intro ε hε
    have hh := hp.varying_depth_typical (a := fun _ => p.L) ⟨hp.L_pos.le, le_rfl⟩
      tendsto_const_nhds (fun _ => ⟨hp.L_pos.le, le_rfl⟩) ε hε
    have hl : IsPowerSmall p.N (fun n => ∑ γ, ENNReal.ofReal (p.ω n γ) *
        p.incidenceMeasure n γ {z | p.g n γ p.L (obs (p.B n γ) (δ (p.N n) p.L) z) <
          ENNReal.ofReal (p.N n ^ (-p.f p.L - ε))}) := by
      apply hh.mono
      exact Eventually.of_forall fun n => Finset.sum_le_sum fun γ _ =>
        mul_le_mul' le_rfl (measure_mono fun z hz => Or.inl hz)
    exact hl.comp s.index s.strictMono.tendsto_atTop
  · intro k lo ε hε
    rw [t.samples.ofReal_transportLoss hp k]
    exact (s.knownSystem_valid k).normalized_lower_tail hp hr (sub_nonneg.mpr hrL)
      (by linarith) (fun b => t.samples.prior_pos hp k b) (by change 0 < (s.atlas k).κ; linarith [s.slack_one k]) lo ε hε

/-- Both tails identify the full normalized terminal exponent before homogenization. -/
theorem RatioSamples.rawData_terminal_typical {p : Data} (hp : p.Valid) {r h : ℝ}
    (t : RatioSamples p r h) (cap : ℝ) (hr : 0 ≤ r) (hrL : r ≤ p.L) :
    ∀ τ : ℝ, 0 < τ → IsPowerSmall (t.samples.rawData hp cap).N (fun k =>
      ∑ b, ENNReal.ofReal ((t.samples.rawData hp cap).ω k b) *
        (t.samples.rawData hp cap).incidenceMeasure k b {z |
          (t.samples.rawData hp cap).g k b (p.L - r)
              (obs ((t.samples.rawData hp cap).B k b) (δ ((t.samples.rawData hp cap).N k) (p.L - r)) z) <
            ENNReal.ofReal ((t.samples.rawData hp cap).N k ^ (-(p.f p.L - t.exponent) - τ)) ∨
          ENNReal.ofReal ((t.samples.rawData hp cap).N k ^ (-(p.f p.L - t.exponent) + τ)) <
            (t.samples.rawData hp cap).g k b (p.L - r)
              (obs ((t.samples.rawData hp cap).B k b) (δ ((t.samples.rawData hp cap).N k) (p.L - r)) z)}) := by
  intro τ hτ
  have hu := t.rawData_upper_tail hp cap hr (sub_nonneg.mpr hrL) le_rfl τ hτ
  rw [show r + (p.L - r) = p.L by ring] at hu
  apply ((t.rawData_terminal_lower hp cap hr hrL τ hτ).add
    (hp.2.1.comp t.samples.sequence.strictMono.tendsto_atTop) hu).mono
  apply Eventually.of_forall
  intro k
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  rw [Set.setOf_or, ← mul_add]
  exact mul_le_mul' le_rfl (measure_union_le _ _)

end Submission.Obl.k4_remainder_pure_profile_normalization
