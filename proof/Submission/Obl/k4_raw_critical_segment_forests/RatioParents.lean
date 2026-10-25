import Submission.Obl.k4_raw_critical_segment_forests.PureModels
import Submission.Obl.k4_raw_critical_segment_forests.PriorInverse
import Submission.Obl.k4_raw_critical_segment_forests.SaturatedRatios
import Submission.Obl.k4_remainder_pure_profile_normalization.RatioCharts

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_remainder_pure_profile_normalization
  (RatioSamples NormalizedSamples KnownSequence)

noncomputable section

/-- Saturated supplied parents give ratio samples on exactly the supplied
sequence. All atlas fields and the index remain definitionally unchanged. -/
def preparedRatioSamples {p : Data} (hp : Valid p) {r : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ p.L) {M D : ℕ}
    (φ : ℕ → ℕ) (ε κ : ℕ → ℝ) (par : (n : ℕ) → Atlas p (φ n))
    (hφ : StrictMono φ) (hεlim : Tendsto ε atTop (nhds 0))
    (hεone : ∀ n, ε n ≤ 1)
    (hpar : ∀ n, PreparedParent p M D r (ε n) (κ n) (par n)) :
    RatioSamples (toPure p) r (M : ℝ) := by
  classical
  let P := toPure p
  have hP : P.Valid := hp
  let aa : (n : ℕ) → PureAtlas P (φ n) := fun n => atlasToPure (par n) (κ n)
  have hknown (n : ℕ) : (aa n).KnownAt M D r := knownAt_toPure (a := refineLists r (par n))
    (knownParent_of_preparedParent hp hrL (hpar n)).2.2.2.2
  have hsub : ∀ e : ℝ, 0 < e → ∀ᶠ n in atTop, κ n ≤ p.N (φ n) ^ e := by
    intro e he
    filter_upwards [hεlim.eventually (eventually_lt_nhds he)] with n hn
    exact (hpar n).2.2.1.trans
      (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one _) hn.le)
  let s : KnownSequence P M D r (M : ℝ) := {
    index := φ
    strictMono := hφ
    atlas := aa
    slack_one := fun n => (hpar n).1
    slack_ambient := fun n => (hpar n).2.1
    slack_subpower := hsub
    time_upper := by
      intro e he
      exact Filter.Eventually.of_forall (fun n => ((hpar n).2.2.2.1).trans (by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one _) (by linarith)))
    valid := hknown }
  let A := 2 * M + ⌈max (p.f r) 0⌉₊ + 1
  have hpriorPos (n : ℕ) (b : Fin (s.atlas n).C) :
      0 < (p.ν (φ n) ((s.atlas n).γ b) ((s.atlas n).A b)).toReal :=
    ((hpar n).prior_saturation hp b).1
  have hprior (n : ℕ) (b : Fin (s.atlas n).C) :
      (p.N (φ n) ^ A)⁻¹ ≤ (p.ν (φ n) ((s.atlas n).γ b) ((s.atlas n).A b)).toReal := by
    have hinv := (hpar n).prior_inverse hp (hεone n) b
    exact (inv_le_comm₀ (hpriorPos n b) (pow_pos (hp.scale_pos _) _)).mp hinv
  let Mp := hP.sampleProblem.choose
  let Dp := hP.sampleProblem.choose_spec.choose
  have hs := hP.sampleProblem.choose_spec.choose_spec
  let t : NormalizedSamples P r (M : ℝ) := {
    atlasM := M
    atlasD := D
    sequence := s
    priorPower := A
    prior_lower := hprior
    formatM := Mp + 7 * M + A + Nat.ceil r + 20
    formatD := max (max Dp D) 1
    sample := fun n => (s.valid n).normalize_sample (hs (φ n)) (hp.scale_ge_two _)
      hr (s.slack_one n) ((hpar n).2.2.2.1) (fun b => by
        have hpow : 0 < p.N (φ n) ^ A := pow_pos (hp.scale_pos _) _
        change 1 ≤ p.N (φ n) ^ A *
          (p.ν (φ n) ((s.atlas n).γ b) ((s.atlas n).A b)).toReal
        rw [mul_comm]
        exact (inv_le_iff_one_le_mul₀ hpow).mp (hprior n b)) }
  refine ⟨t, p.f r, ?_⟩
  intro e he
  filter_upwards [hεlim.eventually (eventually_lt_nhds he)] with n hn b
  have hratio := (hpar n).jacobian_ratio hp b
  exact ⟨(Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one _)
      (by linarith : p.f r - e ≤ p.f r - ε n)).trans hratio.1,
    hratio.2.trans (Real.rpow_le_rpow_of_exponent_le (hp.scale_ge_one _)
      (by linarith : p.f r + ε n ≤ p.f r + e))⟩

/-- Passing to a tail makes the fixed polynomial inverse-prior bound available. -/
theorem ratio_samples_of_prepared {p : Data} (hp : Valid p) {r : ℝ}
    (hr : 0 ≤ r) (hrL : r ≤ p.L) {M D : ℕ}
    (φ : ℕ → ℕ) (ε κ : ℕ → ℝ) (par : (n : ℕ) → Atlas p (φ n))
    (hφ : StrictMono φ) (hεlim : Tendsto ε atTop (nhds 0))
    (hpar : ∀ n, PreparedParent p M D r (ε n) (κ n) (par n)) :
    ∃ (ψ : ℕ → ℕ) (hψ : StrictMono ψ),
      ∃ t : RatioSamples (toPure p) r (M : ℝ),
        t.exponent = p.f r ∧ t.samples.sequence.index = φ ∘ ψ ∧
        ∀ n, HEq (t.samples.sequence.atlas n) (atlasToPure (par (ψ n)) (κ (ψ n))) := by
  classical
  have hεone : ∀ᶠ n in atTop, ε n ≤ 1 :=
    (hεlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ hx => hx.le)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hεone
  let ψ : ℕ → ℕ := fun n => n + n₀
  have hψ : StrictMono ψ := fun i j hij => Nat.add_lt_add_right hij n₀
  exact ⟨ψ, hψ, preparedRatioSamples hp hr hrL (φ ∘ ψ) (ε ∘ ψ) (κ ∘ ψ)
    (fun n => par (ψ n)) (hφ.comp hψ) (hεlim.comp hψ.tendsto_atTop)
    (fun n => hn₀ (ψ n) (by dsimp [ψ]; omega)) (fun n => hpar (ψ n)),
    rfl, rfl, fun n => HEq.rfl⟩

end
end Submission.Obl.k4_raw_critical_segment_forests
