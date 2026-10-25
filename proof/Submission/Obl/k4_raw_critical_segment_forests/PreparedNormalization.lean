import Submission.Obl.k4_raw_critical_segment_forests.RatioParents
import Submission.Obl.k4_raw_critical_segment_forests.PureAssembly
import Submission.Obl.k4_raw_critical_segment_forests.DirectLifting

namespace Submission.Obl.k4_raw_critical_segment_forests

open MeasureTheory Filter
open Submission.Obl.k4_finite_width_output_exclusion
open Submission.Obl.k4_remainder_pure_profile_normalization
  (KnownSequence PureRemainder NormalizedRemainder)

/-- The only analytic completion remaining after pure normalization. -/
def PureCompletion : Prop :=
  ∀ (p : PureData), p.Valid → ∀ (M D : ℕ) (r h cap : ℝ)
    (s : KnownSequence p M D r h) (v : PureRemainder s cap),
    0 ≤ r → r < p.L → (s.remainingData cap v.K v.E v.f v.g v.G).Valid

noncomputable section

/-- Prepared normalization follows while retaining the given parent atlases. -/
theorem nestedNormalizationPrepared_of_pureCompletion (H : PureCompletion) :
    NestedNormalizationPrepared := by
  classical
  intro G hG r hr hrL M D φ ε κ par hφ hε hεlim hpar
  have hεone : ∀ᶠ n in atTop, ε n ≤ 1 :=
    (hεlim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))).mono
      (fun _ hx => hx.le)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp hεone
  let ψ₀ : ℕ → ℕ := fun n => n + n₀
  have hψ₀ : StrictMono ψ₀ := fun i j hij => Nat.add_lt_add_right hij n₀
  let t := preparedRatioSamples hG hr hrL.le (φ ∘ ψ₀) (ε ∘ ψ₀) (κ ∘ ψ₀)
    (fun n => par (ψ₀ n)) (hφ.comp hψ₀) (hεlim.comp hψ₀.tendsto_atTop)
    (fun n => hn₀ (ψ₀ n) (by dsimp [ψ₀]; omega)) (fun n => hpar (ψ₀ n))
  let p := toPure G
  have hp : p.Valid := hG
  have hd0 : 0 < p.d := hG.2.2.2.2.1
  have hd1 : p.d < 1 := hG.2.2.2.2.2.1
  have hcap : ∀ x : ℝ, r ≤ x → x ≤ p.L → p.f p.L - p.f x ≤ p.d * (p.L - x) := by
    rcases hG with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hc, _⟩
    intro x hx hxL
    exact hc x (hr.trans hx) hxL
  obtain ⟨ψ, hψ, v, hv⟩ := PureAssembly.pure_remainder_from_samples hp t hr hrL hd0 hd1 hcap
  let s := t.samples.sequence.reindex ψ hψ
  let q : NormalizedRemainder s p.d := {
    K := v.K
    E := v.E
    f := v.f
    g := v.g
    G := v.G
    valid := H p hp _ _ r _ p.d s v hr hrL
    event_subset := v.event_subset
    prior_positive := v.prior_positive
    normalizer_subpower := v.normalizer_subpower
    terminal_comparison := v.terminal_comparison }
  refine ⟨fromPure q.data, ψ₀ ∘ ψ, q.valid, rfl, rfl, rfl, rfl,
    hψ₀.comp hψ, fun n => rfl, ?_⟩
  exact atlasLift_of_normalized_remainder hp q hr

end
end Submission.Obl.k4_raw_critical_segment_forests
