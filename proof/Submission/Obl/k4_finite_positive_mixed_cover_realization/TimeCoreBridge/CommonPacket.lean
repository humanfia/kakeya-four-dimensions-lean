-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/CommonPacket.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/CommonPacket.lean (namespace renamed).

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.UniformMatching
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.PacketRecovery

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge

open MeasureTheory Set
open Submission.Lib.K4OriginalLists

/-- A single original packet's common density cap gives merged lists with a loss
proportional to its original scale. Pairing and list maximization preserve every component law. -/
theorem common_cap_packet_lists (h : localGraph) (D : ℕ) (d₀ : ℝ)
    (hd₀ : 0 ≤ d₀) (hd₀1 : d₀ < 1) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧
      ∀ R M ε : ℝ, R₀ ≤ R → 0 < M → 0 < ε → ε ≤ ε₀ →
      ∀ (n : ℕ) (f : Fin n → RealSheet D) (f₀ : Real3 → ℂ),
      ∀ {ι X Z : Type*} [Fintype ι] [MeasurableSpace X] [MeasurableSpace Z],
      ∀ (jet : Fin n → ι → ℝ) (width : ι → ℝ), (∀ i, 0 < width i) →
      (∀ a b, (∀ x : Real3, ‖x‖ ≤ (1 : ℝ) / 2 →
        ‖(f a).f (emb x) - (f b).f (emb x)‖ ≤ M * R ^ (-ε)) →
        ∀ i, |jet a i - jet b i| ≤ width i) →
      ∀ (ρ : Measure X) (p : X → Fin n → ℝ),
      (∀ a, Measurable (fun x => p x a)) → (∀ a, Integrable (fun x => p x a) ρ) →
      (∀ x a, 0 ≤ p x a) →
      ∀ (μ : Fin n → Measure Z) (O : Z → X), Measurable O →
      (∀ a, ρ.withDensity (fun x => ENNReal.ofReal (p x a)) = (μ a).map O) →
      ∀ (base : X → Real3), Measurable base → ∀ lam H : ℝ,
      0 < n → 0 < lam → (n : ℝ) ≤ R ^ (d₀ + ε) →
      (∀ i (x : Real3), ‖x‖ ≤ 1 → ‖(f i).f (emb x) - f₀ x‖ ≤ M * R ^ ε) →
      (∑ a, μ a univ) ≤ ENNReal.ofReal lam → (n : ℝ) * H ≤ lam * R ^ ε →
      (∀ a, (μ a).map (base ∘ O) ≤ ENNReal.ofReal H • volume) →
      posteriorBasePairLaw ρ p base {q | ‖q.2‖ ≤ (1 : ℝ) / 2 ∧
        ‖(f q.1.1).f (emb q.2) - (f q.1.2).f (emb q.2)‖ ≤ M * R ^ (-1 + ε)}ᶜ = 0 →
      ∃ L : X → Finset (binLabels width jet), MeasurableLists L ∧
        (∀ x, (L x).card ≤ 7 ^ Fintype.card ι) ∧
        (∑ a, μ a univ) ≤ (∑ a, μ a {z | mergedLabel width jet a ∈ L (O z)}) +
          ENNReal.ofReal (lam * R ^ (-ε)) := by
  obtain ⟨ε₀, hε₀, R₀, hR₀, hmatch⟩ := common_cap_graph_bad_mass h D d₀ hd₀ hd₀1
  refine ⟨ε₀, hε₀, R₀, hR₀, ?_⟩
  intro R M ε hR hM hε hεbound n f f₀ ι X Z _ _ _ jet width hw hjet
    ρ p hpmeas hpint hp μ O hO hlaw base hb lam H hn hlam hcount hband htotal hbudget hcap hsupport
  have hpairtotal : posteriorBasePairLaw ρ p base univ ≤ ENNReal.ofReal lam := by
    rw [posteriorBasePairLaw_univ ρ p hpmeas hp base hb]
    convert htotal using 1
    apply Finset.sum_congr rfl
    intro a _
    rw [hlaw a, Measure.map_apply hO MeasurableSet.univ, preimage_univ]
  have hfirst a (U : Set Real3) (hU : MeasurableSet U) :
      posteriorBasePairLaw ρ p base {q | q.1.1 = a ∧ q.2 ∈ U} ≤ ENNReal.ofReal H * volume U := by
    rw [posteriorBasePairLaw_first_component ρ p hpmeas hp base hb a U hU,
      hlaw a, Measure.map_map hb hO]
    simpa only [Measure.smul_apply, smul_eq_mul] using Measure.le_iff'.mp (hcap a) U
  have hsecond a (U : Set Real3) (hU : MeasurableSet U) :
      posteriorBasePairLaw ρ p base {q | q.1.2 = a ∧ q.2 ∈ U} ≤ ENNReal.ofReal H * volume U := by
    rw [posteriorBasePairLaw_second_component ρ p hpmeas hp base hb a U hU,
      hlaw a, Measure.map_map hb hO]
    simpa only [Measure.smul_apply, smul_eq_mul] using Measure.le_iff'.mp (hcap a) U
  have hbad := hmatch R M ε hR hM hε hεbound n f f₀ (posteriorBasePairLaw ρ p base)
    lam H hn hlam hcount hband hpairtotal hbudget hfirst hsecond
  exact packet_original_lists (fun i => (f i).f) jet width hw R M ε hjet
    ρ p hpmeas hpint hp μ O hO hlaw base hb lam htotal hsupport _ hbad

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
