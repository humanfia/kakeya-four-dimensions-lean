import Submission.Obl.k4_horizontal_strict_parameter_step.RawChartAssembly
import Submission.Obl.k4_horizontal_strict_parameter_step.PartialScales
import Submission.Obl.k4_horizontal_strict_parameter_step.SingleDepthInterface

/-! Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at d910a82958751d2c7c7da2ba0a4c7ac7b29f42f6,
file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/StrictFromRawCharts.lean`.
The namespace and internal imports are changed to o272; source provenance is retained below. -/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set Filter

/-- Raw chart preparation is requested at an arbitrarily small loss, before any
first-jet call. The old square has the exact parameter width needed after improvement. -/
def RawChartsAt (N : ℕ → ℝ) (d e₀ u θ sMax : ℝ) {α : Type} [MeasurableSpace α]
    (ν : ℕ → Measure α) (ρ : ℕ → Measure (α × ℝ)) (π : ℕ → Measure ℝ)
    (b : ℕ → α → Fin 6 → ℝ) : Prop :=
  ∀ s : ℝ, 0 < s → s < sMax → ∀ ξ : ℝ, 0 < ξ →
    let s₀ := s / (1 + θ)
    let c := θ * s₀
    ∀ᶠ k in atTop, Nonempty (RawChartFamily α (ν k) (ρ k) (π k) (b k)
      d (N k) ξ (N k ^ (-e₀)) (N k ^ (-u * s₀)) (N k ^ (-s₀))
      ((N k ^ (-c)) ^ (1000 / (1 - d))))

/-- Raw chart preparation and the chart first jet give the exact single-depth
engine output. All preparation thresholds can depend on this requested depth. -/
theorem layersAt1_of_raw_charts (hjet : RawFirstJetCover)
    {N : ℕ → ℝ} {d e₀ u θ sMax : ℝ} {α : Type} [MeasurableSpace α]
    {ν : ℕ → Measure α} {ρ : ℕ → Measure (α × ℝ)} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hd : 0 ≤ d) (hd1 : d < 1) (hθ : 0 < θ) (hb : ∀ k, Measurable (b k))
    (hraw : RawChartsAt N d e₀ u θ sMax ν ρ π b) :
    LayersAt1 N d e₀ (u / (1 + θ)) sMax ρ π b := by
  intro s hs hsMax ε hε
  have hden : 0 < 1 + θ := by linarith
  have hs₀ : 0 < s / (1 + θ) := div_pos hs hden
  have hc : 0 < θ * (s / (1 + θ)) := mul_pos hθ hs₀
  obtain ⟨ξ, hξ, N₀, hN₀, hreturn⟩ :=
    raw_charts_to_layer hjet d (θ * (s / (1 + θ))) ε hd hd1 hc hε
  filter_upwards [hraw s hs hsMax ξ hξ, hNt.eventually (eventually_ge_atTop N₀)] with k hk hNk
  have hNp : 0 < N k := by linarith [hN k]
  have hN1 : 1 ≤ N k := by linarith [hN k]
  obtain ⟨σ, n, A, q, h, hdom, hmass, hlayer⟩ := hreturn N k hNk α (ν k) (ρ k) π b e₀
    (N k ^ (-u * (s / (1 + θ)))) (N k ^ (-(s / (1 + θ)))) (hb k)
    (Real.rpow_pos_of_pos hNp _) (Real.rpow_pos_of_pos hNp _)
    (Real.rpow_le_one_of_one_le_of_nonpos hN1 (by linarith)) hk
  obtain ⟨ha, hD⟩ := partial_scale_identities (u := u) (θ := θ) (s := s) hNp hden
  have ha' : N k ^ (-(s / (1 + θ))) * N k ^ (-(θ * (s / (1 + θ)))) = N k ^ (-s) := by
    simpa only [neg_mul] using ha
  rw [hD, ha'] at hlayer
  exact ⟨σ, hdom, hmass, n, A, q, h, hlayer⟩

/-- The universal raw geometric output has the same prepared-input prefix as
the rate engine. Original trajectory priors remain explicit in its conclusion. -/
def RawEngineAt (d κ ℓ S U e₀ u θ sMax : ℝ) : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Tendsto N atTop atTop →
    ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε) →
    ∀ (α : Type) [MeasurableSpace α] (ν : ℕ → Measure α) (μ ρ : ℕ → Measure (α × ℝ))
      (π : ℕ → Measure ℝ) (b : ℕ → α → Fin 6 → ℝ) (P : ℕ → MvPolynomial (Fin 4) ℝ)
      (T n : ℕ → ℝ → ℕ) (j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s))
      (A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α)
      (c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ)
      (F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ),
      Hyp1 K ν μ ρ π b P → Hyp2 N K d S μ π b P →
      Hyp3 N K d κ ℓ U e₀ ν μ π b P T n j A B c F → Hyp4 U T n j A →
      RawChartsAt N d e₀ u θ sMax ν ρ π b

theorem single_engine_of_raw_engine (hjet : RawFirstJetCover)
    {d κ ℓ S U e₀ u θ sMax : ℝ} (hd : 0 ≤ d) (hd1 : d < 1) (hθ : 0 < θ)
    (H : RawEngineAt d κ ℓ S U e₀ u θ sMax) :
    EngineAt1 d κ ℓ S U e₀ (u / (1 + θ)) sMax := by
  intro N K hN hNt hK α _ ν μ ρ π b P T n j A B c F h1 h2 h3 h4
  exact layersAt1_of_raw_charts hjet hN hNt hd hd1 hθ (fun k => (h1 k).1)
    (H N K hN hNt hK α ν μ ρ π b P T n j A B c F h1 h2 h3 h4)

/-- The remaining analytic obligation, stated solely as construction of dense
fixed-prior charts from one old full-time engine. -/
def RawStepPreparation : Prop :=
  ScalarInput → RowInput → MatchingInput →
    ∀ d κ ℓ S U e₀ : ℝ, 0 ≤ d → d < 1 → 0 < κ → 2 * κ < 1 → ℓ = κ →
      0 < S → S ≤ 1 → 0 < U → 0 < e₀ →
      ∃ s₁ : ℝ, 0 < s₁ ∧ ∀ sMax : ℝ, 0 < sMax → sMax ≤ s₁ →
        ∀ u θ : ℝ, 2 * κ < u → u ≤ 1 → 0 < θ →
          θ ≤ (1 - d) / 10000 * (u - 2 * κ) →
          EngineAt d κ ℓ S U e₀ u sMax → RawEngineAt d κ ℓ S U e₀ u θ sMax

/-- The remaining chart construction implies the single-depth strict step, with
one buffer for every rate and every permitted positive gain. -/
theorem strict_step_of_raw_preparation (hjet : RawFirstJetCover)
    (H : RawStepPreparation) :
    ScalarInput → RowInput → MatchingInput →
    ∀ d κ ℓ S U e₀ : ℝ, 0 ≤ d → d < 1 → 0 < κ → 2 * κ < 1 → ℓ = κ →
      0 < S → S ≤ 1 → 0 < U → 0 < e₀ →
      ∃ s₁ : ℝ, 0 < s₁ ∧ ∀ sMax : ℝ, 0 < sMax → sMax ≤ s₁ →
        ∀ u θ : ℝ, 2 * κ < u → u ≤ 1 → 0 < θ →
          θ ≤ (1 - d) / 10000 * (u - 2 * κ) →
          EngineAt d κ ℓ S U e₀ u sMax →
          EngineAt1 d κ ℓ S U e₀ (u / (1 + θ)) sMax := by
  intro hScalar hRow hMatching d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1 hU he
  obtain ⟨s₁, hs₁, hraw⟩ :=
    H hScalar hRow hMatching d κ ℓ S U e₀ hd hd1 hκ hκ1 hℓ hS hS1 hU he
  refine ⟨s₁, hs₁, fun sMax hsMax hs₁ u θ hu hu1 hθ hθmax hengine => ?_⟩
  exact single_engine_of_raw_engine hjet hd hd1 hθ
    (hraw sMax hsMax hs₁ u θ hu hu1 hθ hθmax hengine)

end Submission.Obl.k4_horizontal_strict_parameter_step
