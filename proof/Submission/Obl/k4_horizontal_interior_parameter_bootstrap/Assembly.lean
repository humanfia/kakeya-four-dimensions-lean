import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.Interface
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.RateIteration
import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.CoefR

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap

open MeasureTheory Filter

/-- Forget the recoverable coefficient clause of a layer. -/
theorem BudgetLayerAt.forget {N : ℕ → ℝ} {d e₀ R : ℝ} {α : Type} [MeasurableSpace α]
    {π : ℕ → Measure ℝ} {b : ℕ → α → Fin 6 → ℝ} {k : ℕ} {ε : ℝ}
    {ρH : Measure (α × ℝ)} {D a : ℝ} {n : ℕ} {A : Fin n → Set α}
    {q : Fin n → Fin 3 → ℤ} {h : Fin n → Fin 6 → ℝ}
    (H : BudgetLayerAt N d e₀ R π b k ε ρH D a n A q h) :
    LayerAt N d e₀ π b k ε ρH D a n A q h := by
  refine ⟨H.1, H.2.1, ?_, H.2.2.2⟩
  intro i
  exact ⟨(H.2.2.1 i).1, (H.2.2.1 i).2.2.1,
    (H.2.2.1 i).2.2.2.1, (H.2.2.1 i).2.2.2.2⟩

theorem BudgetLayersAt.forget {N : ℕ → ℝ} {d e₀ R u sMax : ℝ} {α : Type}
    [MeasurableSpace α] {ρ : ℕ → Measure (α × ℝ)} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} (H : BudgetLayersAt N d e₀ R u sMax ρ π b) :
    LayersAt N d e₀ u sMax ρ π b := by
  intro m sH hsH ε hε
  filter_upwards [H m sH hsH ε hε] with k hk
  rcases hk with ⟨ρH, hρH, hmass, nH, AH, qH, hH, hL⟩
  exact ⟨ρH, hρH, hmass, nH, AH, qH, hH, fun r => (hL r).forget⟩

theorem LayersAt.mono_buffer {N : ℕ → ℝ} {d e₀ u s₁ s₂ : ℝ} {α : Type}
    [MeasurableSpace α] {ρ : ℕ → Measure (α × ℝ)} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} (H : LayersAt N d e₀ u s₂ ρ π b) (hs : s₁ ≤ s₂) :
    LayersAt N d e₀ u s₁ ρ π b := by
  intro m sH hsH ε hε
  exact H m sH (fun r => ⟨(hsH r).1, (hsH r).2.trans_le hs⟩) ε hε

/-- The canonical base engine supplies G(1) universally at every smaller fixed buffer. -/
def BaseG1 : Prop :=
  ∀ d κ ℓ S U e₀ : ℝ, 0 ≤ d → d < 1 → 0 < κ → 2 * κ < 1 → ℓ = κ →
    0 < S → S ≤ 1 → 0 < U → 0 < e₀ →
    ∃ s₀ : ℝ, 0 < s₀ ∧ ∀ sMax : ℝ, 0 < sMax → sMax ≤ s₀ →
      EngineAt d κ ℓ S U e₀ 1 sMax

theorem baseG1_of_base (H : Base) : BaseG1 := by
  intro d κ ℓ S U e₀ hd₀ hd₁ hκ hκ1 hℓκ hS hS1 hU he
  let s₀ := min (U / 4) (e₀ / 200)
  have hs₀ : 0 < s₀ := lt_min (by positivity) (by positivity)
  refine ⟨s₀, hs₀, ?_⟩
  intro sMax hsMax hsMax0 N K hN hNt hK α _ ν μ ρ π b P T n j A B c F h1 h2 h3 h4
  obtain ⟨sM, R, hsM, hsMU, hsMe, hR, hfixed, hfamily⟩ :=
    H N K hN hNt hK d κ ℓ S U e₀ hd₀ hd₁ hκ (by linarith) (by simpa only [hℓκ] using hκ)
      hS hS1 hU he hκ1 (fun _ => hℓκ) α ν μ ρ π b P T n j A B c F h1 h2 h3 h4
  have hbudget : BudgetLayersAt N d e₀ R 1 sM ρ π b := hfamily 1 rfl
  apply hbudget.forget.mono_buffer
  exact hsMax0.trans_eq (hfixed rfl).symm

/-- The analytic step, including its uniform buffer. A smaller gain only asks for a coarser
first-jet reading scale and permits the final iteration to hit its target exactly. -/
def PartialStep : Prop :=
  ScalarInput → RowInput → MatchingInput →
    ∀ d κ ℓ S U e₀ : ℝ, 0 ≤ d → d < 1 → 0 < κ → 2 * κ < 1 → ℓ = κ →
      0 < S → S ≤ 1 → 0 < U → 0 < e₀ →
      ∃ s₁ : ℝ, 0 < s₁ ∧ ∀ sMax : ℝ, 0 < sMax → sMax ≤ s₁ →
        ∀ u θ : ℝ, 2 * κ < u → u ≤ 1 → 0 < θ →
          θ ≤ (1 - d) / 10000 * (u - 2 * κ) →
          EngineAt d κ ℓ S U e₀ u sMax → EngineAt d κ ℓ S U e₀ (u / (1 + θ)) sMax

/-- All strict rates share one reconstruction buffer, once the analytic step is available. -/
theorem uniform_engines_of_partial_step (hstep : PartialStep)
    (hScalar : ScalarInput) (hRow : RowInput) (hMatching : MatchingInput) (hbase : Base)
    (d κ ℓ S U e₀ : ℝ) (hd₀ : 0 ≤ d) (hd₁ : d < 1) (hκ : 0 < κ)
    (hκ1 : 2 * κ < 1) (hℓκ : ℓ = κ) (hS : 0 < S) (hS1 : S ≤ 1)
    (hU : 0 < U) (he : 0 < e₀) :
    ∃ sMax : ℝ, 0 < sMax ∧ 2 * sMax < U ∧ 100 * sMax < e₀ ∧ sMax ≤ 1 / 100 ∧
      ∀ u : ℝ, 2 * κ < u → u ≤ 1 → EngineAt d κ ℓ S U e₀ u sMax := by
  obtain ⟨s₀, hs₀, hbase⟩ := baseG1_of_base hbase d κ ℓ S U e₀ hd₀ hd₁ hκ hκ1 hℓκ hS hS1 hU he
  obtain ⟨s₁, hs₁, hstep⟩ := hstep hScalar hRow hMatching d κ ℓ S U e₀ hd₀ hd₁ hκ hκ1 hℓκ hS hS1 hU he
  let sMax : ℝ := min s₀ (min s₁ (min (U / 4) (min (e₀ / 200) (1 / 100))))
  have hs : 0 < sMax := by dsimp [sMax]; positivity
  have hs0 : sMax ≤ s₀ := min_le_left _ _
  have hs1 : sMax ≤ s₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hsU : sMax ≤ U / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hse : sMax ≤ e₀ / 200 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hs100 : sMax ≤ 1 / 100 := (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨sMax, hs, by linarith, by linarith, hs100, ?_⟩
  exact bootstrap_all_strict_rates_of_partial_steps (c := 2 * κ) (α := (1 - d) / 10000)
    (by positivity) hκ1 (by positivity) (by nlinarith)
    (fun u => EngineAt d κ ℓ S U e₀ u sMax) (hbase sMax hs hs0) (hstep sMax hs hs1)

/-- A fixed coefficient budget can be recovered from the whole-square norms at every
rate at most one, independently of the requested list and loss. -/
def CoefficientRecovery : Prop :=
  ∀ (N K : ℕ → ℝ), (∀ k, 2 ≤ N k) → Tendsto N atTop atTop →
    ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε) →
    ∀ d e₀ u sMax : ℝ, 0 ≤ d → 0 < e₀ → 0 < u → u ≤ 1 →
      0 < sMax → sMax ≤ 1 / 100 →
      ∀ (α : Type) [MeasurableSpace α] (ν : ℕ → Measure α)
        (μ ρ : ℕ → Measure (α × ℝ)) (π : ℕ → Measure ℝ)
        (b : ℕ → α → Fin 6 → ℝ) (P : ℕ → MvPolynomial (Fin 4) ℝ),
        Hyp1 K ν μ ρ π b P → LayersAt N d e₀ u sMax ρ π b →
        BudgetLayersAt N d e₀ 2 u sMax ρ π b

/-- The complete frozen interior engine follows from the flexible strict step and
fixed coefficient recovery. All outer quantifier orders are preserved. -/
theorem interior_of_partial_step_and_coefficient_recovery
    (hstep : PartialStep) (hCoeff : CoefficientRecovery) :
    ScalarInput → RowInput → MatchingInput → Base → Interior := by
  intro hScalar hRow hMatching hbase N K hN hNt hK d κ ℓ S U e₀ hd₀ hd₁ hκ hκ1 hℓ
    hS hS1 hU he hκgap hℓκ α _ ν μ ρ π b P T n j A B c F h1 h2 h3 h4
  obtain ⟨sMax, hs, hsU, hse, hs100, hengines⟩ :=
    uniform_engines_of_partial_step hstep hScalar hRow hMatching hbase
      d κ ℓ S U e₀ hd₀ hd₁ hκ hκgap (hℓκ rfl) hS hS1 hU he
  refine ⟨sMax, 2, hs, hsU, hse, by norm_num, (by intro h; cases h), ?_⟩
  intro u hu
  have hLayers := hengines u hu.1 hu.2 N K hN hNt hK α ν μ ρ π b P T n j A B c F h1 h2 h3 h4
  exact hCoeff N K hN hNt hK d e₀ u sMax hd₀ he (by linarith [hu.1]) hu.2 hs hs100
    α ν μ ρ π b P h1 hLayers

/-- Only the analytic strict improvement remains: all rate, buffer, and coefficient
quantifiers of the frozen target follow from this one assertion. -/
theorem interior_of_partial_step (hstep : PartialStep) :
    ScalarInput → RowInput → MatchingInput → Base → Interior := by
  apply interior_of_partial_step_and_coefficient_recovery hstep
  intro N K hN hNt hK d e₀ u sMax hd he hu₀ hu hs hs100 α _ ν μ ρ π b P h1 hL
  exact budget_of_layers hN hNt hK hu hs100 h1 hL

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap
