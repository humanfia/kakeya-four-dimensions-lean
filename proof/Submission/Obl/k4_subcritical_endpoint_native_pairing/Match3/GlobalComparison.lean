/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Match3/GlobalComparison.lean.
   Original source attributions are retained below. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.DomainComparison
import Submission.Obl.k4_subcritical_endpoint_native_pairing.ComparisonRestriction

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

open Set MeasureTheory

noncomputable def matchingDomainLaw {Ω Γ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (reader : Ω → Γ) (g : Γ) : Measure Ω := μ.restrict (reader ⁻¹' {g})

def fullComparisonBad {Ω ι₁ ι₂ : Type*} (f₁ : Ω → ι₁) (f₂ : Ω → ι₂)
    (h₁ : ι₁ → Fin 6 → ℝ) (h₂ : ι₂ → Fin 6 → ℝ) (t₀ τ p₀ q₀ D M : ℝ) : Set Ω :=
  {ω | ∃ t p q : ℝ, |t - (t₀ + τ / 2)| ≤ 4 * τ ∧ |p - (p₀ + D / 2)| ≤ 4 * D ∧
    |q - (q₀ + D / 2)| ≤ 4 * D ∧ 10 * M ≤
      |parameterPredictor (h₁ (f₁ ω)) t p q - parameterPredictor (h₂ (f₂ ω)) t p q|}

theorem measurableSet_fullComparisonBad {Ω ι₁ ι₂ : Type*} [MeasurableSpace Ω]
    [Fintype ι₁] [Fintype ι₂] [MeasurableSpace ι₁] [MeasurableSpace ι₂]
    [DiscreteMeasurableSpace ι₁] [DiscreteMeasurableSpace ι₂]
    (f₁ : Ω → ι₁) (f₂ : Ω → ι₂) (hf₁ : Measurable f₁) (hf₂ : Measurable f₂)
    (h₁ : ι₁ → Fin 6 → ℝ) (h₂ : ι₂ → Fin 6 → ℝ) (t₀ τ p₀ q₀ D M : ℝ) :
    MeasurableSet (fullComparisonBad f₁ f₂ h₁ h₂ t₀ τ p₀ q₀ D M) := by
  let B : Set (ι₁ × ι₂) := {ij | ∃ t p q : ℝ,
    |t - (t₀ + τ / 2)| ≤ 4 * τ ∧ |p - (p₀ + D / 2)| ≤ 4 * D ∧
    |q - (q₀ + D / 2)| ≤ 4 * D ∧ 10 * M ≤
      |parameterPredictor (h₁ ij.1) t p q - parameterPredictor (h₂ ij.2) t p q|}
  change MeasurableSet ((fun ω => (f₁ ω, f₂ ω)) ⁻¹' B)
  exact (hf₁.prodMk hf₂) (Set.toFinite B).measurableSet

/-- The per-domain matching theorem, summed with its ORIGINAL reference weights,
produces one good global restriction. Marginal floors belong to the pre-deletion law. -/
theorem global_comparison (hM : Matching) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
      (Γ : Type) [Fintype Γ] [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
      (ι₁ ι₂ : Γ → Type) [∀ g, Fintype (ι₁ g)] [∀ g, Fintype (ι₂ g)]
      [∀ g, MeasurableSpace (ι₁ g)] [∀ g, MeasurableSpace (ι₂ g)]
      [∀ g, DiscreteMeasurableSpace (ι₁ g)] [∀ g, DiscreteMeasurableSpace (ι₂ g)]
      (reader : Ω → Γ) (f₁ : (g : Γ) → Ω → ι₁ g) (f₂ : (g : Γ) → Ω → ι₂ g)
      (T P Q X : Ω → ℝ) (h₁ : (g : Γ) → ι₁ g → Fin 6 → ℝ)
      (h₂ : (g : Γ) → ι₂ g → Fin 6 → ℝ) (t₀ p₀ q₀ V : Γ → ℝ)
      (τ D δ δm E A₀ A Mst : ℝ) (B : ENNReal),
      Measurable reader → (∀ g, Measurable (f₁ g)) → (∀ g, Measurable (f₂ g)) →
      Measurable T → Measurable P → Measurable Q →
      0 < τ → 0 < D → 0 < δ → δ ≤ 1 → 0 < δm → (∀ g, 0 < V g) → 1 ≤ E → 0 < A₀ →
      15360 * E * δm ≤ δ * τ → 15360 * E * δm ≤ δ * D →
      R₀ * δ ≤ Mst → 13720 ≤ A → 2000000 * A₀ * E ≤ A → A ≤ (Mst / δ) ^ η →
      (∀ g, ∀ᵐ ω ∂matchingDomainLaw μ reader g,
        T ω ∈ Icc (t₀ g) (t₀ g + τ) ∧ P ω ∈ Icc (p₀ g) (p₀ g + D) ∧ Q ω ∈ Icc (q₀ g) (q₀ g + D) ∧
        |X ω - parameterPredictor (h₁ g (f₁ g ω)) (T ω) (P ω) (Q ω)| ≤ δ / 2 ∧
        |X ω - parameterPredictor (h₂ g (f₂ g ω)) (T ω) (P ω) (Q ω)| ≤ δ / 2) →
      (∀ g i, ∀ t ∈ Icc (t₀ g) (t₀ g + τ), ∀ p ∈ Icc (p₀ g) (p₀ g + D),
        ∀ q ∈ Icc (q₀ g) (q₀ g + D), |parameterPredictor (h₁ g i) t p q| ≤ E) →
      (∀ g j, ∀ t ∈ Icc (t₀ g) (t₀ g + τ), ∀ p ∈ Icc (p₀ g) (p₀ g + D),
        ∀ q ∈ Icc (q₀ g) (q₀ g + D), |parameterPredictor (h₂ g j) t p q| ≤ E) →
      (∀ g i, ENNReal.ofReal (τ * D ^ 2 * V g * δ ^ d / A₀) ≤
        matchingDomainLaw μ reader g {ω | f₁ g ω = i}) →
      (∀ g j, ENNReal.ofReal (τ * D ^ 2 * V g * δ ^ d / A₀) ≤
        matchingDomainLaw μ reader g {ω | f₂ g ω = j}) →
      (∀ g σ, δ ≤ σ → σ ≤ 1 → ∀ (c : Fin 3 → ℤ) (j : ℤ),
        matchingDomainLaw μ reader g
          {ω | (fun k => ⌊(![T ω, P ω, Q ω] : Fin 3 → ℝ) k / δm⌋) = c ∧ ⌊X ω / σ⌋ = j} ≤
            ENNReal.ofReal (V g * σ ^ d * δm ^ 3)) →
      (∑ g, ENNReal.ofReal (((Fintype.card (ι₁ g) + Fintype.card (ι₂ g) : ℕ) : ℝ) *
        (τ * D ^ 2 * V g * δ ^ d))) ≤ B →
      ∃ ρ : Measure Ω, ρ ≤ μ ∧ μ univ ≤ ρ univ + ENNReal.ofReal (A * (Mst / δ) ^ (-η)) * B ∧
        ∀ᵐ ω ∂ρ, ω ∉ fullComparisonBad (f₁ (reader ω)) (f₂ (reader ω))
          (h₁ (reader ω)) (h₂ (reader ω)) (t₀ (reader ω)) τ (p₀ (reader ω)) (q₀ (reader ω)) D Mst := by
  obtain ⟨η, hη, R₀, hR₀, H⟩ := domain_comparison hM hd0 hd1
  refine ⟨η, hη, R₀, hR₀, ?_⟩
  intro Ω _ μ _ Γ _ _ _ ι₁ ι₂ _ _ _ _ _ _ reader f₁ f₂ T P Q X h₁ h₂ t₀ p₀ q₀ V
    τ D δ δm E A₀ A Mst B hreader hf₁ hf₂ hT hP hQ hτ hD hδ hδ1 hδm hV hE hA₀
    hmτ hmD hMst hA1 hA2 hA hgood hE₁ hE₂ hfloor₁ hfloor₂ hcap hbudget
  let bad (g : Γ) := fullComparisonBad (f₁ g) (f₂ g) (h₁ g) (h₂ g) (t₀ g) τ (p₀ g) (q₀ g) D Mst
  let reference (g : Γ) := ENNReal.ofReal (((Fintype.card (ι₁ g) + Fintype.card (ι₂ g) : ℕ) : ℝ) *
    (τ * D ^ 2 * V g * δ ^ d))
  have hbad (g : Γ) : MeasurableSet (bad g) :=
    measurableSet_fullComparisonBad _ _ (hf₁ g) (hf₂ g) _ _ _ _ _ _ _ _
  have hfac : 0 ≤ A * (Mst / δ) ^ (-η) := by
    have hMp : 0 < Mst := lt_of_lt_of_le (mul_pos (by linarith : 0 < R₀) hδ) hMst
    have hAp : 0 < A := by linarith
    positivity
  have hfailure (g : Γ) : (μ.restrict (reader ⁻¹' {g})) (bad g) ≤
      ENNReal.ofReal (A * (Mst / δ) ^ (-η)) * reference g := by
    haveI : IsFiniteMeasure (matchingDomainLaw μ reader g) := by
      dsimp only [matchingDomainLaw]
      infer_instance
    have h := H Ω (matchingDomainLaw μ reader g) (ι₁ g) (ι₂ g) (f₁ g) (f₂ g) T P Q X
      (h₁ g) (h₂ g) (t₀ g) τ (p₀ g) (q₀ g) D δ δm (V g) E A₀ A Mst
      (hf₁ g) (hf₂ g) hT hP hQ hτ hD hδ hδ1 hδm (hV g) hE hA₀
      hmτ hmD hMst hA1 hA2 hA (hgood g) (hE₁ g) (hE₂ g) (hfloor₁ g) (hfloor₂ g) (hcap g)
    simpa only [matchingDomainLaw, bad, fullComparisonBad, reference,
      ← ENNReal.ofReal_mul hfac, Nat.cast_add] using h
  exact restrict_comparison_failures μ reader hreader bad hbad reference _ B hfailure hbudget

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3
