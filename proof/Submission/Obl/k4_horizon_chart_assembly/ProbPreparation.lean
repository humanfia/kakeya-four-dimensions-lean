import Submission.Obl.k4_horizon_chart_assembly.Defs
import Submission.Obl.k4_dyadic_crop_worlds.BooleanFormat

namespace Submission.Obl.k4_horizon_chart_assembly

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

/-- Exactly the finite-sample information needed by the quantitative atlas. -/
def SampleData (H K : ℝ) (W D₀ : ℕ) (ω : Fin W → ℝ)
    (ν : Fin W → Measure (ℕ × (Fin 6 → ℝ)))
    (E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : Fin W → MvPolynomial (Fin 4) ℝ) (B : Fin W → ℝ) : Prop :=
  (W : ℝ) ≤ H ∧ (∀ γ, 0 ≤ ω γ) ∧ (∑ γ, ω γ) = 1 ∧
  (∀ γ, IsProbabilityMeasure (ν γ) ∧ 0 < B γ ∧ B γ ≤ H ∧ (B γ)⁻¹ ≤ H ∧
    (P γ).totalDegree ≤ 2 ∧ (∀ e, |(P γ).coeff e| ≤ H) ∧
    MeasurableSet (E γ) ∧ E γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧
    (∀ p ∈ E γ, (p.1.1 : ℝ) ≤ H ∧ ∀ e, |p.1.2 e| ≤ H) ∧
    (∀ i, Fmt 7 H D₀ {x : Fin 7 → ℝ |
      ((i, fun e : Fin 6 => x e.castSucc), x 6) ∈ E γ})) ∧
  (∀ γ, ∀ᵐ l ∂ν γ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
    ‖yl l t‖ + ‖vl l‖ ≤ K ∧ |MvPolynomial.eval (xl l t) (P γ)| ≤ K ∧
    |MvPolynomial.eval (xl l t) (MvPolynomial.pderiv (3 : Fin 4) (P γ))| ≤ K * B γ ∧
    |MvPolynomial.eval (xl l t) (MvPolynomial.pderiv (3 : Fin 4)
      (MvPolynomial.pderiv (3 : Fin 4) (P γ)))| ≤ K * (B γ) ^ 2) ∧
  (∀ γ, ∀ᵐ p ∂(((ν γ).prod volume).restrict (E γ)),
    B γ / K ≤ |MvPolynomial.eval (xl p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P γ))|) ∧
  ENNReal.ofReal K⁻¹ ≤ ∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume) (E γ)

/-- The full problem supplies one fixed complexity exponent and one fixed degree
for all finite samples, before any loss exponent is chosen. -/
theorem prepared_samples
    (N K : ℕ → ℝ) (L d S η : ℝ) (W : ℕ → ℕ)
    (ω : (k : ℕ) → Fin (W k) → ℝ)
    (ν : (k : ℕ) → Fin (W k) → Measure (ℕ × (Fin 6 → ℝ)))
    (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (P : (k : ℕ) → Fin (W k) → MvPolynomial (Fin 4) ℝ)
    (B : (k : ℕ) → Fin (W k) → ℝ) (f : ℝ → ℝ)
    (g : (k : ℕ) → Fin (W k) → ℝ → (EuclideanSpace ℝ (Fin 3) × ℤ) → ENNReal)
    (G : (k : ℕ) → Fin (W k) → ℝ → ((EuclideanSpace ℝ (Fin 3) × ℤ) × (Fin 2 → ℤ)) → ENNReal)
    (h : Prob N K L d S η W ω ν E P B f g G) :
    ∃ M D : ℕ, ∀ k, SampleData (N k ^ M) (K k) (W k) D (ω k) (ν k) (E k) (P k) (B k) := by
  rcases h with ⟨_, _, _, _, _, _, _, _, hdata, _⟩
  obtain ⟨M, D, hdata⟩ := hdata
  refine ⟨M, D, fun k => ?_⟩
  obtain ⟨hW, hω₀, hω₁, hworld, hmass⟩ := hdata k
  have hfields (γ : Fin (W k)) :
      (IsProbabilityMeasure (ν k γ) ∧ 0 < B k γ ∧ B k γ ≤ N k ^ M ∧ (B k γ)⁻¹ ≤ N k ^ M ∧
        (P k γ).totalDegree ≤ 2 ∧ (∀ e, |(P k γ).coeff e| ≤ N k ^ M) ∧
        MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧
        (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ M ∧ ∀ e, |p.1.2 e| ≤ N k ^ M) ∧
        (∀ i, Fmt 7 (N k ^ M) D {x : Fin 7 → ℝ |
          ((i, fun e : Fin 6 => x e.castSucc), x 6) ∈ E k γ})) ∧
      (∀ᵐ l ∂ν k γ, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖yl l t‖ + ‖vl l‖ ≤ K k ∧ |MvPolynomial.eval (xl l t) (P k γ)| ≤ K k ∧
        |MvPolynomial.eval (xl l t) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))| ≤ K k * B k γ ∧
        |MvPolynomial.eval (xl l t) (MvPolynomial.pderiv (3 : Fin 4)
          (MvPolynomial.pderiv (3 : Fin 4) (P k γ)))| ≤ K k * (B k γ) ^ 2) ∧
      (∀ᵐ p ∂(((ν k γ).prod volume).restrict (E k γ)), B k γ / K k ≤
        |MvPolynomial.eval (xl p.1 p.2) (MvPolynomial.pderiv (3 : Fin 4) (P k γ))|) := by
    obtain ⟨hν, hB, hBup, hBinv, hdeg, hcoeff, _, hE, hunit, hbox, hfmt, hupper, hlower⟩ := hworld γ
    exact ⟨⟨hν, hB, hBup, hBinv, hdeg, hcoeff, hE, hunit, hbox, hfmt⟩, hupper, hlower⟩
  refine ⟨hW, hω₀, hω₁, fun γ => (hfields γ).1, fun γ => (hfields γ).2.1,
    fun γ => (hfields γ).2.2, ?_⟩
  simpa only [Measure.restrict_apply_univ] using hmass

/-- Increasing the complexity budget preserves the original laws and all a.e.
conditions. It changes no incidence mass. -/
theorem SampleData.mono {H H' K : ℝ} {W D : ℕ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {P : Fin W → MvPolynomial (Fin 4) ℝ} {B : Fin W → ℝ}
    (h : SampleData H K W D ω ν E P B) (hH : H ≤ H') : SampleData H' K W D ω ν E P B := by
  obtain ⟨hW, hω₀, hω₁, hworld, hupper, hlower, hmass⟩ := h
  refine ⟨hW.trans hH, hω₀, hω₁, ?_, hupper, hlower, hmass⟩
  intro γ
  obtain ⟨hν, hB, hBup, hBinv, hdeg, hcoeff, hE, hunit, hbox, hfmt⟩ := hworld γ
  refine ⟨hν, hB, hBup.trans hH, hBinv.trans hH, hdeg, fun e => (hcoeff e).trans hH,
    hE, hunit, ?_, ?_⟩
  · intro p hp
    exact ⟨(hbox p hp).1.trans hH, fun e => ((hbox p hp).2 e).trans hH⟩
  · intro i
    exact Submission.Obl.k4_dyadic_crop_worlds.BoolFormat.mono (hfmt i) hH le_rfl

end
end Submission.Obl.k4_horizon_chart_assembly
