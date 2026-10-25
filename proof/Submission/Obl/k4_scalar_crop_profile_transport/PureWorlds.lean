import Submission.Obl.k4_scalar_crop_profile_transport.Pure

noncomputable section

namespace Submission.Obl.k4_scalar_crop_profile_transport

open MeasureTheory Set Filter
open scoped ENNReal

/-- The pure density part, with one measurable representative chosen at every depth. -/
theorem pure_worlds_part (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k)
    (hlim : Tendsto N atTop atTop)
    (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set Inc)
    (hsource : ∀ k, IsProbabilityMeasure (ν₀ k) ∧ MeasurableSet (E₀ k) ∧
      E₀ k ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (s V L u₀ α : ℝ) (F : ℝ → ℝ → ℝ)
    (hLs : L ≤ s) (hu₀ : 0 ≤ u₀) (huV : u₀ ≤ V)
    (hhom : Homogeneous N s V (fun k => Selected (ν₀ k) (E₀ k)) F)
    (W : ℕ → ℕ) (ω p : (k : ℕ) → Fin (W k) → ℝ)
    (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ)
    (ν : (k : ℕ) → Fin (W k) → Measure Line)
    (E : (k : ℕ) → Fin (W k) → Set Inc) (ρ : ℕ → ℝ)
    (hz : ∀ k, Function.Injective (z k)) (hp : ∀ k γ, 0 < p k γ)
    (hlift : LiftFacts N u₀ W ν₀ E₀ ν E p z)
    (hρ : ∀ k, 0 < ρ k) (hω : ∀ k γ, ω k γ = p k γ / ρ k)
    (hpclass : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ γ,
      N k ^ (-α - ε) ≤ p k γ ∧ p k γ ≤ N k ^ (-α + ε))
    (hρsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, (ρ k)⁻¹ ≤ N k ^ ε) :
    ∃ g : (k : ℕ) → Fin (W k) → ℝ → Base → ENNReal,
      (∀ k γ r, 0 ≤ r → r ≤ L → Measurable (g k γ r) ∧
        (Selected (ν k γ) (E k γ)).map (Obs (N k) r) = BaseRef.withDensity (g k γ r)) ∧
      (∀ r τ : ℝ, 0 ≤ r → r ≤ L → 0 < τ → ∃ c : ℝ, 0 < c ∧ ∀ᶠ k in atTop,
        (∑ γ, ENNReal.ofReal (ω k γ) * Selected (ν k γ) (E k γ)
          {q | g k γ r (Obs (N k) r q) < ENNReal.ofReal (N k ^ (-(F r u₀ + u₀ - α) - τ)) ∨
            ENNReal.ofReal (N k ^ (-(F r u₀ + u₀ - α) + τ)) < g k γ r (Obs (N k) r q)}) ≤
          ENNReal.ofReal (N k ^ (-c))) := by
  classical
  obtain ⟨g₀, G₀, hg₀, hG₀, htyp₀, htypG₀⟩ := hhom
  have hex : ∀ (k : ℕ) (γ : Fin (W k)) (r : ℝ), ∃ g : Base → ENNReal,
      Measurable g ∧ (0 ≤ r → r ≤ L →
        (Selected (ν k γ) (E k γ)).map (Obs (N k) r) = BaseRef.withDensity g) := by
    intro k γ r
    by_cases hr : 0 ≤ r ∧ r ≤ L
    · let : IsProbabilityMeasure (ν₀ k) := (hsource k).1
      let : IsFiniteMeasure (Selected (ν₀ k) (E₀ k)) := selected_finite _ _ (hsource k).2.2
      obtain ⟨g, hg, hlaw⟩ := exists_crop_density (N k ^ (-u₀)) (p k γ)
        (Real.rpow_pos_of_pos (by linarith [hN k]) _) (hp k γ) (z k γ) (N k) r
        (Selected (ν₀ k) (E₀ k)) (Selected (ν k γ) (E k γ)) (hlift.2.2.2.1 k γ)
        (g₀ k r) (hg₀ k r hr.1 (hr.2.trans hLs)).2
      exact ⟨g, hg, fun _ _ => hlaw⟩
    · exact ⟨0, measurable_const, fun h0 hL => (hr ⟨h0, hL⟩).elim⟩
  choose g hg hlaw using hex
  refine ⟨g, fun k γ r h0 hL => ⟨hg k γ r, hlaw k γ r h0 hL⟩, ?_⟩
  intro r τ hr hL hτ
  exact pure_typical N hN hlim ν₀ E₀ hsource W ω p z ν E ρ u₀ α r (F r u₀)
    hz hp hlift hρ hω hpclass hρsub (fun k => G₀ k r u₀)
    (fun k => hG₀ k r u₀ hr (hL.trans hLs) hu₀ huV)
    (htypG₀ r u₀ · hr (hL.trans hLs) hu₀ huV)
    (fun k γ => g k γ r) (fun k γ => ⟨hg k γ r, hlaw k γ r hr hL⟩) τ hτ

end Submission.Obl.k4_scalar_crop_profile_transport
