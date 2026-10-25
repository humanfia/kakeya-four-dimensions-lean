import Submission.Obl.k4_scalar_conditional_crop_worlds.Partition
import Submission.Obl.k4_dyadic_crop_worlds.Selection
import Submission.Obl.k4_dyadic_crop_worlds.Assembly

open MeasureTheory Filter Finset Set

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

noncomputable section

/-- Prior and selected masses of one scalar cell. -/
abbrev priorMass (N u : ℝ) (ν : Measure Line) (q : Label) : ℝ :=
  (ν (scalarCell N u q)).toReal

abbrev activeMass (N u : ℝ) (ν : Measure Line) (E : Set State) (q : Label) : ℝ :=
  ((ν.prod volume) (E ∩ (scalarCell N u q ×ˢ univ))).toReal

/-- Select and enumerate a common prior-mass class. The retained prior and incidence masses
are both inverse-subpower, and each retained prior mass has a fixed polynomial lower bound. -/
theorem select_cells (N K : ℕ → ℝ) (ν₀ : ℕ → Measure Line) (E₀ : ℕ → Set State)
    (u : ℝ) (B U : ℕ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : Subpower N K) (hu : u ≤ U) (hprob : ∀ k, IsProbabilityMeasure (ν₀ k))
    (hbound : ∀ k, ∀ᵐ l ∂ν₀ k, ∀ e, |l.2 e| ≤ N k ^ B)
    (hE : ∀ k, E₀ k ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hmass : ∀ k, ENNReal.ofReal ((K k)⁻¹) ≤ (ν₀ k).prod volume (E₀ k)) :
    ∃ (ψ : ℕ → ℕ) (T : ℕ → ℝ) (α : ℝ) (W : ℕ → ℕ)
      (z : (k : ℕ) → Fin (W k) → Label) (p ω : (k : ℕ) → Fin (W k) → ℝ) (ρ : ℕ → ℝ),
      StrictMono ψ ∧ Subpower (N ∘ ψ) T ∧
      (∀ k, (W k : ℝ) ≤ N (ψ k) ^ (2 * (B + U + 3))) ∧
      (∀ k, Function.Injective (z k)) ∧
      (∀ k γ, p k γ = priorMass (N (ψ k)) u (ν₀ (ψ k)) (z k γ) ∧
        N (ψ k) ^ (-((2 * (B + U + 3) : ℕ) : ℝ) - 1) ≤ p k γ ∧ 0 < p k γ) ∧
      (∀ k, 0 < ρ k ∧ ρ k ≤ 1 ∧ (∑ γ, p k γ) = ρ k ∧ ∀ γ, ω k γ = p k γ / ρ k) ∧
      (∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop, (ρ k)⁻¹ ≤ N (ψ k) ^ τ) ∧
      (∀ τ : ℝ, 0 < τ → ∀ᶠ k in atTop, ∀ γ,
        N (ψ k) ^ (-α - τ) ≤ p k γ ∧ p k γ ≤ N (ψ k) ^ (-α + τ)) ∧
      (∀ k, (T k)⁻¹ ≤ ∑ γ, activeMass (N (ψ k)) u (ν₀ (ψ k)) (E₀ (ψ k)) (z k γ)) := by
  classical
  let A := 2 * (B + U + 3)
  have hpart := fun k => @world_partition (N k) (hN k) B U u hu
    (ν₀ k) (hprob k) (hbound k) (E₀ k) (hE k)
  obtain ⟨ψ, Q, α, T, hψ, hQF, hQlow, hT1, hTsub, hTmass, hα⟩ :=
    k4_dyadic_crop_worlds.exists_common_mass_class N K hN hNt hK.1 hK.2
      (fun k => labelBox ⌈N k ^ B / N k ^ (-u)⌉₊)
      (fun k => priorMass (N k) u (ν₀ k))
      (fun k => activeMass (N k) u (ν₀ k) (E₀ k))
      A (fun k => (hpart k).1) (fun k q => ENNReal.toReal_nonneg)
      (fun k q => (hpart k).2.2.2.1 q) (fun k => (hpart k).2.1.le)
      (fun k => by
        rw [(hpart k).2.2.1]
        exact (ENNReal.ofReal_le_iff_le_toReal
          (ne_top_of_le_ne_top ENNReal.one_ne_top (hpart k).2.2.2.2)).1 (hmass k))
  let W : ℕ → ℕ := fun k => (Q k).card
  let z : (k : ℕ) → Fin (W k) → Label := fun k γ => ((Q k).equivFin.symm γ).1
  let p : (k : ℕ) → Fin (W k) → ℝ :=
    fun k γ => priorMass (N (ψ k)) u (ν₀ (ψ k)) (z k γ)
  let ρ : ℕ → ℝ := fun k => ∑ γ, p k γ
  let ω : (k : ℕ) → Fin (W k) → ℝ := fun k γ => p k γ / ρ k
  have hzmem : ∀ k γ, z k γ ∈ Q k := fun k γ => ((Q k).equivFin.symm γ).2
  have hp0 : ∀ k γ, 0 < p k γ := by
    intro k γ
    exact (Real.rpow_pos_of_pos (by linarith [hN (ψ k)]) _).trans_le
      (hQlow k (z k γ) (hzmem k γ))
  have hρQ : ∀ k, ρ k = ∑ q ∈ Q k, priorMass (N (ψ k)) u (ν₀ (ψ k)) q :=
    fun k => k4_dyadic_crop_worlds.sum_equivFin (Q k)
      (priorMass (N (ψ k)) u (ν₀ (ψ k)))
  have hSQ : ∀ k, ∑ γ, activeMass (N (ψ k)) u (ν₀ (ψ k)) (E₀ (ψ k)) (z k γ) =
      ∑ q ∈ Q k, activeMass (N (ψ k)) u (ν₀ (ψ k)) (E₀ (ψ k)) q :=
    fun k => k4_dyadic_crop_worlds.sum_equivFin (Q k) _
  have hSρ : ∀ k, ∑ q ∈ Q k, activeMass (N (ψ k)) u (ν₀ (ψ k)) (E₀ (ψ k)) q ≤ ρ k := by
    intro k
    rw [hρQ k]
    exact Finset.sum_le_sum fun q _ => (hpart (ψ k)).2.2.2.1 q
  have hTpos : ∀ k, 0 < T k := fun k => by linarith [hT1 k]
  have hρge : ∀ k, (T k)⁻¹ ≤ ρ k := fun k => (hTmass k).trans (hSρ k)
  have hρpos : ∀ k, 0 < ρ k := fun k => (inv_pos.2 (hTpos k)).trans_le (hρge k)
  have hρle : ∀ k, ρ k ≤ 1 := by
    intro k
    rw [hρQ k, ← (hpart (ψ k)).2.1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (hQF k) fun q _ _ => ENNReal.toReal_nonneg
  refine ⟨ψ, T, α, W, z, p, ω, ρ, hψ, ⟨hT1, hTsub⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    exact (show (W k : ℝ) ≤ ((labelBox ⌈N (ψ k) ^ B / N (ψ k) ^ (-u)⌉₊).card : ℝ) by
      exact_mod_cast Finset.card_le_card (hQF k)).trans (hpart (ψ k)).1
  · intro k
    exact k4_dyadic_crop_worlds.injective_equivFin (Q k)
  · intro k γ
    refine ⟨rfl, ?_, hp0 k γ⟩
    convert hQlow k (z k γ) (hzmem k γ) using 1 <;> congr 1 <;> dsimp [A] <;> ring
  · exact fun k => ⟨hρpos k, hρle k, rfl, fun γ => rfl⟩
  · intro τ hτ
    filter_upwards [hTsub τ hτ] with k hk
    exact (inv_le_of_inv_le₀ (hTpos k) (hρge k)).trans hk
  · intro τ hτ
    filter_upwards [hα τ hτ] with k hk γ
    exact hk (z k γ) (hzmem k γ)
  · intro k
    rw [hSQ k]
    exact hTmass k

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
