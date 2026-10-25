import Mathlib
import ChallengeDeps
set_option linter.unusedVariables false

namespace Submission.Obl.k4_scalar_conditional_crop_worlds

noncomputable section

abbrev Coeff := Fin 5 → ℝ
abbrev Line := ℕ × Coeff
abbrev State := Line × ℝ
abbrev Label := Fin 2 → ℤ

abbrev Subpower : ∀ (_N _K : ℕ → ℝ), Prop := fun (N K : ℕ → ℝ) => ((∀ k, 1 ≤ K k) ∧ ∀ ε : ℝ, 0 < ε → ∀ᶠ k in Filter.atTop, K k ≤ N k ^ ε)

abbrev Noise : ∀ (_σ : ℝ), MeasureTheory.Measure (Fin 5 → ℝ) := fun (σ : ℝ) => (MeasureTheory.Measure.pi (fun _ : Fin 5 => ENNReal.ofReal (σ⁻¹) • MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) σ)))

abbrev MarkedPrior : ∀ (_σ : ℝ) (_H : ℕ) (_b₀ : Fin _H → Fin 5 → ℝ) (_w : Fin _H → ℝ), MeasureTheory.Measure (ℕ × (Fin 5 → ℝ)) := fun (σ : ℝ) (H : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) => (∑ j, ENNReal.ofReal (w j) • MeasureTheory.Measure.map (fun u : Fin 5 → ℝ => ((j : ℕ), b₀ j + u)) (Noise σ))

abbrev MarkedEvent : ∀ (_H _J : ℕ) (_mark : Fin _H → Fin _J → Bool), Set ((ℕ × (Fin 5 → ℝ)) × ℝ) := fun (H J : ℕ) (mark : Fin H → Fin J → Bool) => ({p | ∃ j : Fin H, p.1.1 = (j : ℕ) ∧ ∃ z : Fin J, mark j z = true ∧ p.2 ∈ Set.Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))})

abbrev MarkedLaw : ∀ (_σ : ℝ) (_H _J : ℕ) (_b₀ : Fin _H → Fin 5 → ℝ) (_w : Fin _H → ℝ) (_mark : Fin _H → Fin _J → Bool), MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ) := fun (σ : ℝ) (H J : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) => (((MarkedPrior σ H b₀ w).prod MeasureTheory.volume).restrict (MarkedEvent H J mark))

abbrev Tables : ∀ (_N _K _m : ℝ) (_M _H _J : ℕ) (_b₀ : Fin _H → Fin 5 → ℝ) (_w : Fin _H → ℝ) (_mark : Fin _H → Fin _J → Bool), Prop := fun (N K m : ℝ) (M H J : ℕ) (b₀ : Fin H → Fin 5 → ℝ) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) => (1 ≤ J ∧ (H : ℝ) ≤ N ^ (M : ℝ) ∧ (J : ℝ) ≤ N ^ (M : ℝ) ∧ 1 ≤ (J : ℝ) * N ^ (-m) ∧ (J : ℝ) * N ^ (-m) ≤ 2 ∧ (∀ j, 0 ≤ w j) ∧ (∑ j, w j) = 1 ∧ (∀ j e, |b₀ j e| ≤ K) ∧ ENNReal.ofReal (K⁻¹) ≤ MarkedLaw (N ^ (-m)) H J b₀ w mark Set.univ)

abbrev scalarCell : ∀ (N u₀ : ℝ) (z : Fin 2 → ℤ), Set (ℕ × (Fin 5 → ℝ)) := fun (N u₀ : ℝ) (z : Fin 2 → ℤ) => {l | (⌊l.2 0 / N ^ (-u₀)⌋ : ℤ) = z 0 ∧ (⌊l.2 1 / N ^ (-u₀)⌋ : ℤ) = z 1}

abbrev scalarCropLine : ∀ (N u₀ : ℝ) (z : Fin 2 → ℤ) (l : (ℕ × (Fin 5 → ℝ))), (ℕ × (Fin 5 → ℝ)) := fun (N u₀ : ℝ) (z : Fin 2 → ℤ) (l : (ℕ × (Fin 5 → ℝ))) => (l.1, ![l.2 0 / N ^ (-u₀) - (z 0 : ℝ), l.2 1 / N ^ (-u₀) - (z 1 : ℝ), l.2 2, l.2 3, l.2 4])

abbrev scalarCropPoint : ∀ (N u₀ : ℝ) (z : Fin 2 → ℤ) (p : ((ℕ × (Fin 5 → ℝ)) × ℝ)), ((ℕ × (Fin 5 → ℝ)) × ℝ) := fun (N u₀ : ℝ) (z : Fin 2 → ℤ) (p : ((ℕ × (Fin 5 → ℝ)) × ℝ)) => (scalarCropLine N u₀ z p.1, p.2)

abbrev y : ∀ (l : (ℕ × (Fin 5 → ℝ))) (t : ℝ), ℝ := fun (l : (ℕ × (Fin 5 → ℝ))) (t : ℝ) => l.2 0 + t * l.2 1

abbrev x : ∀ (l : (ℕ × (Fin 5 → ℝ))) (t : ℝ), ℝ := fun (l : (ℕ × (Fin 5 → ℝ))) (t : ℝ) => l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

abbrev selected : ∀ (ν : MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E : Set ((ℕ × (Fin 5 → ℝ)) × ℝ)), MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ) := fun (ν : MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E : Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) => (ν.prod MeasureTheory.volume).restrict E

abbrev LiftFacts : ∀ (N : ℕ → ℝ) (u₀ : ℝ) (W : ℕ → ℕ) (ν₀ : ℕ → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E₀ : ℕ → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (p : (k : ℕ) → Fin (W k) → ℝ) (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ), Prop := fun (N : ℕ → ℝ) (u₀ : ℝ) (W : ℕ → ℕ) (ν₀ : ℕ → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E₀ : ℕ → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (p : (k : ℕ) → Fin (W k) → ℝ) (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ) => (∀ k γ, MeasurableSet (scalarCell (N k) u₀ (z k γ))) ∧ (∀ k γ, Measurable (scalarCropLine (N k) u₀ (z k γ))) ∧ (∀ k, Pairwise (fun γ γ' => Disjoint (scalarCell (N k) u₀ (z k γ)) (scalarCell (N k) u₀ (z k γ')))) ∧ (∀ k γ Z, MeasurableSet Z → ENNReal.ofReal (p k γ) * selected (ν k γ) (E k γ) Z = selected (ν₀ k) (E₀ k) {a | a.1 ∈ scalarCell (N k) u₀ (z k γ) ∧ (scalarCropLine (N k) u₀ (z k γ) a.1, a.2) ∈ Z}) ∧ (∀ k γ l, l ∈ scalarCell (N k) u₀ (z k γ) → ∀ t, x (scalarCropLine (N k) u₀ (z k γ) l) t = x l t) ∧ (∀ k γ l, l ∈ scalarCell (N k) u₀ (z k γ) → ∀ t, y (scalarCropLine (N k) u₀ (z k γ) l) t = (y l t - N k ^ (-u₀) * (z k γ 0 : ℝ) - t * (N k ^ (-u₀) * (z k γ 1 : ℝ))) / N k ^ (-u₀)) ∧ (∀ k γ l, l ∈ scalarCell (N k) u₀ (z k γ) → ∀ t ∈ Set.Icc (0 : ℝ) 1, |y (scalarCropLine (N k) u₀ (z k γ) l) t| ≤ 2)

abbrev ScalarCrops : ∀ (N K : ℕ → ℝ) (ν₀ : ℕ → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E₀ : ℕ → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (u₀ α : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (p : (k : ℕ) → Fin (W k) → ℝ) (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ) (ρ : ℕ → ℝ), Prop := fun (N K : ℕ → ℝ) (ν₀ : ℕ → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E₀ : ℕ → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (u₀ α : ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) (p : (k : ℕ) → Fin (W k) → ℝ) (z : (k : ℕ) → Fin (W k) → Fin 2 → ℤ) (ρ : ℕ → ℝ) => (∀ k, MeasureTheory.IsProbabilityMeasure (ν₀ k) ∧ MeasurableSet (E₀ k) ∧ E₀ k ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1) ∧ (∀ k, Function.Injective (z k)) ∧ (∀ k γ, 0 < p k γ ∧ p k γ = ((ν₀ k) (scalarCell (N k) u₀ (z k γ))).toReal ∧ ν k γ = (ENNReal.ofReal (p k γ))⁻¹ • MeasureTheory.Measure.map (scalarCropLine (N k) u₀ (z k γ)) ((ν₀ k).restrict (scalarCell (N k) u₀ (z k γ))) ∧ E k γ = scalarCropPoint (N k) u₀ (z k γ) '' (E₀ k ∩ (scalarCell (N k) u₀ (z k γ) ×ˢ Set.univ)) ∧ |N k ^ (-u₀) * (z k γ 0 : ℝ)| + |N k ^ (-u₀) * (z k γ 1 : ℝ)| ≤ K k) ∧ (∀ k, 0 < ρ k ∧ ρ k ≤ 1 ∧ (∑ γ, p k γ) = ρ k ∧ ∀ γ, ω k γ = p k γ / ρ k) ∧ (∀ τ : ℝ, 0 < τ → ∀ᶠ k in Filter.atTop, (ρ k)⁻¹ ≤ N k ^ τ) ∧ (∀ τ : ℝ, 0 < τ → ∀ᶠ k in Filter.atTop, ∀ γ, N k ^ (-α - τ) ≤ p k γ ∧ p k γ ≤ N k ^ (-α + τ)) ∧ LiftFacts N u₀ W ν₀ E₀ ν E p z

abbrev Format : ∀ (n : ℕ) (B : ℝ) (D : ℕ) (A : Set (Fin n → ℝ)), Prop := fun (n : ℕ) (B : ℝ) (D : ℕ) (A : Set (Fin n → ℝ)) => ∃ k : ℕ, (k : ℝ) ≤ B ∧ ∃ p : Fin k → MvPolynomial (Fin n) ℝ, (∀ j, (p j).totalDegree ≤ D ∧ ∀ b, |(p j).coeff b| ≤ B) ∧ ∃ S : Set (Fin k → SignType), A = {x | (fun j => SignType.sign (MvPolynomial.eval x (p j))) ∈ S}

abbrev WorldFormat : ∀ (N K : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)), Prop := fun (N K : ℕ → ℝ) (W : ℕ → ℕ) (ω : (k : ℕ) → Fin (W k) → ℝ) (ν : (k : ℕ) → Fin (W k) → MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) (E : (k : ℕ) → Fin (W k) → Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) => ∃ M D : ℕ, 1 ≤ M ∧ 1 ≤ D ∧ (∀ k, (W k : ℝ) ≤ N k ^ (M : ℝ) ∧ (∀ γ, 0 ≤ ω k γ) ∧ (∑ γ, ω k γ) = 1 ∧ (∀ γ, MeasureTheory.IsProbabilityMeasure (ν k γ) ∧ (∃ n : ℕ, (n : ℝ) ≤ N k ^ (M : ℝ) ∧ ∃ (h : Fin n → ℝ) (i : Fin n → ℕ) (B : Fin n → Set (Fin 5 → ℝ)), (∀ j, 0 ≤ h j ∧ h j ≤ N k ^ (M : ℝ) ∧ (i j : ℝ) ≤ N k ^ (M : ℝ) ∧ Format 5 (N k ^ (M : ℝ)) D (B j) ∧ ∀ b ∈ B j, ∀ e, |b e| ≤ N k ^ (M : ℝ)) ∧ ν k γ = ∑ j, ENNReal.ofReal (h j) • MeasureTheory.Measure.map (fun b => (i j, b)) (MeasureTheory.volume.restrict (B j))) ∧ (∀ᵐ l ∂ν k γ, ∀ e, |l.2 e| ≤ K k) ∧ MeasurableSet (E k γ) ∧ E k γ ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 ∧ (∀ p ∈ E k γ, (p.1.1 : ℝ) ≤ N k ^ (M : ℝ)) ∧ (∀ i : ℕ, Format 6 (N k ^ (M : ℝ)) D {b : Fin 6 → ℝ | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ E k γ})) ∧ ENNReal.ofReal ((K k)⁻¹) ≤ ∑ γ, ENNReal.ofReal (ω k γ) * selected (ν k γ) (E k γ) Set.univ)

end

end Submission.Obl.k4_scalar_conditional_crop_worlds
