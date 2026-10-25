import Mathlib
import ChallengeDeps
import Submission.Obl.k4_scalar_marked_terminal_support.Cover
import Submission.Obl.k4_scalar_marked_terminal_support.Noise
import Submission.Obl.k4_scalar_marked_terminal_support.Transfer
set_option linter.unusedVariables false

/-!
# `Submission.k4_scalar_marked_terminal_support`

Prove the theorem at the end of this file and keep its statement exactly as
it is. Put helper declarations in `namespace Submission.Obl.k4_scalar_marked_terminal_support`, where others can
reuse them, or make them `private`. Only this file and `Submission/Obl/k4_scalar_marked_terminal_support/`
belong to this obligation.
-/

theorem Submission.k4_scalar_marked_terminal_support : ((fun (Noise : ∀ (σ : ℝ), MeasureTheory.Measure (Fin 5 → ℝ)) => ((fun (MarkedPrior : ∀ (σ : ℝ) (H : ℕ) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ), MeasureTheory.Measure (ℕ × (Fin 5 → ℝ))) => ((fun (timeCell : ∀ (J : ℕ) (z : Fin J), Set ℝ) => ((fun (MarkedEvent : ∀ (H J : ℕ) (mark : Fin H → Fin J → Bool), Set ((ℕ × (Fin 5 → ℝ)) × ℝ)) => ((fun (MarkedLaw : ∀ (σ : ℝ) (H J : ℕ) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool), MeasureTheory.Measure ((ℕ × (Fin 5 → ℝ)) × ℝ)) => ((fun (curveX : ∀ {α : Type} (b : α → (Fin 5 → ℝ)) (l : α) (t : ℝ), ℝ) => ((fun (curveY : ∀ {α : Type} (b : α → (Fin 5 → ℝ)) (l : α) (t : ℝ), ℝ) => ((fun (meshCode : ∀ {α : Type} (b : α → (Fin 5 → ℝ)) (σ : ℝ) (p : α × ℝ), Fin 2 → ℤ) => ((fun (baseRef : MeasureTheory.Measure ((Fin 2 → ℝ) × ℤ)) => ∃ A : ℝ, 1 ≤ A ∧ ∃ q : ℕ, ∀ K σ a δ : ℝ, 1 ≤ K → 0 < δ → δ ≤ σ → 0 < σ → σ ≤ 1 → σ ≤ a → ∀ (α : Type) [MeasurableSpace α] (μ : MeasureTheory.Measure (α × ℝ)) (b : α → (Fin 5 → ℝ)), Measurable b → (∀ l i, |b l i| ≤ K) → ∀ (H J : ℕ) (tag : α → Fin H) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool), 1 ≤ J → 1 ≤ (J : ℝ) * σ → (J : ℝ) * σ ≤ 2 → Measurable tag → (∀ j, 0 ≤ w j) → (∀ l i, |b l i - b₀ (tag l) i| ≤ δ) → (∀ j z, mark j z = true → ENNReal.ofReal (w j / ((J : ℝ) * (2 * K))) ≤ μ {p | tag p.1 = j ∧ p.2 ∈ timeCell J z}) → ∀ F : Finset ((Fin 2 → ℤ) × ℤ), (∀ᵐ p ∂μ, (meshCode b σ p, (⌊curveX b p.1 p.2 / a⌋ : ℤ)) ∈ F) → ∃ B : Set ((Fin 2 → ℝ) × ℤ), MeasurableSet B ∧ baseRef B ≤ ENNReal.ofReal (A * K ^ q * ((F.card : ℝ) * σ ^ 2)) ∧ ∀ᵐ p ∂(MarkedLaw σ H J b₀ w mark), ((![p.2, curveY Prod.snd p.1 p.2] : Fin 2 → ℝ), (⌊curveX Prod.snd p.1 p.2 / a⌋ : ℤ)) ∈ B) (MeasureTheory.volume.prod (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)))) (fun {α : Type} (b : α → (Fin 5 → ℝ)) (σ : ℝ) (p : α × ℝ) => ![⌊p.2 / σ⌋, ⌊curveY b p.1 p.2 / σ⌋]))) (fun {α : Type} (b : α → (Fin 5 → ℝ)) (l : α) (t : ℝ) => b l 0 + t * b l 1))) (fun {α : Type} (b : α → (Fin 5 → ℝ)) (l : α) (t : ℝ) => b l 2 + t * b l 3 + t ^ 2 * b l 4))) (fun (σ : ℝ) (H J : ℕ) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool) => ((MarkedPrior σ H b₀ w).prod MeasureTheory.volume).restrict (MarkedEvent H J mark)))) (fun (H J : ℕ) (mark : Fin H → Fin J → Bool) => {p | ∃ j : Fin H, p.1.1 = (j : ℕ) ∧ ∃ z : Fin J, mark j z = true ∧ p.2 ∈ timeCell J z}))) (fun (J : ℕ) (z : Fin J) => Set.Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))))) (fun (σ : ℝ) (H : ℕ) (b₀ : Fin H → (Fin 5 → ℝ)) (w : Fin H → ℝ) => ∑ j, ENNReal.ofReal (w j) • MeasureTheory.Measure.map (fun u : (Fin 5 → ℝ) => ((j : ℕ), b₀ j + u)) (Noise σ)))) (fun (σ : ℝ) => MeasureTheory.Measure.pi (fun _ : Fin 5 => ENNReal.ofReal (σ⁻¹) • MeasureTheory.volume.restrict (Set.Icc 0 σ)))) := by
  dsimp only
  refine ⟨2000, by norm_num, 2, ?_⟩
  intro K σ a δ hK hδ hδσ hσ hσ1 hσa α _ μ b hbm hb H J tag b₀ w mark
    hJ hJσ hJσ2 htag hw hround hmark F hF
  refine ⟨Submission.Obl.k4_scalar_marked_terminal_support.observationCover K σ F,
    Submission.Obl.k4_scalar_marked_terminal_support.measurableSet_observationCover K σ F,
    Submission.Obl.k4_scalar_marked_terminal_support.reference_observationCover_le hK hσ.le F,
    ?_⟩
  exact Submission.Obl.k4_scalar_marked_terminal_support.support_transfer hK hδσ hσ hσa
    μ b hb tag b₀ w mark hJ hJσ hw hround hmark F hF
