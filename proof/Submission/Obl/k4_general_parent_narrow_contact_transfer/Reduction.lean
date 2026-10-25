/- Retained from this obligation, o255, branch x0901 at commit 0f8ba410.
   Earlier source attributions in this file are preserved. -/
import Submission.Obl.k4_general_parent_narrow_contact_transfer.Dichotomy2

/-!
# Reduction of o255 to its narrow alternative

`NarrowCore` is what remains of o255 after the wide/narrow dichotomy of
`Dichotomy.lean`: for one prepared sequence with no contact assumption, an
ordinary projected layer that is narrow by a fixed power at a requested depth
must yield the general candidates, using Row, Match and the contact principle.
`main_of_core` proves the frozen statement from it.
-/

namespace Submission.Obl.k4_general_parent_narrow_contact_transfer

open MeasureTheory Set Filter

/-- The narrow alternative of o255.  The wide constant is `Λ L₀`, chosen by the
narrow argument from the ordinary constant `L₀` (and the prepared sequence),
so that the later true parent of the narrow argument stays below `U`; it must
satisfy `L + 2 ≤ S Λ L` (needed to refine wide outputs).  The narrow ordinary
layer comes at the moderate mesh exponent `(L₀ + 1) a`. -/
def NarrowCore : Prop :=
  Row → Match → Principle 3 →
  ∀ (α : Type) [MeasurableSpace α] (cfg : Model α), Model.Valid cfg →
    ∃ Λ : ℝ → ℝ, (∀ L, 2 < L → L + 2 ≤ cfg.S * Λ L) ∧
    ∀ L₀ : ℝ, 2 < L₀ →
      (∀ a : ℝ, 0 < a → 2 * a < cfg.U → ∀ D : Finset ℝ, (∀ s ∈ D, a ≤ s ∧ s ≤ 2 * a) →
        ∀ m : ℝ, L₀ * a < m → Model.LayerOutput cfg false L₀ a D m) →
      ∀ a s : ℝ, 0 < a → Λ L₀ * a < cfg.U → a ≤ s → s ≤ 2 * a →
      ∀ (τ : ℕ → ℕ) (H : ℕ → ℝ) (ρ' : ℕ → Measure (α × ℝ)) (β : ℕ → ℝ → ℝ)
        (n' : ℕ → ℝ → ℕ) (C : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Set α)
        (tag : (k : ℕ) → (s : ℝ) → Fin (n' k s) → Fin 2 → ℤ)
        (u v : (k : ℕ) → (s : ℝ) → Fin (n' k s) → ℝ)
        (G : (k : ℕ) → (s : ℝ) → Fin (n' k s) → MvPolynomial (Fin 2) ℝ),
        Model.NarrowWitness cfg L₀ a ((L₀ + 1) * a) s τ H ρ' β n' C tag u v G →
          cfg.Candidates

theorem main_of_core (hcore : NarrowCore) :
    Row → Match → RawPrinciple 3 → RawPrinciple 0 → RawPrinciple 1 → RawPrinciple 2 := by
  intro hRow hMatch h3 h0 h1
  rw [principle_iff] at h3 h0 h1 ⊢
  intro α _ cfg hv _
  obtain ⟨Λ, hΛ, hcore'⟩ := hcore hRow hMatch h3 α cfg hv
  have h0' : Model.Layers cfg false := by
    have := h0 α cfg hv (fun h => absurd h (by decide))
    rwa [Model.Outcome, if_pos rfl] at this
  have h1' : Model.Layers cfg true → cfg.Candidates := by
    have := h1 α cfg hv (fun h => absurd h (by decide))
    rwa [Model.Outcome, if_neg (by decide), if_pos rfl] at this
  rw [Model.Outcome, if_neg (by decide), if_neg (by decide)]
  exact Model.candidates_of_layers_moderate cfg hv h0' h1' Λ hΛ hcore'

end Submission.Obl.k4_general_parent_narrow_contact_transfer
