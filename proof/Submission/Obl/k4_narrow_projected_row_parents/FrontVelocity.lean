/- Adapted from this LOT tree o255, session x0901, commit25b5b5db,
   Submission/Obl/k4_general_parent_narrow_contact_transfer/ListGlue2.lean. -/
import Submission.Obl.k4_narrow_projected_row_parents.VelocityGlue
import Submission.Obl.k4_narrow_projected_row_parents.Front

namespace Submission.Obl.k4_narrow_projected_row_parents

open MeasureTheory Set Filter

/-- `NarrowLists` with velocity lists in place of listed parents; the mesh is at least as
fine as the parent's transverse width (`ℓ r ≤ aξ`). -/
def NarrowVel : Prop :=
  Match →
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
        cfg.Candidates ∨ ∃ r aξ e : ℝ, 0 < r ∧ 0 < e ∧ e < aξ ∧ cfg.ℓ * r ≤ aξ ∧
          r + aξ / cfg.κ + e / cfg.ℓ < cfg.U ∧ VelocityLists cfg r aξ e

/-- The global velocity-list comparison is the remaining input to the frozen front. -/
theorem narrowFront_of_vel (h : NarrowVel) : NarrowFront := by
  intro hRow hMatch α _ cfg hv
  obtain ⟨Λ, hΛ, hf⟩ := h hMatch α cfg hv
  refine ⟨Λ, hΛ, ?_⟩
  intro L₀ hL₀ hlay a s ha haU has hs2 τ H ρ' β n' C tag u v G hw
  rcases hf L₀ hL₀ hlay a s ha haU has hs2 τ H ρ' β n' C tag u v G hw with
    hc | ⟨r, aξ, e, hr, he, heξ, _hℓr, hroom, hvl⟩
  · exact Or.inl hc
  · have hrU : r < cfg.U := by
      have := div_pos (he.trans heξ) hv.rate_pos
      have := div_pos he hv.transverse_pos
      linarith
    exact Or.inr ⟨r, hr, hrU, rowParents_of_velocityLists hRow cfg hv hr he heξ hroom hvl⟩

end Submission.Obl.k4_narrow_projected_row_parents
