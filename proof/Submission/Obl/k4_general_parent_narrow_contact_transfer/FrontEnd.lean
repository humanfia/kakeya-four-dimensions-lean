/- Retained from this obligation, o255, branch x0901 at commit 0f8ba410.
   Earlier source attributions in this file are preserved. -/
import Submission.Obl.k4_general_parent_narrow_contact_transfer.Reduction
import Submission.Obl.k4_general_parent_narrow_contact_transfer.RenewalBridge
import Submission.Obl.k4_general_parent_narrow_contact_transfer.Renewal.RowParent

/-!
# The two halves of the narrow alternative

`NarrowCore` (Reduction.lean) splits at row parents, the output of the row-fit
part of the paper's Proposition 8.5:

* `NarrowFront`: a fixed-power narrow ordinary layer gives, at one fixed true
  depth `r < U`, row parents frequently (or the candidates directly). This uses
  the comparison of true and projected labels (Match) and the row fit (Row).
* `NarrowBack`: row parents frequently give the candidates. Power-small skew
  gives strips; otherwise the zoomed, row-normalized parent law is a contact
  instance, and the contact principle applies (renewal and pullback).

`core_of_front_back` proves `NarrowCore` from the two.
-/

namespace Submission.Obl.k4_general_parent_narrow_contact_transfer

open MeasureTheory Set Filter

/-- Row parents at the true depth `r`, frequently, with power-small row error
`N^(-e)` and subpower size bound `M`. -/
def RowParents {α : Type} [MeasurableSpace α] (cfg : Model α) (r : ℝ) : Prop :=
  ∃ e : ℝ, 0 < e ∧ ∃ M : ℕ → ℝ, (∀ k, 1 ≤ M k) ∧ Model.Subpow cfg.N M ∧
    ∃ᶠ k in atTop, Nonempty
      (Renewal.RowParent (Model.parameters cfg) (Model.prepared cfg) k r
        (cfg.N k ^ (-e)) (M k))

/-- The front half: narrow layers give row parents at one depth below `U`. -/
def NarrowFront : Prop :=
  Row → Match →
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
        cfg.Candidates ∨ ∃ r : ℝ, 0 < r ∧ r < cfg.U ∧ RowParents cfg r

/-- The back half: row parents give the candidates. -/
def NarrowBack : Prop :=
  Principle 3 →
  ∀ (α : Type) [MeasurableSpace α] (cfg : Model α), Model.Valid cfg →
    ∀ r : ℝ, 0 < r → r < cfg.U → RowParents cfg r → cfg.Candidates

theorem core_of_front_back (hf : NarrowFront) (hb : NarrowBack) : NarrowCore := by
  intro hRow hMatch h3 α _ cfg hv
  obtain ⟨Λ, hΛ, hfront⟩ := hf hRow hMatch α cfg hv
  refine ⟨Λ, hΛ, ?_⟩
  intro L₀ hL₀ hlay a s ha haU has hs2 τ H ρ' β n' C tag u v G hw
  rcases hfront L₀ hL₀ hlay a s ha haU has hs2 τ H ρ' β n' C tag u v G hw with
    hc | ⟨r, hr, hrU, hrows⟩
  · exact hc
  · exact hb h3 α cfg hv r hr hrU hrows

/-- The frozen statement from the two halves. -/
theorem main_of_front_back (hf : NarrowFront) (hb : NarrowBack) :
    Row → Match → RawPrinciple 3 → RawPrinciple 0 → RawPrinciple 1 → RawPrinciple 2 :=
  main_of_core (core_of_front_back hf hb)

end Submission.Obl.k4_general_parent_narrow_contact_transfer
