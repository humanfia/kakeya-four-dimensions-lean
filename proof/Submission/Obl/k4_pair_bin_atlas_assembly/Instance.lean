import Submission.Obl.k4_pair_bin_atlas_assembly.Interface

-- Adapted from this LOT tree, o158, session x0532, branch x0532:
-- Submission/Obl/k4_matched_pair_representative_realization/Instance.lean
-- (the structures `IndexFacts` and the predicate `RoughBody`).

/-!
# One frequent index of the realization: input and output data

`IndexFacts` collects the global
fields of `paired` at that index.  `RoughBody` is the body of `roughSys` at one index, after
the time scale `2 ^ T` and the slack `κ` have been chosen.
-/

namespace Submission.Obl.k4_pair_bin_atlas_assembly

open Submission.Obl.k4_quadratic_atlas_normalization

set_option linter.unusedVariables false

/-- Trajectory labels `(index, six affine parameters)`. -/
abbrev Traj := ℕ × (Fin 6 → ℝ)

/-- The block `[j / 2^T, (j + 1) / 2^T]`. -/
def tblock (T : ℕ) (j : ℝ) : Set ℝ := Set.Icc (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T)

/-- The global fields of `paired` at one index. -/
structure IndexFacts (N : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → MeasureTheory.Measure Traj)
    (E : Fin W → Set (Traj × ℝ)) (B : Fin W → ℝ) (Mb Me De : ℕ) : Prop where
  two_le : 2 ≤ N
  ω_nonneg : ∀ γ, 0 ≤ ω γ
  ω_sum : (∑ γ, ω γ) = 1
  ν_prob : ∀ γ, MeasureTheory.IsProbabilityMeasure (ν γ)
  B_bounds : ∀ γ, 0 < B γ ∧ B γ ≤ N ^ Mb ∧ (B γ)⁻¹ ≤ N ^ Mb
  E_meas : ∀ γ, MeasurableSet (E γ)
  E_fmt : ∀ γ i, fmt 7 (N ^ Me) De {r : Fin 7 → ℝ | ((i, fun z : Fin 6 => r z.castSucc), r 6) ∈ E γ}

/-- The body of `roughSys` at one index, once `κ` and `T` are chosen. -/
def RoughBody (N : ℝ) (W : ℕ) (ω : Fin W → ℝ) (ν : Fin W → MeasureTheory.Measure Traj)
    (E : Fin W → Set (Traj × ℝ)) (B : Fin W → ℝ) (L a : ℝ) (M D : ℕ) (κ : ℝ) (T : ℕ) : Prop :=
  ∃ C' : ℕ, ∃ (γ : Fin C' → Fin W) (j : Fin C' → Fin (2 ^ T))
    (c u : Fin C' → EuclideanSpace ℝ (Fin 2)) (Q : Fin C' → Matrix (Fin 2) (Fin 2) ℝ)
    (R : Fin C' → MvPolynomial (Fin 4) ℝ) (A : Fin C' → Set Traj) (F : Fin C' → Set (Traj × ℝ))
    (lst : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C')),
    (C' : ℝ) ≤ N ^ M ∧ (∀ b b', b ≠ b' → γ b = γ b' → j b = j b' → Disjoint (A b) (A b')) ∧
    (∀ γ₁ o, ((lst γ₁ o).card : ℝ) ≤ κ) ∧
    (∀ b, rough N M D κ T ((j b : ℕ) : ℝ) L a (B (γ b)) (E (γ b)) (c b) (u b) (Q b) (R b) (A b)
      (F b) (∀ p ∈ F b, b ∈ lst (γ b) (obs (B (γ b)) (δ N L) p))) ∧
    ENNReal.ofReal κ⁻¹ ≤ ∑ b, ENNReal.ofReal (ω (γ b)) * ((ν (γ b)).prod MeasureTheory.volume) (F b)

end Submission.Obl.k4_pair_bin_atlas_assembly
