/- Adapted from: here:o009
Original counted marginal support and mesh lookup proofs developed in this workspace. -/

import Submission.Lib.K4MarginalAveraging.CountedAveraging
import Submission.Lib.K4ModelReduction.FiniteTable

/-! Pointwise height bounds and common mesh tables for counted marginals. -/

namespace Submission.Lib.K4MarginalAveraging

open MeasureTheory Set
open scoped ENNReal
open Submission.Lib.K4ModelReduction

/-- A pointwise support bound controls the explicit marginal at every
base point, including the grid corners used by a lookup table. -/
theorem countedMarginal_le_of_support {Y X A : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f : Y → X → ℝ≥0∞) (L : Y × X → A)
    (S : Set Y) (hS : MeasurableSet S) (H : ℝ≥0∞)
    (hbound : ∀ y ∈ S, ∀ x, f y x ≤ H)
    (hsupport : ∀ y ∉ S, ∀ x, f y x = 0) (z : X × A) :
    countedMarginal μ f L z ≤ H * μ S := by
  classical
  calc
    _ ≤ ∫⁻ y, S.indicator (fun _ => H) y ∂μ := by
      apply lintegral_mono
      intro y
      by_cases hy : y ∈ S
      · rw [indicator_of_mem hy]
        change (if L (y, z.1) = z.2 then f y z.1 else 0) ≤ H
        split_ifs
        · exact hbound y hy z.1
        · exact zero_le
      · rw [indicator_of_notMem hy]
        simp only [hsupport y hy z.1, ite_self, le_refl]
    _ = _ := lintegral_indicator_const hS _

/-- Every coarsening of the retained hidden labels uses the same base
mesh, so its density factors through the common finest observation code. -/
theorem exists_common_counted_mesh_table {Y A B ι : Type*} [MeasurableSpace Y]
    (μ : Measure Y) (f : Y → (ι → ℝ) → ℝ) (L : Y → A) (C : A → B)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hconstant : ∀ y x x', (∀ i, ⌊x i / ρ⌋ = ⌊x' i / ρ⌋) → f y x = f y x') :
    ∃ T : ((ι → ℤ) × A) → ℝ, ∀ (x : ι → ℝ) (a : A),
      realCountedMarginal μ f (fun z => C (L z.1)) (x, C a) = T (meshTag ρ x, a) := by
  refine ⟨fun z => realCountedMarginal μ f (fun p => C (L p.1))
    (meshRepresentative ρ z.1, C z.2), ?_⟩
  intro x a
  apply realCountedMarginal_same_cell μ f (C ∘ L) ρ hconstant
  intro i
  exact (congrFun (meshTag_representative hρ (meshTag ρ x)) i).symm

end Submission.Lib.K4MarginalAveraging
