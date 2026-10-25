-- Adapted from this LOT tree, obligation o254, branch x0898, commit 91a4f454, file Submission/Obl/k4_general_parent_wide_layer_candidates/NativeParentLists.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.ProjectedSlices

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The true/coarse native comparison returned to the original labels
and original short domains, before the fine-layer event assembly. -/
structure NativeParentLists (k : ℕ) (r m H : ℝ)
    (L : ProjectedLayer α) (σ : Measure (α × ℝ)) where
  law : Measure (α × ℝ)
  le_source : law ≤ σ
  mass_lower : ENNReal.ofReal H⁻¹ ≤ law Set.univ
  parent : α × ℝ → Fin (p.n k r)
  coarse : α × ℝ → Fin L.count
  measurable_parent : Measurable parent
  measurable_coarse : Measurable coarse
  coarseChoices : Fin (p.n k r) → (Fin 2 → ℤ) → Finset (Fin L.count)
  coarse_card : ∀ Q tag, ((coarseChoices Q tag).card : ℝ) ≤ H
  reverseChoices : (Fin 2 → ℤ) → (ℤ × ℤ × ℤ) → Fin L.count → Finset (Fin (p.n k r))
  reverse_card : ∀ tag D i, ((reverseChoices tag D i).card : ℝ) ≤ H
  source_data : ∀ᵐ ω ∂law,
    ω.1 ∈ p.B k r (parent ω) ∧
    ω.2 ∈ block (p.T k r) (p.j k r (parent ω)) ∧
    ω.1 ∈ L.C (coarse ω) ∧
    coarse ω ∈ coarseChoices (parent ω) (L.tag (coarse ω)) ∧
    parent ω ∈ reverseChoices (L.tag (coarse ω))
      (p.domainCode k ((2 : ℝ) ^ (-(p.T k r : ℤ))) (p.N k ^ (-p.ℓ * r))
        ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) ω) (coarse ω)

end Parent

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
