-- Adapted from this LOT tree, obligation o200, branch x0934, commit 2510f406, file Submission/Obl/k4_finite_projected_horizontal_candidates/TrueSourceFactory.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.Native.
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.TrueSourceFamilies

/-! The original true-family output consumed by the prepared comparison. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set MvPolynomial
open Submission.Obl.k4_general_parent_projected_layers

noncomputable section

def TrueSourceFactory {α : Type} [MeasurableSpace α]
    (p : Parameters) (a : PreparedModel α) (k : ℕ) (s q χ m aTable : ℝ) (Kchart : NNReal)
    (E : Set (α × ℝ)) (assign : α × ℝ → Fin (a.n k s))
    (g : Fin (a.n k s) → Bool → EuclideanSpace ℂ (Fin 3) → ℂ) : Prop :=
  ∀ (μD : Measure (α × ℝ)) (c : CommonDomain.Code), μD ≪ a.mu k → μD E = 0 →
    (∀ᵐ z ∂μD, CommonDomain.code q χ (PreparedModel.narrow p k s) m (a.b k z.1) z.2 = c) →
    ∃ (F : OriginalSheetFamily μD 4 aTable Kchart (commonBase a k q χ (PreparedModel.narrow p k s) m c)
        (fun z => eval (a.x k z.1 z.2) (a.P k)))
      (idx : Fin F.n → Fin (a.n k s) × Bool),
      Function.Injective idx ∧
      (∀ i z, z ∈ F.witness i → z.1 ∈ a.B k s (idx i).1 ∧ z.2 ∈ a.block k s (idx i).1) ∧
      (∀ i z, z ∈ F.witness i →
        F.f i = trueCandidate p a k s g q χ (PreparedModel.narrow p k s) m c (idx i)) ∧
      ∀ᵐ z ∂μD, idx (F.index z) = (assign z, nativeBranch p a k s (assign z) z)

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
