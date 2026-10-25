-- Adapted from this LOT tree, obligation o254, branch x0898, commit 91a4f454, file Submission/Obl/k4_general_parent_wide_layer_candidates/NativePaletteSupport.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
import Submission.Obl.k4_general_wide_layer_offset_comparison.OriginalBudgets
import Submission.Obl.k4_subcritical_endpoint_native_pairing.PositivePalette

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- Positive original palette weights hold almost everywhere; there is
no cutoff for small positive bins. -/
theorem AtDepth.ae_positive_palette (hbase : p.Basic) {k : ℕ} {s R m : ℝ}
    (hat : p.AtDepth k s R) (hK : 0 ≤ p.K k)
    (hmlo : R⁻¹ ≤ m) (hmhi : m ≤ R) :
    ∀ᵐ ω ∂p.μ k,
      0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋} := by
  apply Submission.Obl.k4_subcritical_endpoint_native_pairing.ae_positive_palette_of_cell_caps
    (p.μ k) (fun _ : α × ℝ => ())
    (fun ω => ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋)
    (fun v : ℤ => p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = v})
    (ENNReal.ofReal (p.K k))
  intro _ v
  simpa only [true_and] using hat.global_palette_bin p hbase hK hmlo hmhi v

end Parent

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
