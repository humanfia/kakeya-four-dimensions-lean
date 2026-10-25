/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at c4765076c45bb6cb7fbc53c5859035579f22a4b1, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeGoodSelection.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeMenuStatement
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeBlockChoice

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

/-- Freeze one actual successful native entry for each old chart and each
original time block, paying only the bounded list factor. The trajectory prior
and every original witness floor remain those fixed before this selection. -/
theorem select_native_blocks (lev : cfg.AssignmentLevel k s) (hbasic : cfg.Basic)
    {M δ : ℝ} (hmenu : NativeMenuBound c M δ)
    (hfactor : 0 ≤ (100800 * cfg.K k * (M / c.a) ^ cfg.d) / δ) :
    ∃ choice : Fin c.m → Fin (2 ^ cfg.T k s) → Option (Fin (cfg.n k s)),
      (∀ h block i, choice h block = some i → c.paired M δ h i ∧ cfg.j k s i = block) ∧
      ∃ τ : Measure (α × ℝ), τ ≤ c.goodLaw M δ ∧
        c.goodLaw M δ univ ≤
          ENNReal.ofReal ((100800 * cfg.K k * (M / c.a) ^ cfg.d) / δ) * τ univ ∧
        ∀ᵐ p ∂τ, ∃ h i, p.1 ∈ c.AH h ∧ p.1 ∈ cfg.B k s i ∧
          p.2 ∈ Data.I (cfg.T k s) (cfg.j k s i) ∧ choice h (cfg.j k s i) = some i := by
  letI := (hbasic k).2.1
  have hdom : c.goodLaw M δ ≤ ENNReal.ofReal (cfg.K k) • (cfg.ν k).prod volume :=
    (c.goodLaw_le M δ).trans (c.dominated.trans (hbasic k).2.2.2.1)
  exact Submission.Obl.k4_subcritical_corrected_scalar_charts.exists_native_block_choice
    (cfg.ν k) (c.goodLaw M δ) (ENNReal.ofReal (cfg.K k)) hdom
    (cfg.T k s) c.m (cfg.n k s) c.AH c.layer.1
    (fun i j hij => c.layer.2.1 i j hij) (cfg.B k s) lev.fitted_measurable
    (cfg.j k s) (c.paired M δ) hfactor hmenu (c.goodLaw_paired_cover M δ)

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
