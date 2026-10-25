/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 834638c014c0cbff19a3094ac9f8f299bfd756b8, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeProductComparison.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeProductStatement

/-!
# The product comparison of a successful mark

`native_product_comparison`: for every actual mark outside `c.badMarks M`, the physical witness
predictor and the old full-time predictor differ by at most `M` on the WHOLE native time block
and the WHOLE static parameter cell of the old group. The common colour frame maps this product
into the matching half ball (`nativeComparisonFrame_product`), where the mark's normalized
comparison holds, and the frame's rechart returns to the physical predictors
(`ComparisonFrame.rechart_parameterPoint`).
-/

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

attribute [local instance] sum_measurableSingletonClass

namespace NativeComparisonData

variable {α : Type} [MeasurableSpace α] {cfg : NativeModel α}
  {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)} (c : NativeComparisonData cfg k s σ)

theorem native_product_comparison (M : ℝ) : NativeProductComparison c M := by
  intro r hr t ht p hp q hq
  let T := c.support.table
  let l : c.Colour := (c.group (T.old r), cfg.j k s (T.native r))
  have hq0 : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hD0 : 0 < c.D := c.D_pos
  -- the whole product lies in the half ball of the common frame
  let z := (c.frame l).parameterPoint t p q
  have hzhalf : ‖z‖ ≤ 1 / 2 := by
    apply nativeComparisonFrame_product hq0 hD0
    · simpa only [l, T, Data.I, Data.timeLength, div_eq_mul_inv] using ht
    · dsimp only [l, T]
      exact ⟨by nlinarith [hp.1], by nlinarith [hp.2]⟩
    · dsimp only [l, T]
      exact ⟨by nlinarith [hq.1], by nlinarith [hq.2]⟩
  -- the mark is good
  have hgood : |predictor (c.comparison.coefficients (c.comparison.source r)) (z 0) (z 1) (z 2) -
      predictor (c.comparison.coefficients (c.comparison.witness r)) (z 0) (z 1) (z 2)| < M := by
    by_contra h
    exact hr ⟨z, hzhalf, le_of_not_gt h⟩
  -- both coefficients are the frame's rechart of the physical predictors
  have hsrc : c.comparison.coefficients (c.comparison.source r) =
      (c.frame l).rechart (c.hH (T.old r)) := rfl
  have hwit : c.comparison.coefficients (c.comparison.witness r) =
      (c.frame l).rechart (c.physical (T.witness c.group (cfg.j k s) r)) := rfl
  have hts : (c.frame l).timeScale ≠ 0 := by
    change 16 * cfg.timeLength k s ≠ 0; positivity
  have hps : (c.frame l).parameterScale ≠ 0 := by
    change 16 * c.D ≠ 0; positivity
  dsimp only [z] at hgood
  rw [hsrc, hwit, (c.frame l).rechart_parameterPoint _ t p q hts hps,
    (c.frame l).rechart_parameterPoint _ t p q hts hps] at hgood
  rw [abs_sub_comm]
  exact hgood.le

end NativeComparisonData

end

end Submission.Obl.k4_horizontal_strict_parameter_step
