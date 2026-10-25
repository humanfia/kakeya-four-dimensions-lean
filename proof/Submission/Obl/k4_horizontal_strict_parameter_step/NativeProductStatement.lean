/- Adapted from this LOT tree, obligation o245, session x0854,
branch x0854 at ba3817bb17b771a5ddd349237fa63f3fef2ba670, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/NativeProductStatement.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeMatching

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Lib.K4AffineMeshCaps
open Submission.Obl.k4_critical_derivative_evaluation_lists

noncomputable section

/-- A successful actual marked comparison holds on the WHOLE original static
parameter cell and native time block. These are the domains of original floors,
including points outside the later current observed pair fibre. -/
def NativeProductComparison {α : Type} [MeasurableSpace α]
    {cfg : NativeModel α} {k : ℕ} {s : ℝ} {σ : Measure (α × ℝ)}
    (c : NativeComparisonData cfg k s σ) (M : ℝ) : Prop :=
  ∀ r : Fin c.support.table.count, r ∉ c.badMarks M →
    ∀ t ∈ Data.I (cfg.T k s) (cfg.j k s (c.support.table.native r)),
    ∀ p ∈ Icc ((c.group (c.support.table.old r) 1 : ℝ) * c.D)
      (((c.group (c.support.table.old r) 1 : ℝ) + 1) * c.D),
    ∀ q ∈ Icc ((c.group (c.support.table.old r) 2 : ℝ) * c.D)
      (((c.group (c.support.table.old r) 2 : ℝ) + 1) * c.D),
    |predictor (c.physical (c.support.table.witness c.group (cfg.j k s) r)) t p q -
      predictor (c.hH (c.support.table.old r)) t p q| ≤ M

end

end Submission.Obl.k4_horizontal_strict_parameter_step
