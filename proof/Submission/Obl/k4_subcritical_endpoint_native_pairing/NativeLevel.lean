import Submission.Obl.k4_subcritical_endpoint_native_pairing.NativeTable
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeLevel

/-! Reuse the common original native foundation from accepted o263. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Data

open Set MeasureTheory Filter MvPolynomial
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

abbrev NativeLevel (cfg : Data α) (k : ℕ) (s : ℝ) :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.NativeLevel cfg k s

theorem Prepared.eventually_native_level (h : cfg.Prepared) {s : ℝ}
    (hs : 0 < s) (hsU : s ≤ cfg.U) :
    ∀ᶠ k in atTop, Nonempty (cfg.NativeLevel k s) :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.Prepared.eventually_native_level h hs hsU

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Data
