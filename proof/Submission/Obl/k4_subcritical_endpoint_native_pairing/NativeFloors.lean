import Submission.Obl.k4_subcritical_endpoint_native_pairing.NativeData
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeFloors

/-! Reuse the common original native foundation from accepted o263. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Data

open Set MeasureTheory Filter MvPolynomial
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem Prepared.native_prior_bounds (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2 ≤
        (cfg.ν k).real (cfg.A k s i) ∧
      (cfg.ν k).real (cfg.A k s i) ≤
        cfg.K k ^ 2 * cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.Prepared.native_prior_bounds h a i

theorem Prepared.native_witness_lower (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s)
    (hμ : ∀ i, ENNReal.ofReal (cfg.timeLength k s / cfg.K k) * cfg.ν k (cfg.A k s i) ≤
      cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)))
    (i : Fin (cfg.n k s)) :
    ENNReal.ofReal (cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 3) ≤
      cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.Prepared.native_witness_lower h a hμ i

theorem Prepared.native_assignment_budget (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) :
    (∑ i, ENNReal.ofReal (cfg.timeLength k s) * cfg.ν k (cfg.A k s i)) ≤ 1 :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.Prepared.native_assignment_budget h a

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Data
