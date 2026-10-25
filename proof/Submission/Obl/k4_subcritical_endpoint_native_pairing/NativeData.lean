import Submission.Obl.k4_subcritical_endpoint_native_pairing.Model
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeData

/-! Reuse the common original native foundation from accepted o263. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Data

open Set MeasureTheory Filter MvPolynomial
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem Prepared.eventually_assignment_level (h : cfg.Prepared) {s : ℝ}
    (hs : 0 < s) (hsU : s ≤ cfg.U) : ∀ᶠ k in atTop, cfg.AssignmentLevel k s :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.Prepared.eventually_assignment_level h hs hsU

theorem Prepared.eventually_native_mass (h : cfg.Prepared) {s : ℝ}
    (hs : 0 < s) (hsU : s ≤ cfg.U) :
    ∀ᶠ k in atTop, ∀ i : Fin (cfg.n k s),
      ENNReal.ofReal (cfg.timeLength k s / cfg.K k) * cfg.ν k (cfg.A k s i) ≤
        cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.Prepared.eventually_native_mass h hs hsU

theorem Prepared.eventually_nested (h : cfg.Prepared) {s t : ℝ}
    (hs : 0 < s) (hst : s < t) (htU : t ≤ cfg.U) :
    ∀ᶠ k in atTop, ∀ i : Fin (cfg.n k t), ∃ ip : Fin (cfg.n k s),
      cfg.A k t i ⊆ cfg.A k s ip ∧
        I (cfg.T k t) (cfg.j k t i) ⊆ I (cfg.T k s) (cfg.j k s ip) :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.Prepared.eventually_nested h hs hst htU

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Data
