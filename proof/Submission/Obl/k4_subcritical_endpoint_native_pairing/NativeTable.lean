import Submission.Obl.k4_subcritical_endpoint_native_pairing.NativeFloors
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeTable

/-! Reuse the common original native foundation from accepted o263. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Data

open Set MeasureTheory Filter MvPolynomial
open Submission.Obl.k4_critical_intercept_concentration.Data

noncomputable section

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem Prepared.native_hidden_time_ratios (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (hs : 0 ≤ s) :
    cfg.N k ^ (-s) / cfg.timeLength k s ≤ cfg.K k ∧
      cfg.N k ^ (-s) / cfg.timeLength k s ^ 2 ≤ cfg.K k ^ 2 :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.Prepared.native_hidden_time_ratios h a hs

theorem Prepared.native_base_position_bound (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) (l : α) (hl : l ∈ cfg.A k s i)
    {t : ℝ} (ht : t ∈ I (cfg.T k s) (cfg.j k s i)) :
    |(cfg.x k l t) 1| ≤ 3 * cfg.K k :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.Prepared.native_base_position_bound h a i l hl ht

theorem Prepared.native_affine_table (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (hs : 0 ≤ s)
    (hμ : ∀ i, ENNReal.ofReal (cfg.timeLength k s / cfg.K k) * cfg.ν k (cfg.A k s i) ≤
      cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i))) :
    ∃ L : Fin (cfg.n k s) → Fin 4 → ℝ,
      (∀ i, ∀ e : Fin 3, |L i e.succ| ≤ 36 * cfg.K k ^ 4) ∧
      ∀ i, cfg.F k s i = X (3 : Fin 4) -
        (C (L i 0) + C (L i 1) * X (0 : Fin 4) + C (L i 2) * X (1 : Fin 4) +
          C (L i 3) * X (2 : Fin 4)) ∧
        ∀ l ∈ cfg.B k s i, ∀ t ∈ I (cfg.T k s) (cfg.j k s i),
          |cfg.b k l 2 + t * cfg.b k l 5 - (L i 0 + L i 1 * t +
            L i 2 * (cfg.b k l 0 + t * cfg.b k l 3) +
            L i 3 * (cfg.b k l 1 + t * cfg.b k l 4))| ≤ cfg.K k * cfg.N k ^ (-s) :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.Prepared.native_affine_table h a hs hμ

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing.Data
