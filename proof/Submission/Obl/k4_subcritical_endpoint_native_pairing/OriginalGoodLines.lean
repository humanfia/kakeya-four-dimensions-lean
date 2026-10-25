import Submission.Obl.k4_subcritical_endpoint_native_pairing.NativeLevel
import Submission.Obl.k4_subcritical_corrected_scalar_charts.OriginalGoodLines

/-! Original good-line facts are imported from accepted o263. The additional
weakening below keeps the original coefficient ceiling and changes only the defect. -/

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing

open Set MeasureTheory Filter

noncomputable section

abbrev goodOriginalLines :=
  @Submission.Obl.k4_subcritical_corrected_scalar_charts.goodOriginalLines

abbrev measurableSet_goodOriginalLines :=
  @Submission.Obl.k4_subcritical_corrected_scalar_charts.measurableSet_goodOriginalLines

namespace Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem NativeLevel.original_good_ae (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.NativeLevel k s) :
    ∀ᵐ p ∂cfg.μ k, (∀ e, |cfg.b k p.1 e| ≤ 2 * cfg.K k) ∧
      |cfg.b k p.1 4 + cfg.b k p.1 0| ≤ cfg.N k ^ (-cfg.e₀) :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.NativeLevel.original_good_ae h a

/-- Weakening the velocity defect preserves the conull bounded original-line
set without any new asymptotic coefficient loss. -/
theorem NativeLevel.original_good_lines_ae (h : cfg.Prepared) {k : ℕ} {s M : ℝ}
    (a : cfg.NativeLevel k s) (hMe : M ≤ cfg.e₀) :
    ∀ᵐ p ∂cfg.μ k,
      p.1 ∈ goodOriginalLines (cfg.b k) (2 * cfg.K k) (cfg.N k ^ (-M)) := by
  have hN : 1 ≤ cfg.N k := by linarith [h.scale k]
  filter_upwards [a.original_good_ae h] with p hp
  exact ⟨hp.1, hp.2.trans (Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hMe))⟩

theorem Prepared.eventually_good_original_lines (h : cfg.Prepared) {s M ε : ℝ}
    (hM : M ≤ cfg.e₀) (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∀ a : cfg.NativeLevel k s,
      ∀ᵐ p ∂cfg.μ k, p.1 ∈ goodOriginalLines (cfg.b k) (cfg.N k ^ ε) (cfg.N k ^ (-M)) :=
  Submission.Obl.k4_subcritical_corrected_scalar_charts.Data.Prepared.eventually_good_original_lines h hM hε

end Data

abbrev original_good_line_cut_mass :=
  @Submission.Obl.k4_subcritical_corrected_scalar_charts.original_good_line_cut_mass

end

end Submission.Obl.k4_subcritical_endpoint_native_pairing
