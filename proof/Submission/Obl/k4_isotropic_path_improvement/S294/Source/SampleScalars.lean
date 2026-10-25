-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.SampleScalars, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The per-sample scalars: positivity, order and the row bound (session x1088).

* `sample_scalars_pos`: `0 < θ, ε, pv` and `ε ≤ θ`, `pv ≤ θ` for the skeleton's
  `θ = thetaOf …`, `ε = epsOf …`, `pv = pvOf …` (`K ≥ 1`, `ζ ≤ 1`).
* `row_bound_le_K`: `28 Kg^6 ≤ K = N^kexp` once `Kg ≤ N^(kexp/7)` and `28 ≤ N^(kexp/7)`. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.Stages

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

noncomputable section

/-- **The per-sample scalars are positive and ordered.** -/
theorem sample_scalars_pos {Ep : ℕ} {precision loss gain N L rA rB : ℝ} {TA TB : ℕ}
    (hN : 1 < N) (hkexp : 0 ≤ loss * gain * L / ((Ep : ℝ) + 1))
    (hpgl : 0 ≤ precision * gain * L) :
    0 < thetaOf Ep precision loss gain N L rA rB TA TB ∧
      0 < epsOf Ep precision loss gain N L rA rB TA TB ∧
      0 < pvOf Ep precision loss gain N L rA rB TA TB ∧
      epsOf Ep precision loss gain N L rA rB TA TB ≤ thetaOf Ep precision loss gain N L rA rB TA TB ∧
      pvOf Ep precision loss gain N L rA rB TA TB ≤ thetaOf Ep precision loss gain N L rA rB TA TB := by
  have hNp : 0 < N := by linarith
  have hK1 : 1 ≤ KOf Ep loss gain N L := Real.one_le_rpow hN.le hkexp
  have hK0 : 0 < KOf Ep loss gain N L := by linarith
  have hζ0 : 0 < zetaOf precision gain N L := O204.Tangent.δ_pos _ _
  have hζ1 : zetaOf precision gain N L ≤ 1 := O204.Tangent.δ_le_one _ _ hN.le hpgl
  have ha0 : 0 < aRelOf N rA rB := div_pos (O204.Tangent.δ_pos _ _) (O204.Tangent.δ_pos _ _)
  have hh0 : 0 < hRelOf TA TB := by unfold hRelOf; positivity
  have hθ : 0 < thetaOf Ep precision loss gain N L rA rB TA TB := by
    unfold thetaOf; positivity
  have hKp : 1 ≤ KOf Ep loss gain N L ^ (Ep + 2) := one_le_pow₀ hK1
  refine ⟨hθ, by unfold epsOf; positivity, by unfold pvOf; positivity, ?_, ?_⟩
  · unfold epsOf
    rw [div_le_iff₀ (by positivity)]
    calc thetaOf Ep precision loss gain N L rA rB TA TB * zetaOf precision gain N L
        ≤ thetaOf Ep precision loss gain N L rA rB TA TB * 1 := by gcongr
      _ ≤ thetaOf Ep precision loss gain N L rA rB TA TB * KOf Ep loss gain N L ^ (Ep + 2) := by
          gcongr
  · unfold pvOf
    rw [div_le_iff₀ (by positivity)]
    calc thetaOf Ep precision loss gain N L rA rB TA TB
        = thetaOf Ep precision loss gain N L rA rB TA TB * 1 := by ring
      _ ≤ thetaOf Ep precision loss gain N L rA rB TA TB * KOf Ep loss gain N L ^ (Ep + 2) := by
          gcongr

/-- **The row bound**: `28 Kg^6 ≤ N^kexp` when `Kg ≤ N^(kexp/7)` and `28 ≤ N^(kexp/7)`. -/
theorem row_bound_le_K {N kexp Kg : ℝ} (hN : 1 < N) (hKg0 : 0 ≤ Kg)
    (hKg : Kg ≤ N ^ (kexp / 7)) (h28 : 28 ≤ N ^ (kexp / 7)) : 28 * Kg ^ 6 ≤ N ^ kexp := by
  have hNp : 0 < N := by linarith
  have h7 : N ^ kexp = (N ^ (kexp / 7)) ^ 7 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; congr 1; push_cast; ring
  rw [h7]
  have hY0 : 0 ≤ N ^ (kexp / 7) := by positivity
  calc 28 * Kg ^ 6 ≤ N ^ (kexp / 7) * (N ^ (kexp / 7)) ^ 6 := by gcongr
    _ = (N ^ (kexp / 7)) ^ 7 := by ring

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
