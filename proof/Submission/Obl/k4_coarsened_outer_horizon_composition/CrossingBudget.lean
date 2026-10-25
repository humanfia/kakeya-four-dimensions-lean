import Submission.Obl.k4_coarsened_outer_horizon_composition.Crossings

namespace Submission.Obl.k4_coarsened_outer_horizon_composition

open MeasureTheory Set
open scoped ENNReal

/-- The true floor pays for the observation volume after imposing a typical
pure-density ceiling. The loss is only a fixed power of the chart slack. -/
theorem crossing_volume_floor_budget {N κ f τ J : ℝ} {T : ℕ} {m v : ℝ≥0∞}
    (hN : 0 < N) (hκ : 0 < κ) (hJ : 0 ≤ J)
    (hfloor : ENNReal.ofReal (N ^ (-f) * J / ((2 : ℝ) ^ T * κ)) ≤ m)
    (hvol : v ≤ ENNReal.ofReal (256 * κ ^ 4 / (2 : ℝ) ^ T * J)) :
    ENNReal.ofReal (N ^ (-f + τ)) * v ≤ ENNReal.ofReal (256 * κ ^ 5 * N ^ τ) * m := by
  calc
    _ ≤ ENNReal.ofReal (N ^ (-f + τ)) *
        ENNReal.ofReal (256 * κ ^ 4 / (2 : ℝ) ^ T * J) :=
      mul_le_mul (le_refl _) hvol zero_le zero_le
    _ = ENNReal.ofReal (256 * κ ^ 5 * N ^ τ) *
        ENNReal.ofReal (N ^ (-f) * J / ((2 : ℝ) ^ T * κ)) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ N ^ (-f + τ)),
        ← ENNReal.ofReal_mul (by positivity : 0 ≤ 256 * κ ^ 5 * N ^ τ), Real.rpow_add hN]
      congr 1
      field_simp
    _ ≤ _ := mul_le_mul (le_refl _) hfloor zero_le zero_le

/-- Specialize the crossing-volume budget to the exact chart predicate used
by the frozen terminal-system assertion. -/
theorem chart_crossing_budget {N κ j r B f τ : ℝ} {M D T : ℕ}
    (hN : 0 < N) (hκ : 1 ≤ κ) (hB : 0 < B)
    (ν : Measure Line) (E : Set Inc) (c u : E2) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (R : MvPolynomial (Fin 4) ℝ) (A : Set Line) (F : Set Inc)
    (hc : chart N M D κ T j r B E c u Q R A F
      (ENNReal.ofReal (N ^ (-f) * |Q.det| / ((2 : ℝ) ^ T * κ)) ≤ (ν.prod volume) F)) :
    ENNReal.ofReal (N ^ (-f + τ)) * (volume.prod Measure.count)
      (crossing κ (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) (δ N r / B) B c u Q R) ≤
      ENNReal.ofReal (256 * κ ^ 5 * N ^ τ) * (ν.prod volume) F := by
  rcases hc with ⟨hdet, hcu, hframe, hsize, hR, hcoeff, hA, hF, hfmt, hwhole, hsel, hfloor⟩
  have hκ0 : 0 < κ := by linarith
  have hδ : 0 < δ N r := by unfold δ; positivity
  have ht : j / (2 : ℝ) ^ T ≤ (j + 1) / (2 : ℝ) ^ T :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hvol := reference_crossing hκ ht (div_pos hδ hB) hB c u Q hdet R hR
  apply crossing_volume_floor_budget hN hκ0 (abs_nonneg _) hfloor
  apply hvol.trans_eq
  congr 1
  field_simp
  ring

end Submission.Obl.k4_coarsened_outer_horizon_composition
