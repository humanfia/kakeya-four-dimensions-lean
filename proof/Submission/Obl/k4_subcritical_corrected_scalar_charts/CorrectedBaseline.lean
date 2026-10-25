/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/CorrectedBaseline.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.ChartInterface

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set

noncomputable section

/-- Rewrite the time primitive from chart coordinates in the original parameters. -/
def unscaledFiberCorrection (β : Fin 3 → ℝ) (A D pc qc : ℝ) : Fin 6 → ℝ :=
  ![-(A / D) * β 0 * pc, -(A / D) * (β 1 * pc + β 2 * qc / 2),
    (A / D) * β 0, (A / D) * β 1, 0, (A / D) * (β 2 / 2)]

def correctedBaseline (H : Fin 6 → ℝ) (β : Fin 3 → ℝ) (A D pc qc : ℝ) :
    Fin 6 → ℝ := H + unscaledFiberCorrection β A D pc qc

theorem parameterPredictor_add (H H' : Fin 6 → ℝ) (t p q : ℝ) :
    parameterPredictor (H + H') t p q =
      parameterPredictor H t p q + parameterPredictor H' t p q := by
  simp only [parameterPredictor, Submission.Lib.K4FullTimeLayers.parameterPredictor,
    Pi.add_apply]
  ring

theorem unscaledFiberCorrection_eval (β : Fin 3 → ℝ) (A D pc qc t p q : ℝ) :
    parameterPredictor (unscaledFiberCorrection β A D pc qc) t p q =
      A * parameterPredictor (fiberCorrection β) t ((p - pc) / D) ((q - qc) / D) := by
  dsimp [unscaledFiberCorrection, fiberCorrection, parameterPredictor,
    Submission.Lib.K4FullTimeLayers.parameterPredictor]
  ring

theorem correctedBaseline_signal {A : ℝ} (hA : A ≠ 0)
    (H : Fin 6 → ℝ) (β : Fin 3 → ℝ) (D pc qc : ℝ) (b : Fin 6 → ℝ) (t : ℝ) :
    chartSignal A (correctedBaseline H β A D pc qc) b t =
      chartSignal A H b t -
        parameterPredictor (fiberCorrection β) t ((b 0 - pc) / D) ((b 1 - qc) / D) := by
  unfold chartSignal correctedBaseline
  rw [parameterPredictor_add, unscaledFiberCorrection_eval]
  field_simp
  <;> ring

theorem normalized_parameter_mem_unit {x D : ℝ} {z : ℤ} (hD : 0 < D)
    (hz : ⌊x / D⌋ = z) : (x - (z : ℝ) * D) / D ∈ Icc (0 : ℝ) 1 := by
  have hlo : (z : ℝ) ≤ x / D := by simpa only [hz] using Int.floor_le (x / D)
  have hhi : x / D < (z : ℝ) + 1 := by simpa only [hz] using Int.lt_floor_add_one (x / D)
  rw [sub_div, mul_div_cancel_right₀ _ hD.ne']
  constructor <;> linarith

theorem fiberCorrection_eval_bound {β : Fin 3 → ℝ} {B t p q : ℝ}
    (hβ : ∀ e, |β e| ≤ B) (ht : t ∈ Icc (0 : ℝ) 1)
    (hp : p ∈ Icc (0 : ℝ) 1) (hq : q ∈ Icc (0 : ℝ) 1) :
    |parameterPredictor (fiberCorrection β) t p q| ≤ 3 * B := by
  have hB : 0 ≤ B := (abs_nonneg _).trans (hβ 0)
  have ht' : |t| ≤ 1 := by simpa only [abs_of_nonneg ht.1] using ht.2
  have hp' : |p| ≤ 1 := by simpa only [abs_of_nonneg hp.1] using hp.2
  have hq' : |q| ≤ 1 := by simpa only [abs_of_nonneg hq.1] using hq.2
  have h1 : |β 1 * t| ≤ B := by
    rw [abs_mul]
    exact (mul_le_mul (hβ 1) ht' (abs_nonneg _) hB).trans_eq (mul_one _)
  have h2 : |β 2 / 2 * t| ≤ B / 2 := by
    rw [abs_mul, abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    exact (mul_le_mul (div_le_div_of_nonneg_right (hβ 2) (by norm_num)) ht'
      (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have h3 : |(β 0 + β 1 * t) * p| ≤ 2 * B := by
    rw [abs_mul]
    exact (mul_le_mul ((abs_add_le _ _).trans (by linarith [hβ 0])) hp'
      (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  have h4 : |(β 2 / 2 * t) * q| ≤ B / 2 := by
    rw [abs_mul]
    exact (mul_le_mul h2 hq' (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
  change |0 + 0 * t + (β 0 + β 1 * t) * p + (0 + β 2 / 2 * t) * q| ≤ _
  simp only [zero_mul, zero_add]
  exact (abs_add_le _ _).trans (by linarith)

theorem correctedBaseline_box_bound {H : Fin 6 → ℝ} {β : Fin 3 → ℝ}
    {A D pc qc E B : ℝ} (hA : 0 ≤ A) (hD : 0 < D)
    (hβ : ∀ e, |β e| ≤ B)
    (hH : ∀ t ∈ Icc (0 : ℝ) 1, ∀ p ∈ Icc pc (pc + D),
      ∀ q ∈ Icc qc (qc + D), |parameterPredictor H t p q| ≤ E)
    {t p q : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hp : p ∈ Icc pc (pc + D)) (hq : q ∈ Icc qc (qc + D)) :
    |parameterPredictor (correctedBaseline H β A D pc qc) t p q| ≤ E + 3 * A * B := by
  have hp' : (p - pc) / D ∈ Icc (0 : ℝ) 1 := by
    exact ⟨div_nonneg (sub_nonneg.mpr hp.1) hD.le,
      (div_le_one hD).mpr (by linarith [hp.2])⟩
  have hq' : (q - qc) / D ∈ Icc (0 : ℝ) 1 := by
    exact ⟨div_nonneg (sub_nonneg.mpr hq.1) hD.le,
      (div_le_one hD).mpr (by linarith [hq.2])⟩
  unfold correctedBaseline
  rw [parameterPredictor_add, unscaledFiberCorrection_eval]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg hA]
  have := mul_le_mul_of_nonneg_left (fiberCorrection_eval_bound hβ ht hp' hq') hA
  linarith [hH t ht p hp q hq]

theorem correctedBaseline_fit_bound {H : Fin 6 → ℝ} {β : Fin 3 → ℝ}
    {A D E B : ℝ} {P Q : ℤ} (hA : A ≠ 0) (hD : 0 < D)
    (hβ : ∀ e, |β e| ≤ B) {b : Fin 6 → ℝ} {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) (hP : ⌊b 0 / D⌋ = P) (hQ : ⌊b 1 / D⌋ = Q)
    (hfit : |chartSignal A H b t| ≤ E) :
    |chartSignal A (correctedBaseline H β A D ((P : ℝ) * D) ((Q : ℝ) * D)) b t| ≤
      E + 3 * B := by
  rw [correctedBaseline_signal hA]
  exact (abs_sub _ _).trans (add_le_add hfit
    (fiberCorrection_eval_bound hβ ht (normalized_parameter_mem_unit hD hP)
      (normalized_parameter_mem_unit hD hQ)))

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
