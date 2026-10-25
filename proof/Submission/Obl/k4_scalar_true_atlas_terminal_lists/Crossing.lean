import Submission.Obl.k4_scalar_true_atlas_terminal_lists.Defs
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.MassBounds
import Submission.Obl.k4_scalar_terminal_chart_packet_extraction.TrueSystem

/-! Observation crossings and their reference-volume budgets. -/

namespace Submission.Obl.k4_scalar_true_atlas_terminal_lists

open MeasureTheory Set
open scoped ENNReal BigOperators
open Submission.Obl.k4_scalar_terminal_chart_packet_extraction
  (chartPar measurableSet_chartPar volume_chartPar_le volume_fin2_eq
   prod_count_box_le floor_near_of_fit)

/-- Compatibility of an observation with a chart. It uses only its observed
base point and hidden bin, and does not inspect the underlying trajectory. -/
def crossing (a Λ s q u v J : ℝ) (P : MvPolynomial (Fin 2) ℝ) : Set Observation :=
  {z | (z.1 0, z.1 1) ∈ chartPar s q u v (Λ * J) ∧
    |(z.2 : ℝ) - MvPolynomial.eval z.1 P / a| ≤ Λ + 1}

theorem crossing_measurable (a Λ s q u v J : ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    MeasurableSet (crossing a Λ s q u v J P) := by
  apply MeasurableSet.inter
  · exact (measurableSet_chartPar s q u v (Λ * J)).preimage (by fun_prop)
  · exact measurableSet_le
      ((((measurable_from_top (f := fun k : ℤ => (k : ℝ))).comp measurable_snd).sub
        (((MvPolynomial.continuous_eval P).measurable.comp measurable_fst).div_const a)).abs)
      measurable_const

/-- A crossing occupies only O(Λ) hidden bins over a base parallelogram. -/
theorem crossing_volume_le (a Λ s q u v J : ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (hΛ : 0 ≤ Λ) (hJ : 0 ≤ J) :
    (volume.prod Measure.count) (crossing a Λ s q u v J P) ≤
      ENNReal.ofReal ((2 * Λ + 3) * (q * (2 * (Λ * J)))) := by
  let X' : Set (Fin 2 → ℝ) := {z | (z 0, z 1) ∈ chartPar s q u v (Λ * J)}
  have hX : MeasurableSet X' := (measurableSet_chartPar s q u v (Λ * J)).preimage (by fun_prop)
  have h := prod_count_box_le hX ((MvPolynomial.continuous_eval P).measurable.div_const a)
    (by linarith : 0 ≤ Λ + 1)
  change (volume.prod Measure.count) (crossing a Λ s q u v J P) ≤
    ENNReal.ofReal (2 * (Λ + 1) + 1) * volume X' at h
  calc
    _ ≤ ENNReal.ofReal (2 * (Λ + 1) + 1) * volume X' := h
    _ ≤ ENNReal.ofReal (2 * (Λ + 1) + 1) * ENNReal.ofReal (q * (2 * (Λ * J))) := by
      gcongr
      rw [show volume X' = volume (chartPar s q u v (Λ * J)) from
        volume_fin2_eq (measurableSet_chartPar s q u v (Λ * J))]
      exact volume_chartPar_le s q u v (Λ * J) (mul_nonneg hΛ hJ)
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      ring

/-- Every selected incidence of a geometrically fitting chart crosses that
chart at the frozen depth observation. -/
theorem fitting_incidence_crosses (p : Data) (k T : ℕ) (r Λ : ℝ)
    (j : Fin (2 ^ T)) (u v J : ℝ) (P : MvPolynomial (Fin 2) ℝ)
    (l : Trajectory) (t : ℝ) (hN : 0 < N p k) (ht : t ∈ I T j)
    (hy : |y l t - u - t * v| ≤ Λ * J)
    (hx : |x l t - MvPolynomial.eval ![t, y l t] P| ≤ Λ * N p k ^ (-r)) :
    ((![t, y l t], ⌊x l t / (N p k ^ (-r))⌋) : Observation) ∈
      crossing (N p k ^ (-r)) Λ ((j : ℕ) / (2 : ℝ) ^ T)
        (1 / (2 : ℝ) ^ T) u v J P := by
  constructor
  · constructor
    · simpa only [I, add_div, Matrix.cons_val_zero] using ht
    · simpa only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        sub_sub, mul_comm v t] using hy
  · exact floor_near_of_fit (Real.rpow_pos_of_pos hN _) hx

end Submission.Obl.k4_scalar_true_atlas_terminal_lists
