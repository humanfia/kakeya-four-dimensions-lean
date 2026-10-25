import Submission.Obl.k4_critical_affine_derivative_preparation.Model
import Submission.Obl.k4_affine_skew_row_fit.Interfaces

namespace Submission.Obl.k4_critical_affine_derivative_preparation

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open Submission.Obl.k4_affine_skew_row_fit

/-- Increasing the input loss preserves all original functions, measures,
palette bins and row lists. -/
def enlargeIncidenceLoss {α : Type} [MeasurableSpace α] {S a η η' N : ℝ}
    (d : IncidenceData S a η N α) (hN : 1 ≤ N) (hη : η ≤ η') :
    IncidenceData S a η' N α := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hpow : N ^ η ≤ N ^ η' := Real.rpow_le_rpow_of_exponent_le hN hη
  have hneg : N ^ (-η') ≤ N ^ (-η) := Real.rpow_le_rpow_of_exponent_le hN (neg_le_neg hη)
  have hE : 0 ≤ d.error := (Real.rpow_pos_of_pos hNpos (-a)).le.trans d.error_lower
  exact {
    prior := d.prior
    active := d.active
    intercept := d.intercept
    velocity := d.velocity
    evaluation := d.evaluation
    row := d.row
    palette := d.palette
    error := d.error
    bins := d.bins
    measurable_intercept := d.measurable_intercept
    measurable_velocity := d.measurable_velocity
    measurable_evaluation := d.measurable_evaluation
    measurable_row := d.measurable_row
    prior_probability := d.prior_probability
    palette_probability := d.palette_probability
    error_lower := d.error_lower
    error_upper := d.error_upper
    trajectory_bound := fun l => (d.trajectory_bound l).trans hpow
    domination := d.domination.trans (by
      intro s
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hpow) zero_le)
    time_support := d.time_support
    mass_lower := (ENNReal.ofReal_le_ofReal hneg).trans d.mass_lower
    palette_cap := fun x r hr hr1 => (d.palette_cap x r hr hr1).trans
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg ((Real.rpow_pos_of_pos hNpos (-a)).le.trans hr) _)))
    joint_cap := fun q j => (d.joint_cap q j).trans
      (mul_le_mul_of_nonneg_right
        (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hpow (sq_nonneg _))) zero_le)
    bins_card := fun q => (d.bins_card q).trans hpow
    row_constraint := d.row_constraint.mono (fun p hp =>
      ⟨fun j => (hp.1 j).trans hpow, hp.2.1,
        hp.2.2.trans (mul_le_mul_of_nonneg_right hpow hE)⟩)
  }

end

end Submission.Obl.k4_critical_affine_derivative_preparation
