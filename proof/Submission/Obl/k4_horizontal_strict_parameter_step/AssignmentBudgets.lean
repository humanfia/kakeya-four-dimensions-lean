/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/AssignmentBudgets.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.NativeAssignments
import Submission.Obl.k4_quadratic_atlas_normalization.AssignmentMass

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set

noncomputable section

/-- Full assignments at one dyadic time depth have total prior-times-duration
at most one. This budget uses the original prior, regardless of any later success set. -/
theorem assignment_prior_time_budget {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] {T n : ℕ}
    (j : Fin n → Fin (2 ^ T)) (A : Fin n → Set α)
    (hA : ∀ i, MeasurableSet (A i))
    (hd : ∀ i i', i ≠ i' → j i = j i' → Disjoint (A i) (A i')) :
    ∑ i, ((2 : ℝ) ^ T)⁻¹ * ν.real (A i) ≤ 1 := by
  have hgroup : (∑ i, ν (A i)) ≤ (2 ^ T : ENNReal) := by
    simpa using Submission.Obl.k4_quadratic_atlas_normalization.weighted_assignment_budget
      (fun _ : Unit => ν) (fun _ : Unit => (1 : ENNReal)) (fun _ : Fin n => ()) j A
      (fun _ => measure_univ) (by simp) hA (fun i i' hne _ hji => hd i i' hne hji)
  have hbound : ∑ i, ν.real (A i) ≤ (2 : ℝ) ^ T := by
    have hh := ENNReal.toReal_mono (by finiteness : (2 ^ T : ENNReal) ≠ ⊤) hgroup
    simpa only [ENNReal.toReal_sum (fun i _ => measure_ne_top ν (A i)),
      ENNReal.toReal_pow, ENNReal.toReal_ofNat, ← measureReal_def] using hh
  rw [← Finset.mul_sum]
  calc
    _ ≤ ((2 : ℝ) ^ T)⁻¹ * (2 : ℝ) ^ T :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = 1 := inv_mul_cancel₀ (by positivity)

namespace NativeModel

open Submission.Obl.k4_critical_derivative_evaluation_lists

/-- The native cell/domain threshold weights sum to a subpower budget.
The squared transverse scale survives because the earlier assignment floors are cubic. -/
theorem reference_budget {α : Type} [MeasurableSpace α] (cfg : NativeModel α)
    {k : ℕ} {s : ℝ} (a : cfg.AssignmentLevel k s)
    (hν : IsProbabilityMeasure (cfg.ν k)) (hN : 0 < cfg.N k)
    (hK : 0 < cfg.K k) (hℓ : cfg.ℓ = cfg.κ) :
    (cfg.n k s : ℝ) * cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d ≤ cfg.K k ^ 2 := by
  letI := hν
  have hq : 0 < cfg.timeLength k s := by unfold Data.timeLength; positivity
  have hbudget : ∑ i, cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i) ≤ 1 :=
    assignment_prior_time_budget (cfg.ν k) (cfg.j k s) (cfg.A k s) a.measurable a.disjoint
  have hfloor (i : Fin (cfg.n k s)) :
      cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d ≤
        cfg.K k ^ 2 * (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i)) := by
    have hlo := (cfg.prior_bounds a hν hN hK hℓ i).1
    have hm := (div_le_iff₀ (sq_pos_of_pos hK)).mp hlo
    have hh := mul_le_mul_of_nonneg_left hm hq.le
    convert hh using 1 <;> ring
  calc
    _ = ∑ _i : Fin (cfg.n k s), cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d := by simp; ring
    _ ≤ ∑ i : Fin (cfg.n k s), cfg.K k ^ 2 *
        (cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i)) := Finset.sum_le_sum (fun i _ => hfloor i)
    _ = cfg.K k ^ 2 * ∑ i, cfg.timeLength k s * (cfg.ν k).real (cfg.A k s i) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ cfg.K k ^ 2 * 1 := mul_le_mul_of_nonneg_left hbudget (sq_nonneg _)
    _ = _ := mul_one _

end NativeModel

end

end Submission.Obl.k4_horizontal_strict_parameter_step
