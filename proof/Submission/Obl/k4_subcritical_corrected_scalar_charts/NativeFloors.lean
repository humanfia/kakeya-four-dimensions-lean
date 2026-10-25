/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeFloors.lean`. Original attributions are retained below. -/
import Submission.Obl.k4_subcritical_corrected_scalar_charts.NativeData
import Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.Mass

/-! Original horizontal floors and budgets. The critical-name prior estimate
of accepted o212 uses only the time comparison and the horizontal rate equality;
it applies at every horizontal rate, as recorded below. -/

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory Filter
open scoped ENNReal
open Submission.Obl.k4_critical_intercept_concentration

noncomputable section

namespace Data

open Submission.Obl.k4_critical_intercept_concentration.Data

variable {α : Type} [MeasurableSpace α] {cfg : Data α}

theorem Prepared.native_prior_bounds (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) (i : Fin (cfg.n k s)) :
    cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2 ≤
        (cfg.ν k).real (cfg.A k s i) ∧
      (cfg.ν k).real (cfg.A k s i) ≤
        cfg.K k ^ 2 * cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hN : 0 < cfg.N k := by linarith [h.scale k]
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hlow := ENNReal.toReal_mono (measure_ne_top (cfg.ν k) _) (a.prior_lower i)
  have hupp := ENNReal.toReal_mono ENNReal.ofReal_ne_top (a.prior_upper i)
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤
    (cfg.N k ^ (-s)) ^ cfg.d * cfg.timeLength k s ^ 2 * cfg.N k ^ (-cfg.ℓ * s) / cfg.K k),
    ← measureReal_def] at hlow
  simp only [ENNReal.toReal_ofReal (by positivity : 0 ≤
    cfg.K k * (cfg.N k ^ (-s)) ^ cfg.d * cfg.timeLength k s ^ 2 *
      cfg.N k ^ (-cfg.ℓ * s)), ← measureReal_def] at hupp
  rw [h.horizontal_rate] at hlow hupp
  exact assignment_bounds_from_time_comparison hN hK a.time_lower a.time_upper hlow hupp


theorem Prepared.native_witness_lower (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s)
    (hμ : ∀ i, ENNReal.ofReal (cfg.timeLength k s / cfg.K k) * cfg.ν k (cfg.A k s i) ≤
      cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)))
    (i : Fin (cfg.n k s)) :
    ENNReal.ofReal (cfg.timeLength k s ^ 4 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 3) ≤
      cfg.μ k (cfg.B k s i ×ˢ I (cfg.T k s) (cfg.j k s i)) := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  have hK : 0 < cfg.K k := by linarith [h.subpower.1 k]
  have hq : 0 < cfg.timeLength k s := by unfold timeLength; positivity
  have hprior : ENNReal.ofReal
      (cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2) ≤
      cfg.ν k (cfg.A k s i) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top (cfg.ν k) (cfg.A k s i))]
    exact ENNReal.ofReal_le_ofReal (h.native_prior_bounds a i).1
  calc
    _ = ENNReal.ofReal (cfg.timeLength k s / cfg.K k) *
        ENNReal.ofReal (cfg.timeLength k s ^ 3 * (cfg.N k ^ (-s)) ^ cfg.d / cfg.K k ^ 2) := by
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ cfg.timeLength k s / cfg.K k)]
      congr 1
      field_simp
    _ ≤ ENNReal.ofReal (cfg.timeLength k s / cfg.K k) * cfg.ν k (cfg.A k s i) :=
      mul_le_mul' le_rfl hprior
    _ ≤ _ := hμ i

/-- Every original full native assignment is charged only to its time block. -/
theorem Prepared.native_assignment_budget (h : cfg.Prepared) {k : ℕ} {s : ℝ}
    (a : cfg.AssignmentLevel k s) :
    (∑ i, ENNReal.ofReal (cfg.timeLength k s) * cfg.ν k (cfg.A k s i)) ≤ 1 := by
  let : IsProbabilityMeasure (cfg.ν k) := (h.basic k).2.1
  simpa only [timeLength, ENNReal.ofReal_inv_of_pos (by positivity : (0 : ℝ) < 2 ^ cfg.T k s),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] using
    Submission.Obl.k4_horizontal_supercritical_three_projections.Parent.sum_full_label_weights_le_one
      (cfg.ν k) (cfg.T k s) (cfg.j k s) (cfg.A k s) a.measurable a.disjoint

end Data

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
