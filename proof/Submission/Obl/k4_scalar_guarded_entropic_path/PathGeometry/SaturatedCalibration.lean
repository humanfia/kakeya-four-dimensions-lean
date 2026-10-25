/-
Adapted from this LOT tree, obligation o093, session x0544, branch x0544,
Submission/Obl/k4_scalar_critical_path_terminal/SaturatedCalibration.lean.
Its original attribution comments are retained below.
-/
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.ProfileZero
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.RefinementSubfamilies
import Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry.IntermediateCalibration

/-! Full-prior saturation from a true supplied atlas calibrates every
intermediate child depth. The absolute zero-depth sign removes any fixed
positive profile loss. -/

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_scalar_linear_critical_extremizers.Split

namespace RefinementWitness

variable {p q : Code} {r b h : ℝ} (w : RefinementWitness p q r b h)

/-- Exact relative-profile transport and the original absolute sign give
the intermediate profile inequality without an additional constant. -/
theorem intermediate_profile_le (hq : Exact q) {s : ℝ}
    (hrelative : f q s - f q 0 = f p (r + s) - f p r) :
    f q s - f p (r + s) ≤ -f p r := by
  linarith [exact_profile_zero_le hq]

/-- Saturation belongs to the full original assignment, even when later
incidence masks have shrunk. It supplies the precise intermediate floor. -/
theorem intermediate_floor_of_saturation (hp : Exact p) (hq : Exact q)
    (σ : ℕ → ℝ) (hsat : w.toRefinementData.Saturated r σ)
    {s δ : ℝ} (hrelative : f q s - f q 0 = f p (r + s) - f p r)
    (k : ℕ) (hσ : σ k ≤ δ) (i : Fin (W q k)) :
    ENNReal.ofReal (N q k ^ (f q s - f p (r + s) - δ) * w.width k i) ≤
      ν p (w.sample k) (w.world k i) (w.assignment k i) := by
  apply le_trans _ (hsat k i)
  apply ENNReal.ofReal_le_ofReal
  rw [(w.charts k).1]
  apply mul_le_mul_of_nonneg_right _ (w.width_pos k i).le
  exact Real.rpow_le_rpow_of_exponent_le
    ((show (1 : ℝ) ≤ 2 by norm_num).trans (hp.1.1 (w.sample k)))
    (by linarith [intermediate_profile_le hq hrelative])

/-- The real-valued calibration used by the original true-chart lifting
formula has exactly the full original assignment mass. -/
theorem intermediate_calibration_real (hp : Exact p) (hq : Exact q)
    (σ : ℕ → ℝ) (hsat : w.toRefinementData.Saturated r σ)
    {s δ : ℝ} (hrelative : f q s - f q 0 = f p (r + s) - f p r)
    (k : ℕ) (hσ : σ k ≤ δ) (i : Fin (W q k)) :
    N p (w.sample k) ^ (-f p (r + s)) * w.width k i ≤
      N p (w.sample k) ^ δ *
        (ν p (w.sample k) (w.world k i) (w.assignment k i)).toReal * N q k ^ (-f q s) := by
  have hN : 0 < N p (w.sample k) := by linarith [hp.1.1 (w.sample k)]
  have hfloor := ENNReal.toReal_mono (w.assignment_mass_ne_top hp k i)
    (w.intermediate_floor_of_saturation hp hq σ hsat hrelative k hσ i)
  rw [ENNReal.toReal_ofReal (mul_nonneg
    (Real.rpow_nonneg (by linarith [hq.1.1 k]) _) (w.width_pos k i).le),
    (w.charts k).1] at hfloor
  rw [(w.charts k).1]
  calc
    _ = N p (w.sample k) ^ δ *
        (N p (w.sample k) ^ (f q s - f p (r + s) - δ) * w.width k i) *
          N p (w.sample k) ^ (-f q s) := by
      have hpower : N p (w.sample k) ^ δ *
          N p (w.sample k) ^ (f q s - f p (r + s) - δ) *
            N p (w.sample k) ^ (-f q s) = N p (w.sample k) ^ (-f p (r + s)) := by
        rw [← Real.rpow_add hN, ← Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = (N p (w.sample k) ^ δ *
            N p (w.sample k) ^ (f q s - f p (r + s) - δ) *
              N p (w.sample k) ^ (-f q s)) * w.width k i := by rw [hpower]
        _ = _ := by ring
    _ ≤ _ := by gcongr

/-- A saturated true-parent refinement has no under-calibrated world once
its vanishing inherited saturation loss is below the declared tolerance. -/
theorem intermediateBadMass_eq_zero_of_saturation (hp : Exact p) (hq : Exact q)
    (σ : ℕ → ℝ) (hsat : w.toRefinementData.Saturated r σ)
    {s δ : ℝ} (hrelative : f q s - f q 0 = f p (r + s) - f p r)
    (k : ℕ) (hσ : σ k ≤ δ) : w.intermediateBadMass s δ k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro i _
  exact ite_eq_right (not_lt.mpr (w.intermediate_floor_of_saturation hp hq σ hsat
    hrelative k hσ i))

theorem eventually_intermediateBadMass_eq_zero (hp : Exact p) (hq : Exact q)
    (σ : ℕ → ℝ) (hsat : w.toRefinementData.Saturated r σ)
    (hσ : Tendsto σ atTop (nhds 0)) {s δ : ℝ} (hδ : 0 < δ)
    (hrelative : f q s - f q 0 = f p (r + s) - f p r) :
    ∀ᶠ k in atTop, w.intermediateBadMass s δ k = 0 := by
  filter_upwards [hσ.eventually (gt_mem_nhds hδ)] with k hk
  exact w.intermediateBadMass_eq_zero_of_saturation hp hq σ hsat hrelative k hk.le

end RefinementWitness

end Submission.Obl.k4_scalar_guarded_entropic_path.PathGeometry
