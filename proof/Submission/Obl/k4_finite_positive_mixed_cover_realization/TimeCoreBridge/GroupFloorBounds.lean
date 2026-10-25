-- Adapted from this LOT tree, o210, session x0719, commit be8f7224,
-- Submission/Obl/k4_clean_cover_graph_atlas/GroupFloorBounds.lean. Earlier provenance is retained below.
-- The shared path interface drops only its unused zero-narrowness estimate.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.SampleScales
import Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge.ProjectionNumerics
import Mathlib.Analysis.Real.Pi.Bounds

namespace Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
open MeasureTheory

/-- The comparison half-ball has volume at most one. -/
theorem comparison_halfBall_volume_le_one :
    volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) ≤ 1 := by
  rw [EuclideanSpace.volume_closedBall_fin_three,
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
    ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ (3 : ℕ))]
  apply ENNReal.ofReal_le_one.mpr
  nlinarith [Real.pi_lt_four]

/-- The common group projection floor is an admissible relative mass parameter. -/
theorem groupFloor_le_one {N S : ℝ} (hN : 1 ≤ N) (hS : 0 ≤ S) : groupFloor N S ≤ 1 := by
  have hp : N ^ (-(30 * S)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)
  unfold groupFloor
  exact (div_le_self (by positivity) (by norm_num)).trans hp

/-- The small-slack group floor lies below the original packet-relative floor
obtained after entry-volume cancellation. -/
theorem groupFloor_le_original_fraction {N κ σ ρ gain L δ₀ ε τ : ℝ}
    (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hκN : κ ≤ N ^ σ) (hσ : 0 ≤ σ)
    (hρ : 0 ≤ ρ) (hgain : 0 ≤ gain) (hL : 0 ≤ L) (hε : 0 ≤ ε) (hτ : 0 ≤ τ)
    (hδρ : δ₀ ≤ ρ * gain) :
    groupFloor N (slackTot ρ gain L ε σ τ) ≤
      N ^ (-((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ) - ε - τ) /
        ((2 : ℝ) ^ (23 : ℕ) * κ ^ 6) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hκpos : 0 < κ := zero_lt_one.trans_le hκ
  have hκ6 : κ ^ 6 ≤ N ^ (6 * σ) := by
    calc
      κ ^ 6 ≤ (N ^ σ) ^ (6 : ℕ) := by gcongr
      _ = _ := by rw [← Real.rpow_mul_natCast hNpos.le]; congr 1; ring
  let S := slackTot ρ gain L ε σ τ
  have hexp : -(30 * S) + 6 * σ ≤
      -((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ) - ε - τ := by
    dsimp [S, slackTot]
    nlinarith [mul_le_mul_of_nonneg_right hδρ hL, mul_nonneg (mul_nonneg hρ hgain) hL]
  have hprod : N ^ (-(30 * S)) * κ ^ 6 ≤
      N ^ (-((12 * ρ * gain + 5 * δ₀) * L + 12 * ε + τ) - ε - τ) := by
    calc
      _ ≤ N ^ (-(30 * S)) * N ^ (6 * σ) := mul_le_mul_of_nonneg_left hκ6 (by positivity)
      _ = N ^ (-(30 * S) + 6 * σ) := (Real.rpow_add hNpos _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hN hexp
  apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ (23 : ℕ) * κ ^ 6)).mpr
  change (N ^ (-(30 * S)) / (2 : ℝ) ^ (30 : ℕ)) * ((2 : ℝ) ^ (23 : ℕ) * κ ^ 6) ≤ _
  calc
    _ = (N ^ (-(30 * S)) * κ ^ 6) / 128 := by ring
    _ ≤ N ^ (-(30 * S)) * κ ^ 6 := div_le_self (by positivity) (by norm_num)
    _ ≤ _ := hprod

/-- A scalar projection floor yields the exact ENNReal mass input used by
GroupRecovery, with no estimate of a projection image. -/
theorem groupFloor_mass_input {N S m H : ℝ} (hN : 0 < N)
    (hfloor : groupFloor N S ≤ m / H) :
    ENNReal.ofReal (groupFloor N S) *
      volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (1 / 2)) ≤ ENNReal.ofReal (m / H) := by
  calc
    _ ≤ ENNReal.ofReal (groupFloor N S) * 1 := mul_le_mul' le_rfl comparison_halfBall_volume_le_one
    _ = ENNReal.ofReal (groupFloor N S) := mul_one _
    _ ≤ _ := ENNReal.ofReal_le_ofReal hfloor

/-- An entry's packet-relative retained mass divided by its common cap. The
original packet prior, the old time length and the table count cancel exactly. -/
theorem relative_entry_floor_of_cap_budget {N base geom H C exponent loss slack : ℝ}
    (hN : 0 < N) (hbase : 0 < base) (hgeom : 0 < geom) (hH : 0 < H) (hC : 0 < C)
    (hcap : N ^ exponent * geom * H ≤ base * C * N ^ loss) :
    N ^ (-loss - slack) / C ≤ (base * N ^ (-exponent - slack) / geom) / H := by
  let lam := base * N ^ (-exponent) / geom
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hNc : 0 < N ^ exponent := Real.rpow_pos_of_pos hN _
  have hcap' : H ≤ lam * C * N ^ loss := by
    calc
      H = (N ^ exponent * geom * H) / (N ^ exponent * geom) := by
        field_simp
      _ ≤ (base * C * N ^ loss) / (N ^ exponent * geom) :=
        div_le_div_of_nonneg_right hcap (by positivity)
      _ = _ := by dsimp [lam]; rw [Real.rpow_neg hN.le]; field_simp <;> ring
  have hmass : lam * N ^ (-slack) ≤ base * N ^ (-exponent - slack) / geom := by
    apply le_of_eq
    calc
      _ = base * (N ^ (-exponent) * N ^ (-slack)) / geom := by dsimp [lam]; ring
      _ = _ := by rw [← Real.rpow_add hN]; congr 2 <;> ring
  have hh := power_projection_fraction hN hlam hH hC hmass hcap'
  convert hh using 1 <;> congr 2 <;> ring

end Submission.Obl.k4_finite_positive_mixed_cover_realization.TimeCoreBridge
