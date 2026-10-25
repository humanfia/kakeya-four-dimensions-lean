-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0891 1eea2098, x0807 96b53fe0, x0812 ed32fd12, x0923 e804508c; namespace and module path renamed to k4_finite_affine_parent_sources.
import Submission.Obl.k4_finite_affine_parent_sources.RowPowerBudgets
import Mathlib.Tactic.FieldSimp

namespace Submission.Obl.k4_finite_affine_parent_sources

noncomputable section

/-- A geometric exponent small enough for both the model slack and the
positive cumulative narrowness of the chosen parent. -/
def trackingSlackExponent (n : ℕ) (ℓ ρ : ℝ) : ℝ :=
  min ((ρ / (1000000 * ((n : ℝ) + 1))) / 1000) (ℓ / 1000)

theorem trackingSlackExponent_pos (n : ℕ) {ℓ ρ : ℝ} (hℓ : 0 < ℓ) (hρ : 0 < ρ) :
    0 < trackingSlackExponent n ℓ ρ := by
  unfold trackingSlackExponent
  apply lt_min <;> positivity

theorem trackingSlackExponent_model (n : ℕ) {ℓ ρ : ℝ} (hρ : 0 ≤ ρ) :
    5 * trackingSlackExponent n ℓ ρ ≤ ρ / (1000000 * ((n : ℝ) + 1)) := by
  have hθ : 0 ≤ ρ / (1000000 * ((n : ℝ) + 1)) := by positivity
  have hh := min_le_left ((ρ / (1000000 * ((n : ℝ) + 1))) / 1000) (ℓ / 1000)
  change 5 * min _ _ ≤ _
  linarith

theorem trackingSlackExponent_narrowness (n : ℕ) (ℓ ρ : ℝ) :
    1000 * trackingSlackExponent n ℓ ρ ≤ ℓ := by
  have hh := min_le_right ((ρ / (1000000 * ((n : ℝ) + 1))) / 1000) (ℓ / 1000)
  change 1000 * min _ _ ≤ _
  linarith

/-- The same native slack pays all five coefficients and the three
tracking rows, including the fixed factor sixteen. -/
theorem native_tracking_model_budget (n : ℕ) (N ℓ ρ : ℝ)
    (hN : 1 ≤ N) (hρ : 0 ≤ ρ) (hconstant : 16 ≤ N ^ trackingSlackExponent n ℓ ρ) :
    16 * (N ^ trackingSlackExponent n ℓ ρ) ^ 4 ≤
      N ^ (ρ / (1000000 * ((n : ℝ) + 1))) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  exact (geometric_row_power_budget N (N ^ trackingSlackExponent n ℓ ρ)
    (trackingSlackExponent n ℓ ρ) hN (by positivity) le_rfl hconstant).trans
      (Real.rpow_le_rpow_of_exponent_le hN (trackingSlackExponent_model n hρ))

/-- A fixed coefficient loss and the original path slack each use only
one eighth of the available original exponent. -/
theorem tracking_parent_slack_budget (N κ B : ℝ) (hN : 1 ≤ N) (hκ : 0 ≤ κ)
    (hκpow : κ ≤ N ^ (B / 8)) (hconstant : 18 ≤ N ^ (B / 8)) :
    18 * κ ≤ N ^ (B / 4) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    _ ≤ N ^ (B / 8) * N ^ (B / 8) := mul_le_mul hconstant hκpow hκ (by positivity)
    _ = N ^ (B / 4) := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring

/-- The original strip width costs at most a quarter of the geometric
exponent. Its nonnegative fit loss helps this estimate. -/
theorem tracking_relative_row_budget (N κ B h L fitLoss : ℝ)
    (hN : 1 ≤ N) (hκ : 0 ≤ κ) (hfit : 0 ≤ fitLoss)
    (hparent : 18 * κ ≤ N ^ (B / 4)) (hgain : h * L ≤ B / 4)
    (hconstant : 2 ≤ N ^ (B / 2)) :
    36 * κ / (N ^ fitLoss * N ^ (-h * L)) ≤ N ^ B := by
  have htwo : 2 ≤ N ^ (B - B / 4 - h * L) :=
    hconstant.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  have hh := no_candidate_row_power_budget N (18 * κ) (B / 4) B h L fitLoss hN
    (by positivity) hparent hfit htwo
  convert hh using 1 <;> ring

/-- The source floor's epsilon bound already dominates the exact
original-candidate floor; no geometric slack enters this comparison. -/
theorem candidate_floor_of_inverse_budget (N cost ε τ : ℝ)
    (hN : 1 ≤ N) (hcost : 0 ≤ cost) (hε : 0 < ε) (hτ : 0 < τ)
    (hbudget : τ⁻¹ ≤ N ^ (ε / 4000000)) :
    N ^ (-cost - ε) ≤ τ := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  calc
    _ ≤ N ^ (-(ε / 4000000)) :=
      Real.rpow_le_rpow_of_exponent_le hN (by linarith)
    _ = (N ^ (ε / 4000000))⁻¹ := Real.rpow_neg hN0.le _
    _ ≤ τ := (inv_le_comm₀ (by positivity : 0 < N ^ (ε / 4000000)) hτ).mpr hbudget

/-- A deficient-axis mask at half the geometric exponent supplies the
required physical fullness, with only a fixed factor four. -/
theorem tracking_axis_fullness_budget (N κ B : ℝ) (hN : 1 ≤ N) (hκ : 1 ≤ κ)
    (hconstant : 4 ≤ N ^ (B / 2)) :
    4 / N ^ B ≤ N ^ (-(B / 2)) * κ := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hN0 B)).mpr
  calc
    _ ≤ N ^ (B / 2) := hconstant
    _ = N ^ (-(B / 2)) * N ^ B := by
      rw [← Real.rpow_add hN0]
      congr 1
      ring
    _ = N ^ (-(B / 2)) * 1 * N ^ B := by ring
    _ ≤ (N ^ (-(B / 2)) * κ) * N ^ B := by gcongr

/-- A parent chosen after the first unit of depth has enough cumulative
narrowness to absorb the transverse term at this geometric exponent. -/
theorem tracking_parent_area_margin (β ℓ u sp δ L : ℝ)
    (hβ : 0 ≤ β) (hℓ : 0 ≤ ℓ) (hu : 0 ≤ u) (hL : 0 ≤ L)
    (hsmall : 1000 * β ≤ ℓ) (hparent : u ≤ sp) (hδ : 4 * δ ≤ u * β) :
    (u * L * β) / 2 ≤ (ℓ * sp - 2 * δ) * L - 3 * (u * L * β) := by
  have hsp := mul_le_mul_of_nonneg_left hparent hℓ
  have hβu := mul_le_mul_of_nonneg_left hsmall hu
  have hbase : u * β / 2 ≤ ℓ * sp - 2 * δ - 3 * (u * β) := by
    nlinarith only [hsp, hβu, hδ, mul_nonneg hu hβ]
  have hh := mul_le_mul_of_nonneg_right hbase hL
  convert hh using 1 <;> ring

/-- The preceding exponent margin gives exactly the parent area budget
used by `TrackingGeometry`, in original time units. -/
theorem tracking_parent_area_budget (N q B χ area : ℝ) (hN : 1 ≤ N)
    (hmargin : B / 2 ≤ χ - 3 * B) (hconstant : 4 ≤ N ^ (B / 2))
    (harea : area ≤ q ^ 2 * N ^ (-χ)) :
    area ≤ q ^ 2 / (2 * (N ^ B) ^ 3) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have htwo : 2 ≤ N ^ (χ - 3 * B) :=
    (by norm_num : (2 : ℝ) ≤ 4).trans
      (hconstant.trans (Real.rpow_le_rpow_of_exponent_le hN hmargin))
  exact cumulative_area_power_budget N q (N ^ B) B χ area hN (by positivity) le_rfl htwo harea

/-- Converting a cumulative determinant estimate to physical area keeps
the exact squared original time length. -/
theorem normalized_area_of_cumulative_narrowness (N w target error area : ℝ) (T : ℕ)
    (hN : 1 ≤ N) (harea : area * (4 : ℝ) ^ T ≤ N ^ (-(w - error)))
    (hprofile : |w - target| ≤ error) :
    area ≤ (((2 : ℝ) ^ T)⁻¹) ^ 2 * N ^ (-(target - 2 * error)) := by
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hp := abs_le.mp hprofile
  have ha : area * (4 : ℝ) ^ T ≤ N ^ (-(target - 2 * error)) :=
    harea.trans (Real.rpow_le_rpow_of_exponent_le hN (by linarith only [hp.1]))
  have hfour : (4 : ℝ) ^ T = ((2 : ℝ) ^ T) ^ 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, ← pow_mul, mul_comm 2 T, pow_mul]
  have hq : (((2 : ℝ) ^ T)⁻¹) ^ 2 * (4 : ℝ) ^ T = 1 := by
    rw [hfour]
    field_simp
  calc
    _ = (((2 : ℝ) ^ T)⁻¹) ^ 2 * (area * (4 : ℝ) ^ T) := by
      rw [show (((2 : ℝ) ^ T)⁻¹) ^ 2 * (area * (4 : ℝ) ^ T) =
        ((((2 : ℝ) ^ T)⁻¹) ^ 2 * (4 : ℝ) ^ T) * area by ring, hq, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left ha (sq_nonneg _)

end

end Submission.Obl.k4_finite_affine_parent_sources
