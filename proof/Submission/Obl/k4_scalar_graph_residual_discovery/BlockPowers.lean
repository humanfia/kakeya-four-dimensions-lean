import Mathlib
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing
open Submission.Obl.k4_profile_density_bounds

/-- A lower scale comparison with a subpower constant pays any fixed
positive exponent margin, also after taking a real power of the block. -/
theorem eventually_block_rpow_lower {N K h : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hK : Subpower N K) {κ b η : ℝ}
    (hb : 0 < b) (hη : 0 < η)
    (hscale : ∀ᶠ k in atTop, N k ^ (-κ) / K k ≤ h k) :
    ∀ᶠ k in atTop, N k ^ (-κ * b - η) ≤ h k ^ b := by
  filter_upwards [hscale, hK.2 (η / b) (div_pos hη hb)] with k hs hsmall
  have hNp : 0 < N k := lt_of_lt_of_le zero_lt_one (hN k)
  have hKp : 0 < K k := lt_of_lt_of_le zero_lt_one (hK.1 k)
  have hlower : N k ^ (-κ - η / b) ≤ h k := by
    calc
      _ = N k ^ (-κ) / N k ^ (η / b) := Real.rpow_sub hNp _ _
      _ ≤ N k ^ (-κ) / K k :=
        div_le_div_of_nonneg_left (Real.rpow_nonneg hNp.le _) hKp hsmall
      _ ≤ _ := hs
  have hr := Real.rpow_le_rpow (Real.rpow_nonneg hNp.le _) hlower hb.le
  rw [← Real.rpow_mul hNp.le] at hr
  have he : (-κ - η / b) * b = -κ * b - η := by
    rw [sub_mul, div_mul_cancel₀ _ hb.ne']
  simpa only [he] using hr

/-- A polynomial subpower cost at a strictly smaller scale fits in the
block's real power. The coefficient sequence may contain any fixed
polynomial loss from the original data. -/
theorem eventually_monomial_le_block_rpow {N H K h : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : Subpower N H) (hK : Subpower N K) {κ b a A : ℝ}
    (hb : 0 < b) (hgap : a < -κ * b) (hA : 0 ≤ A) (p : ℕ)
    (hscale : ∀ᶠ k in atTop, N k ^ (-κ) / K k ≤ h k) :
    ∀ᶠ k in atTop, A * H k ^ p * N k ^ a ≤ h k ^ b := by
  let η : ℝ := (-κ * b - a) / 2
  have hη : 0 < η := by dsimp only [η]; linarith
  have hmiddle : a < -κ * b - η := by dsimp only [η]; linarith
  filter_upwards [eventually_block_rpow_lower hN hK hb hη hscale,
    eventually_subpower_mul_rpow_lt hN hNt hH.1 hH.2 p hmiddle hA] with k hlower hupper
  exact hupper.le.trans hlower

/-- A fixed floor exponent with strict surplus is below the actual dyadic
block power; it is chosen independently of all later loss budgets. -/
theorem eventually_floor_le_block_rpow {N K h : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hK : Subpower N K) {κ b C : ℝ}
    (hb : 0 < b) (hC : κ * b < C)
    (hscale : ∀ᶠ k in atTop, N k ^ (-κ) / K k ≤ h k) :
    ∀ᶠ k in atTop, N k ^ (-C) ≤ h k ^ b := by
  have hη : 0 < C - κ * b := sub_pos.mpr hC
  filter_upwards [eventually_block_rpow_lower hN hK hb hη hscale] with k hk
  have he : -κ * b - (C - κ * b) = -C := by ring
  simpa only [he] using hk

end Submission.Obl.k4_scalar_graph_residual_discovery
