/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/Scales.lean.
Earlier source credits are retained below. -/

import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open Filter
open Submission.Obl.k4_profile_density_bounds

noncomputable section

/-- All fixed-power margins needed by the intercept selection hold
uniformly for the horizon allowed by the original field certificate. -/
theorem eventually_heavy_packet_margins (N H : ℕ → ℝ)
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : ∀ k, 1 ≤ H k)
    (hsub : ∀ e : ℝ, 0 < e → ∀ᶠ k in atTop, H k ≤ N k ^ e)
    {κ c Z B L : ℝ} (hκ : 0 < κ) (hκ₁ : κ ≤ 1)
    (hc : 0 < c) (hcκ : c ≤ κ / 1000) (hZ : 10 ≤ Z) (hB : Z + 10 ≤ B)
    (hL : 0 ≤ L) (p : ℕ) :
    ∀ᶠ k in atTop,
      20 * H k * N k ^ (-1 - 2 * c) ≤ N k ^ (-1 - c) ∧
      10 * N k ^ (-B) ≤ N k ^ (-1 - c) ∧
      10 * L * H k ^ (p + 1) * N k ^ (-B + κ) ≤ N k ^ (-1 - c) ∧
      L * H k ^ p * N k ^ (-Z) ≤ N k ^ (-1 - c) ∧
      H k * N k ^ (-B + κ) ≤ N k ^ (-Z) ∧
      H k * N k ^ (-κ / 8) ≤ N k ^ (-c) := by
  have hc₁ : c < 1 := by linarith
  have he := eventually_subpower_mul_rpow_lt hN hNt hH hsub 1
    (show -1 - 2 * c < -1 - c by linarith) (A := 20) (by norm_num)
  have hb := eventually_subpower_mul_rpow_lt hN hNt hH hsub 0
    (show -B < -1 - c by linarith) (A := 10) (by norm_num)
  have hf := eventually_subpower_mul_rpow_lt hN hNt hH hsub (p + 1)
    (show -B + κ < -1 - c by linarith) (A := 10 * L) (by positivity)
  have ho := eventually_subpower_mul_rpow_lt hN hNt hH hsub p
    (show -Z < -1 - c by linarith) (A := L) hL
  have ha := eventually_subpower_mul_rpow_lt hN hNt hH hsub 1
    (show -B + κ < -Z by linarith) (A := 1) (by norm_num)
  have hj := eventually_subpower_mul_rpow_lt hN hNt hH hsub 1
    (show -κ / 8 < -c by linarith) (A := 1) (by norm_num)
  filter_upwards [he, hb, hf, ho, ha, hj] with k he hb hf ho ha hj
  exact ⟨by simpa only [pow_one] using he.le,
    by simpa only [pow_zero, mul_one] using hb.le,
    hf.le, ho.le, by simpa only [pow_one, one_mul] using ha.le,
    by simpa only [pow_one, one_mul] using hj.le⟩

/-- The fine physical mesh divided by the actual horizon has its
expected power upper bound, with the original loss appearing once. -/
theorem physical_mesh_horizon_ratio {N H h κ B : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hh : 0 < h)
    (hlo : N ^ (-κ) / H ≤ h) :
    N ^ (-B) / h ≤ H * N ^ (-B + κ) := by
  calc
    _ ≤ N ^ (-B) / (N ^ (-κ) / H) :=
      div_le_div_of_nonneg_left (Real.rpow_pos_of_pos hN _).le
        (by positivity) hlo
    _ = H * (N ^ (-B) / N ^ (-κ)) := by
      field_simp [hH.ne', (Real.rpow_pos_of_pos hN (-κ)).ne']
    _ = _ := by
      rw [← Real.rpow_sub hN]
      congr 2
      ring

/-- Numerical preparation of the finite packet theorem from the six
fixed-power margins. No choice of packet or trajectory is involved. -/
theorem heavy_packet_scale_inequalities {N H h κ c Z B L : ℝ} (p : ℕ)
    (hN : 1 ≤ N) (hH : 1 ≤ H) (hh : 0 < h) (hc : 0 < c) (hZ : 0 ≤ Z)
    (hL : 0 ≤ L) (hlo : N ^ (-κ) / H ≤ h) (hup : h ≤ H * N ^ (-κ))
    (he : 20 * H * N ^ (-1 - 2 * c) ≤ N ^ (-1 - c))
    (hb : 10 * N ^ (-B) ≤ N ^ (-1 - c))
    (hf : 10 * L * H ^ (p + 1) * N ^ (-B + κ) ≤ N ^ (-1 - c))
    (ho : L * H ^ p * N ^ (-Z) ≤ N ^ (-1 - c))
    (ha : H * N ^ (-B + κ) ≤ N ^ (-Z))
    (hj : H * N ^ (-κ / 8) ≤ N ^ (-c)) :
    N ^ (-B) ≤ h * N ^ (-Z) ∧
      H * N ^ (-1 - 2 * c) ≤ N ^ (-1 - c) ∧
      N ^ (-B) + (L * H ^ p) * (N ^ (-B) / h) +
        2 * (H * N ^ (-1 - 2 * c)) ≤ N ^ (-1 - c) ∧
      (L * H ^ p) * N ^ (-Z) ≤ N ^ (-1 - c) ∧
      N ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8) ≤ N ^ (-1 - c) ∧
      N ^ (-1 - c) ≤ N ^ (-1 : ℝ) ∧ N ^ (-Z) ≤ 1 := by
  have hN₀ : 0 < N := by linarith
  have hH₀ : 0 < H := by linarith
  have hw : 0 < N ^ (-1 - c) := Real.rpow_pos_of_pos hN₀ _
  have hε : 0 ≤ H * N ^ (-1 - 2 * c) := by positivity
  have hr := physical_mesh_horizon_ratio (B := B) hN₀ hH₀ hh hlo
  have hsmall : N ^ (-B) / h ≤ N ^ (-Z) := hr.trans ha
  have hfine : 10 * ((L * H ^ p) * (N ^ (-B) / h)) ≤ N ^ (-1 - c) := by
    calc
      _ ≤ 10 * ((L * H ^ p) * (H * N ^ (-B + κ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hr (by positivity)) (by norm_num)
      _ = 10 * L * H ^ (p + 1) * N ^ (-B + κ) := by rw [pow_succ]; ring
      _ ≤ _ := hf
  have hpower : h ^ ((1 : ℝ) / 8) ≤ H * N ^ (-κ / 8) := by
    calc
      _ ≤ (H * N ^ (-κ)) ^ ((1 : ℝ) / 8) :=
        Real.rpow_le_rpow hh.le hup (by norm_num)
      _ = H ^ ((1 : ℝ) / 8) * N ^ (-κ / 8) := by
        rw [Real.mul_rpow hH₀.le (Real.rpow_nonneg hN₀.le _), ← Real.rpow_mul hN₀.le]
        congr 2
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_self_of_one_le hH (by norm_num)) (Real.rpow_nonneg hN₀.le _)
  refine ⟨by simpa only [mul_comm] using (div_le_iff₀ hh).mp hsmall,
    ?_, ?_, ho, ?_, ?_, ?_⟩
  · nlinarith
  · nlinarith
  · calc
      _ ≤ N ^ (-1 : ℝ) * N ^ (-c) :=
        mul_le_mul_of_nonneg_left (hpower.trans hj) (Real.rpow_nonneg hN₀.le _)
      _ = _ := by rw [← Real.rpow_add hN₀]; congr 1
  · exact Real.rpow_le_rpow_of_exponent_le hN (by linarith)
  · exact Real.rpow_le_one_of_one_le_of_nonpos hN (by linarith)

/-- The width gain in the heavy-group mass floor is exactly the
power required by the frozen potential certificate. -/
theorem target_intercept_width_gain {N : ℝ} (hN : 0 < N) (c d : ℝ) :
    (N ^ (-1 : ℝ) / N ^ (-1 - c)) ^ d = N ^ (d * c) := by
  rw [← Real.rpow_sub hN, ← Real.rpow_mul hN.le]
  congr 1
  ring

theorem target_intercept_base_gain {N : ℝ} (hN : 0 < N) (c d : ℝ) :
    (N ^ (-1 - c) / N ^ (-1 : ℝ)) ^ d = N ^ (-d * c) := by
  rw [← Real.rpow_sub hN, ← Real.rpow_mul hN.le]
  congr 1
  ring

/-- The physical width of a normalized base cell is covered by one
fixed compact range of the original all-exponent rectangular caps. -/
theorem normalized_mesh_exponent_bounds {N H h κ Z r : ℝ}
    (hN : 1 < N) (hH : 0 < H) (hHN : H ≤ N)
    (hlo : N ^ (-κ) / H ≤ h) (hup : h ≤ H * N ^ (-κ))
    (hr : N ^ (-r) = h * N ^ (-Z)) :
    Z + κ - 1 ≤ r ∧ r ≤ Z + κ + 1 := by
  have hN₀ : 0 < N := by linarith
  have hhlo : N ^ (-κ) / N ≤ h :=
    (div_le_div_of_nonneg_left (Real.rpow_nonneg hN₀.le _) hH hHN).trans hlo
  have hhhi : h ≤ N * N ^ (-κ) :=
    hup.trans (mul_le_mul_of_nonneg_right hHN (Real.rpow_nonneg hN₀.le _))
  have hl : N ^ (-(Z + κ + 1)) ≤ h * N ^ (-Z) := by
    calc
      _ = N ^ (-κ - 1) * N ^ (-Z) := by
        rw [← Real.rpow_add hN₀]
        congr 1
        ring
      _ = (N ^ (-κ) / N) * N ^ (-Z) := by rw [Real.rpow_sub hN₀, Real.rpow_one]
      _ ≤ _ := mul_le_mul_of_nonneg_right hhlo (Real.rpow_nonneg hN₀.le _)
  have hu : h * N ^ (-Z) ≤ N ^ (-(Z + κ - 1)) := by
    calc
      _ ≤ (N * N ^ (-κ)) * N ^ (-Z) :=
        mul_le_mul_of_nonneg_right hhhi (Real.rpow_nonneg hN₀.le _)
      _ = (N ^ (1 : ℝ) * N ^ (-κ)) * N ^ (-Z) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hN₀, ← Real.rpow_add hN₀]
        congr 1
        ring
  rw [← hr] at hl hu
  constructor <;> linarith [(Real.rpow_le_rpow_left_iff hN).mp hl,
    (Real.rpow_le_rpow_left_iff hN).mp hu]

/-- Rewrite an original rectangular power cap at the exact physical
base mesh and hidden width without changing its multiplicative constant. -/
theorem rectangular_power_factor {N : ℝ} (hN : 0 < N) (r s d : ℝ) :
    N ^ (-2 * r - d * s) = (N ^ (-r)) ^ (2 : ℕ) * (N ^ (-s)) ^ d := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_mul hN.le,
    ← Real.rpow_add hN]
  congr 1
  ring

theorem normalized_mesh_square {N : ℝ} (hN : 0 < N) (Z : ℝ) :
    (N ^ (-Z)) ^ (2 : ℕ) = N ^ (-2 * Z) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  congr 1
  ring

theorem inverse_normalized_mesh_square {N : ℝ} (hN : 0 < N) (Z : ℝ) :
    N ^ (2 * Z) = 1 / (N ^ (-Z)) ^ (2 : ℕ) := by
  rw [one_div, ← Real.rpow_natCast, ← Real.rpow_mul hN.le, ← Real.rpow_neg hN.le]
  congr 1
  ring

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
