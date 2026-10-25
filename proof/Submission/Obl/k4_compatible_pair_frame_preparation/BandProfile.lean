-- Adapted from this LOT tree, o114, session x0680, branch x0680,
-- Submission/Obl/k4_terminal_representative_atlas/Preparation/BandProfile.lean.

import Submission.Obl.k4_compatible_pair_frame_preparation.Interface
import Submission.Obl.k4_compatible_pair_frame_preparation.BandInterpolation
import Submission.Obl.k4_quadratic_atlas_normalization.Thickness

namespace Submission.Obl.k4_compatible_pair_frame_preparation.Band

open Set

/-- The one-depth band and world-equation-window estimates give the complete
all-width cap. The geometry is contained in `J`, which in preparation is
`(100 * κ)^3 * |det Qnew|`. All other losses are independent of polynomial format. -/
theorem band_bound_of_profile {N L u d dc τ K J : ℝ} {V : ENNReal}
    (hN : 1 < N) (hL : 0 ≤ L) (hu : 0 ≤ u) (hd : 0 ≤ d) (hdc : d ≤ dc)
    (hK : 1 ≤ K) (hJ : 0 ≤ J) (f : ℝ → ℝ) (R : Finset ℝ)
    (h0 : 0 ∈ R) (hLmem : L ∈ R)
    (hcover : ∀ r ∈ Icc 0 L, ∃ s ∈ R, s ≤ r ∧ r ≤ s + u)
    (hprofile : ∀ r ∈ R, f L - f r ≤ d * (L - r))
    (F : ℝ → ENNReal) (hmono : Monotone F)
    (hdepth : ∀ r ∈ R, F (N ^ (-r)) ≤ ENNReal.ofReal
      (N ^ (-f r + τ) * (2 * N ^ (-r) / δ N r + 2) * J) * V)
    (hwindow : ∀ ρ, F ρ ≤ ENNReal.ofReal
      (N ^ (-f 0 + τ) * (16 * (1 + K ^ 2 / δ N 0)) * J) * V)
    {ρ : ℝ} (hρ : 0 < ρ) :
    F ρ ≤ ENNReal.ofReal
      ((32 * K ^ 2 * N ^ (-f L + τ) * J) * (2 : ℝ) ^ d * N ^ (d * u) *
        (max ρ (δ N L) / δ N L) ^ dc) * V := by
  have hN0 : 0 < N := by linarith
  let C₀ := N ^ (-f L + τ)
  let A := 32 * K ^ 2 * C₀ * J
  have hC₀ : 0 < C₀ := Real.rpow_pos_of_pos hN0 _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hKsq : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hcap (r : ℝ) (hr : r ∈ R) : N ^ (-f r + τ) ≤ C₀ * N ^ (d * (L - r)) := by
    dsimp [C₀]
    rw [← Real.rpow_add hN0]
    apply Real.rpow_le_rpow_of_exponent_le hN.le
    linarith [hprofile r hr]
  have h4A : 4 * C₀ * J ≤ A := by
    have hnum : (4 : ℝ) ≤ 32 * K ^ 2 := by linarith
    calc 4 * C₀ * J = 4 * (C₀ * J) := by ring
      _ ≤ (32 * K ^ 2) * (C₀ * J) :=
        mul_le_mul_of_nonneg_right hnum (by positivity)
      _ = A := by dsimp [A]; ring
  have hgrid : ∀ r ∈ R, F (N ^ (-r)) ≤ ENNReal.ofReal (A * N ^ (d * (L - r))) * V := by
    intro r hr
    have hδr : N ^ (-r) ≤ δ N r :=
      (Submission.Obl.k4_quadratic_atlas_normalization.delta_bounds hN0 r).1
    have hδr0 : 0 < δ N r := (Real.rpow_pos_of_pos hN0 _).trans_le hδr
    have hratio : 2 * N ^ (-r) / δ N r + 2 ≤ 4 := by
      rw [mul_div_assoc]
      have := (div_le_one hδr0).mpr hδr
      linarith
    apply (hdepth r hr).trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    calc N ^ (-f r + τ) * (2 * N ^ (-r) / δ N r + 2) * J ≤
        (C₀ * N ^ (d * (L - r))) * 4 * J := by
          apply mul_le_mul_of_nonneg_right _ hJ
          exact mul_le_mul (hcap r hr) hratio (by positivity) (by positivity)
      _ = (4 * C₀ * J) * N ^ (d * (L - r)) := by ring
      _ ≤ A * N ^ (d * (L - r)) :=
        mul_le_mul_of_nonneg_right h4A (by positivity)
  have hwhole : ∀ ρ, F ρ ≤ ENNReal.ofReal (A * N ^ (d * L)) * V := by
    intro ρ
    have hδ0 : δ N 0 = 1 := by simp [δ]
    have hwindowNum : 16 * (1 + K ^ 2 / δ N 0) ≤ 32 * K ^ 2 := by
      rw [hδ0, div_one]
      linarith
    have hcap0 := hcap 0 h0
    simp only [sub_zero] at hcap0
    apply (hwindow ρ).trans
    apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    calc N ^ (-f 0 + τ) * (16 * (1 + K ^ 2 / δ N 0)) * J ≤
        (C₀ * N ^ (d * L)) * (32 * K ^ 2) * J := by
          apply mul_le_mul_of_nonneg_right _ hJ
          exact mul_le_mul hcap0 hwindowNum (by positivity) (by positivity)
      _ = A * N ^ (d * L) := by dsimp [A]; ring
  exact band_bound_of_comparable_depth_grid hN hL hu hd hdc hA
    (Submission.Obl.k4_quadratic_atlas_normalization.delta_bounds hN0 L).1
    (Submission.Obl.k4_quadratic_atlas_normalization.delta_bounds hN0 L).2
    R hLmem hcover F hmono hgrid hwhole hρ

end Submission.Obl.k4_compatible_pair_frame_preparation.Band
