import Submission.Obl.k4_scalar_grid_polynomial_qualification.Rounding
import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Growth

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification

open Set MeasureTheory Filter
open Submission.Obl.k4_scalar_marked_coefficient_smoothing
open Submission.Obl.k4_profile_density_bounds

/-- The higher-jet discovery's extra quarter power pays for a fixed rounding
margin, together with every prescribed coefficient and duration allowance. -/
theorem eventually_discovery_slack {N H K h : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : Subpower N H) (hK : Subpower N K) {κ ε : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hh : ∀ k, 0 < h k)
    (hscale : ∀ᶠ k in atTop, h k ≤ K k * N k ^ (-κ)) :
    ∀ᶠ k in atTop, H k ≤ N k ^ (ε / 2) ∧
      H k * h k ^ ((1 : ℝ) / 4) ≤ 1 / 2 ∧
      N k ^ (-(ε / 2)) ≤ (H k)⁻¹ := by
  let J : ℕ → ℝ := fun k => max (H k) (K k)
  have hJ : Subpower N J := subpower_max hH hK
  have hsmall := eventually_subpower_mul_rpow_lt hN hNt hJ.1 hJ.2 5
    (a := -κ) (b := 0) (by linarith) (A := 16) (by norm_num)
  simp only [Real.rpow_zero] at hsmall
  filter_upwards [hscale, hsmall, hH.2 (ε / 2) (by positivity)] with k hk hsm hcoeff
  have hNnonneg : 0 ≤ N k := by linarith [hN k]
  have hHpos : 0 < H k := by linarith [hH.1 k]
  have hJpos : 0 < J k := hHpos.trans_le (le_max_left _ _)
  have hq : (h k ^ ((1 : ℝ) / 4)) ^ 4 = h k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hh k).le]
    norm_num
  have hbound : H k ^ 4 * h k ≤ J k ^ 5 * N k ^ (-κ) := by
    calc
      _ ≤ J k ^ 4 * (K k * N k ^ (-κ)) := by
        exact mul_le_mul (pow_le_pow_left₀ hHpos.le (le_max_left _ _) 4)
          hk (hh k).le (pow_nonneg hJpos.le 4)
      _ ≤ J k ^ 4 * (J k * N k ^ (-κ)) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hNnonneg _))
          (pow_nonneg hJpos.le 4)
      _ = _ := by ring
  have hfourth : (H k * h k ^ ((1 : ℝ) / 4)) ^ 4 < ((1 : ℝ) / 2) ^ 4 := by
    rw [mul_pow, hq]
    nlinarith only [hbound, hsm]
  have hhalf : H k * h k ^ ((1 : ℝ) / 4) < (1 : ℝ) / 2 :=
    (pow_lt_pow_iff_left₀ (mul_nonneg hHpos.le (Real.rpow_nonneg (hh k).le _))
      (by norm_num) (by norm_num : 4 ≠ 0)).mp hfourth
  refine ⟨hcoeff, hhalf.le, ?_⟩
  rw [Real.rpow_neg hNnonneg]
  simpa only [one_div] using one_div_le_one_div_of_le hHpos hcoeff

/-- All the power-loss absorption happens once for the original fit, before
any polynomial rounding or modification of its witness times. -/
theorem eventually_upgrade_discovery_fit {α : Type*} [MeasurableSpace α]
    {N H K h : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hH : Subpower N H) (hK : Subpower N K) {κ ε : ℝ}
    (hκ : 0 < κ) (hε : 0 < ε) (hh : ∀ k, 0 < h k)
    (hscale : ∀ᶠ k in atTop, h k ≤ K k * N k ^ (-κ)) (M : ℕ) :
    ∀ᶠ k in atTop, ∀ (E : Set (α × ℝ)) (f : α × ℝ → Fin 2 → ℝ)
      (I : Set ℝ) (p : α × ℝ) (P : RowPolynomial),
      FitsWith E f I M (H k) (H k * h k ^ M * h k ^ ((1 : ℝ) / 4)) (h k / H k) p P →
      FitsWith E f I M (N k ^ (ε / 2)) (h k ^ M / 2)
        (h k * N k ^ (-(ε / 2))) p P := by
  filter_upwards [eventually_discovery_slack hN hNt hH hK hκ hε hh hscale]
    with k hk
  intro E f I p P hfit
  apply hfit.mono (Subset.rfl) (Subset.rfl) le_rfl hk.1
  · calc
      H k * h k ^ M * h k ^ ((1 : ℝ) / 4) =
          h k ^ M * (H k * h k ^ ((1 : ℝ) / 4)) := by ring
      _ ≤ h k ^ M * (1 / 2) := mul_le_mul_of_nonneg_left hk.2.1 (pow_pos (hh k) M).le
      _ = h k ^ M / 2 := by ring
  · simpa only [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hk.2.2 (hh k).le

end Submission.Obl.k4_scalar_grid_polynomial_qualification
