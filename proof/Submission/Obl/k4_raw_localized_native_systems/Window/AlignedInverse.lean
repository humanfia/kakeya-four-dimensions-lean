import Submission.Obl.k4_raw_localized_native_systems.MinorFrameInverse
import Submission.Obl.k4_raw_localized_native_systems.Window.ChartVelocity

namespace Submission.Obl.k4_raw_localized_native_systems.Window

open MeasureTheory Set
open Submission.Obl.k4_finite_width_output_exclusion
open Pairing

noncomputable section

theorem normalTangent_eq (n : Plane) : normalTangent n = tangentOfNormal n := by
  ext i
  fin_cases i <;> simp [normalTangent, tangentOfNormal, rot90]

/-- A fixed relative gain of four and a long earlier major axis give both exact
raw inverse-frame estimates. The window exponent is fixed as `s + 4`. -/
theorem raw_inverse_bounds {p : Data} {k M D : ℕ} {W : Atlas p k} {e : Fin W.C}
    {κ r N χ s g thickness β : ℝ} {n : Plane} {l : Line}
    (hN : 256 ≤ N) (hχ : 0 ≤ χ) (hs : s ≤ 1)
    (hκ : 1 ≤ κ) (hκN : κ ≤ N) (hT : (2 : ℝ) ^ W.T ≤ N)
    (hW : WChart p k W M D κ r e) (hl : l ∈ W.A e)
    (hn : ‖n‖ = 1) (hv : ‖v l‖ ≤ N)
    (hg : 0 ≤ g) (hth0 : 0 ≤ thickness) (hth : thickness ≤ N * g)
    (hcurrent : |inner ℝ n (v l - β • n)| ≤ 2 * N * g)
    (hmajor : 1 / (N * (2 : ℝ) ^ W.T) ≤ ‖longCol (W.Q e)‖)
    (hangle : min ‖n - minorNormal (W.Q e)‖ ‖n + minorNormal (W.Q e)‖ ≤
      N * minorWidth (W.Q e) * (2 : ℝ) ^ W.T)
    (hrel : g ≤ minorWidth (W.Q e) / ((2 : ℝ) ^ W.T * N ^ (4 : ℕ))) :
    (|(1 / (2 : ℝ) ^ W.T)⁻¹| +
        ‖Matrix.toEuclideanLin (W.Q e)⁻¹ (normalTangent n)‖ +
        ‖Matrix.toEuclideanLin (W.Q e)⁻¹ ((inner ℝ n (β • n)) • n - W.u e)‖ ≤
      N ^ ((s + 4) - s + χ) / 8) ∧
    thickness * ‖Matrix.toEuclideanLin (W.Q e)⁻¹ n‖ ≤ N ^ (-s + χ) / 8 := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hA : (0 : ℝ) < (2 : ℝ) ^ W.T := by positivity
  have hA1 : (1 : ℝ) ≤ (2 : ℝ) ^ W.T := one_le_pow₀ (by norm_num)
  have hQ := hW.det_ne
  have hb : 0 < minorWidth (W.Q e) :=
    div_pos (abs_pos.mpr hQ) (longCol_norm_pos hQ)
  have hmajorInv : ‖longCol (W.Q e)‖⁻¹ ≤ N * (2 : ℝ) ^ W.T := by
    have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 1 / (N * (2 : ℝ) ^ W.T)) hmajor
    simpa only [one_div, inv_inv] using h
  have htBound : ‖longCol (W.Q e)‖⁻¹ +
      (4 * (minorWidth (W.Q e))⁻¹) * (N * minorWidth (W.Q e) * (2 : ℝ) ^ W.T) ≤
        5 * N * (2 : ℝ) ^ W.T := by
    calc _ ≤ N * (2 : ℝ) ^ W.T +
        (4 * (minorWidth (W.Q e))⁻¹) * (N * minorWidth (W.Q e) * (2 : ℝ) ^ W.T) :=
          add_le_add hmajorInv le_rfl
      _ = _ := by field_simp; ring
  have htangent := (inverse_aligned_tangent hQ hangle).trans htBound
  have hden1 : 1 ≤ (2 : ℝ) ^ W.T * N ^ (4 : ℕ) := by
    calc 1 = 1 * 1 := by ring
      _ ≤ _ := mul_le_mul hA1 (one_le_pow₀ hN1) (by norm_num) (by positivity)
  have hgb : g ≤ minorWidth (W.Q e) := by
    apply hrel.trans
    exact div_le_self hb.le hden1
  have hgInv : g * (minorWidth (W.Q e))⁻¹ ≤ 1 := by
    calc _ ≤ minorWidth (W.Q e) * (minorWidth (W.Q e))⁻¹ :=
        mul_le_mul_of_nonneg_right hgb (inv_nonneg.mpr hb.le)
      _ = 1 := mul_inv_cancel₀ hb.ne'
  have hlast : (2 * N * g) * (4 * (minorWidth (W.Q e))⁻¹) ≤ 8 * N := by
    calc _ = 8 * N * (g * (minorWidth (W.Q e))⁻¹) := by ring
      _ ≤ 8 * N * 1 := mul_le_mul_of_nonneg_left hgInv (by positivity)
      _ = _ := mul_one _
  have hcenter := inverse_center_speed_le hQ hn hangle hv (hW.velocity_inverse hl) hcurrent
  have hcenter' : ‖Matrix.toEuclideanLin (W.Q e)⁻¹ (β • n - W.u e)‖ ≤
      2 * N * (2 : ℝ) ^ W.T + 5 * N ^ (2 : ℕ) * (2 : ℝ) ^ W.T + 8 * N := by
    apply hcenter.trans
    have hfirst := mul_le_mul_of_nonneg_right hκN (by positivity : 0 ≤ 2 * (2 : ℝ) ^ W.T)
    have hsecond := mul_le_mul_of_nonneg_left htBound hN0.le
    nlinarith
  have hinner : inner ℝ n (β • n) = β := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq, hn]
    ring
  have hN23 : N ^ (2 : ℕ) ≤ N ^ (3 : ℕ) := pow_le_pow_right₀ hN1 (by omega)
  have hN13 : N ≤ N ^ (3 : ℕ) := by
    simpa only [pow_one] using (pow_le_pow_right₀ hN1 (by omega : 1 ≤ 3))
  constructor
  · rw [hinner, normalTangent_eq]
    have hq : |(1 / (2 : ℝ) ^ W.T)⁻¹| = (2 : ℝ) ^ W.T := by
      rw [one_div, inv_inv, abs_of_pos hA]
    rw [hq]
    calc _ ≤ (2 : ℝ) ^ W.T + 5 * N * (2 : ℝ) ^ W.T +
          (2 * N * (2 : ℝ) ^ W.T + 5 * N ^ (2 : ℕ) * (2 : ℝ) ^ W.T + 8 * N) :=
        add_le_add (add_le_add le_rfl htangent) hcenter'
      _ ≤ N + 5 * N * N + (2 * N * N + 5 * N ^ (2 : ℕ) * N + 8 * N) := by gcongr
      _ = 5 * N ^ (3 : ℕ) + 7 * N ^ (2 : ℕ) + 9 * N := by ring
      _ ≤ 5 * N ^ (3 : ℕ) + 7 * N ^ (3 : ℕ) + 9 * N ^ (3 : ℕ) := by gcongr
      _ = 21 * N ^ (3 : ℕ) := by ring
      _ ≤ N ^ (4 : ℕ) / 8 := by
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
        have hh : 21 * 8 ≤ N := by linarith
        have := mul_le_mul_of_nonneg_right hh (pow_nonneg hN0.le 3)
        nlinarith
      _ ≤ N ^ ((s + 4) - s + χ) / 8 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        have hh := Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (4 : ℝ) ≤ (s + 4) - s + χ)
        exact (Real.rpow_natCast N 4).symm.le.trans hh
  · have hnInv : ‖Matrix.toEuclideanLin (W.Q e)⁻¹ n‖ ≤ 4 * (minorWidth (W.Q e))⁻¹ := by
      simpa only [hn, mul_one] using inverse_action_le_minor hQ n
    calc _ ≤ (N * g) * (4 * (minorWidth (W.Q e))⁻¹) :=
        mul_le_mul hth hnInv (norm_nonneg _) (by positivity)
      _ ≤ (N * (minorWidth (W.Q e) / ((2 : ℝ) ^ W.T * N ^ (4 : ℕ)))) *
          (4 * (minorWidth (W.Q e))⁻¹) := by gcongr
      _ = 4 / ((2 : ℝ) ^ W.T * N ^ (3 : ℕ)) := by field_simp
      _ ≤ 4 / N ^ (3 : ℕ) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact le_mul_of_one_le_left (by positivity) hA1
      _ ≤ 1 / (8 * N) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have hNsq : 32 ≤ N ^ (2 : ℕ) := by nlinarith [sq_nonneg (N - 1)]
        have := mul_le_mul_of_nonneg_right hNsq hN0.le
        nlinarith
      _ = N ^ (-1 : ℝ) / 8 := by rw [Real.rpow_neg_one]; ring
      _ ≤ N ^ (-s + χ) / 8 := by
        apply div_le_div_of_nonneg_right _ (by norm_num)
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)

end
end Submission.Obl.k4_raw_localized_native_systems.Window
