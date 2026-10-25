/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file DiscoveryGeometryNumerics.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.WorldTimeRow

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Zoom

/-- A single polynomial envelope for the actual first original row
constant. The factor Q belongs to the FIRST grid. -/
theorem discovery_first_row_constant_le {H Hg Q : ℝ}
    (hH : 1 ≤ H) (hHg : 0 ≤ Hg) (hHgH : Hg ≤ H) (hQ : 1 ≤ Q) :
    6 * (Q + (2 * Hg + 2) ^ 2) ≤ 102 * H ^ 2 * Q := by
  have hH₀ : 0 ≤ H := by linarith
  have hQ₀ : 0 ≤ Q := by linarith
  have hsquare : (2 * Hg + 2) ^ 2 ≤ 16 * H ^ 2 := by nlinarith
  have hHsq : 1 ≤ H ^ 2 := by nlinarith
  have hHQ : Q ≤ H ^ 2 * Q := by nlinarith only [mul_nonneg (sub_nonneg.mpr hHsq) hQ₀]
  have hHQ' : H ^ 2 ≤ H ^ 2 * Q := by nlinarith only [mul_nonneg (sq_nonneg H) (sub_nonneg.mpr hQ)]
  nlinarith only [hsquare, hHQ, hHQ']

theorem discovery_world_row_constant_le {H Hc Krow Q : ℝ}
    (hH : 1 ≤ H) (hHc : Hc ≤ 2 * H) (hQ : 1 ≤ Q)
    (hrow : Krow ≤ 102 * H ^ 2 * Q) :
    worldRowConstant Hc Krow ≤ 128 * H ^ 2 * Q := by
  have hHH : H ≤ H ^ 2 := by nlinarith
  have hHHQ : H ^ 2 ≤ H ^ 2 * Q := by
    nlinarith only [mul_nonneg (sq_nonneg H) (sub_nonneg.mpr hQ)]
  dsimp only [worldRowConstant]
  nlinarith only [hrow, hHc, hHH, hHHQ, hH]

theorem discovery_time_row_constants_le {H Hc Krow Q : ℝ}
    (hH : 1 ≤ H) (hHc : 1 ≤ Hc) (hHcH : Hc ≤ 2 * H)
    (hKrow : 0 ≤ Krow) (hQ : 1 ≤ Q) (hrow : Krow ≤ 102 * H ^ 2 * Q) :
    4 * worldRowConstant Hc Krow ^ 2 ≤ 65536 * H ^ 4 * Q ^ 2 ∧
      12 * worldRowConstant Hc Krow ^ 2 ≤ 196608 * H ^ 4 * Q ^ 2 := by
  have hK : 0 ≤ worldRowConstant Hc Krow := by dsimp only [worldRowConstant]; linarith
  have hbound := discovery_world_row_constant_le hH hHcH hQ hrow
  have hs := pow_le_pow_left₀ hK hbound 2
  constructor
  · exact (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 4)).trans_eq (by ring)
  · exact (mul_le_mul_of_nonneg_left hs (by norm_num : (0 : ℝ) ≤ 12)).trans_eq (by ring)

/-- The actual raw residual list budget has only THREE original floor
losses and TWO powers of the first-grid ratio. It contains no second-grid
interpolation factor. -/
theorem discovery_raw_list_bound_le {H Hg Hrow Lrow Q X : ℝ}
    (hH : 1 ≤ H) (hHg : 0 ≤ Hg) (hHgH : Hg ≤ H)
    (hHrow : 0 ≤ Hrow) (hHrowH : Hrow ≤ H) (hLrow : 0 ≤ Lrow)
    (hQ : 1 ≤ Q) (hX : 1 ≤ X) (hL : Lrow ≤ 196608 * H ^ 4 * Q ^ 2) :
    (Hg * X + 2) * ((X * H ^ 3 * (H + 2) ^ 2 * X) * (2 * (7 + Hrow + 2 * Lrow) + 2)) ≤
      30000000 * H ^ 10 * X ^ 3 * Q ^ 2 := by
  have hH₀ : 0 ≤ H := by linarith
  have hQ₀ : 0 ≤ Q := by linarith
  have hX₀ : 0 ≤ X := by linarith
  have hHX : 1 ≤ H * X := by
    have hh := mul_le_mul_of_nonneg_left hX hH₀
    nlinarith only [hh, hH]
  have hfirst : Hg * X + 2 ≤ 3 * H * X := by
    have hh := mul_le_mul_of_nonneg_right hHgH hX₀
    nlinarith only [hh, hHX]
  have hsquare : (H + 2) ^ 2 ≤ 9 * H ^ 2 := by nlinarith
  have hsecond : X * H ^ 3 * (H + 2) ^ 2 * X ≤ 9 * H ^ 5 * X ^ 2 := by
    calc
      _ ≤ X * H ^ 3 * (9 * H ^ 2) * X := by gcongr
      _ = _ := by ring
  have hHfour : H ≤ H ^ 4 := by nlinarith [sq_nonneg (H ^ 2 - H)]
  have hQsq : 1 ≤ Q ^ 2 := by nlinarith
  have hHQ : H ^ 4 ≤ H ^ 4 * Q ^ 2 := by
    nlinarith only [mul_nonneg (pow_nonneg hH₀ 4) (sub_nonneg.mpr hQsq)]
  have hthird : 2 * (7 + Hrow + 2 * Lrow) + 2 ≤ 800000 * H ^ 4 * Q ^ 2 := by
    nlinarith only [hL, hHrowH, hHfour, hHQ, hH]
  calc
    _ ≤ (3 * H * X) * ((9 * H ^ 5 * X ^ 2) * (800000 * H ^ 4 * Q ^ 2)) := by
      exact mul_le_mul hfirst (mul_le_mul hsecond hthird (by positivity) (by positivity))
        (by positivity) (by positivity)
    _ = 21600000 * H ^ 10 * X ^ 3 * Q ^ 2 := by ring
    _ ≤ _ := by gcongr <;> norm_num

/-- The planar filling budget is exactly a fixed polynomial times the
eighth floor-loss power; angular separation pays its remaining factor. -/
theorem discovery_planar_filling_budget {H X C : ℝ} (hH : 1 ≤ H) (hC : 0 ≤ C) :
    200 * C * (3 * H * X ^ 2) ^ 4 * (1 + H) ^ 2 ≤ 64800 * C * H ^ 6 * X ^ 8 := by
  have hsquare : (1 + H) ^ 2 ≤ 4 * H ^ 2 := by nlinarith
  calc
    _ ≤ 200 * C * (3 * H * X ^ 2) ^ 4 * (4 * H ^ 2) := by gcongr
    _ = _ := by ring

theorem discovery_hereditary_budget {H A C X V : ℝ}
    (hH : 1 ≤ H) (hA : A ≤ 7 * H) (hX : 1 ≤ X) (hV : 1 ≤ V) :
    18 * (A + 1) * (13824 * H ^ 7) ≤
      2000000 * (max 1 C + 1) * H ^ 8 * X ^ 8 * V ∧
    2 * A + 2 ≤ 2000000 * (max 1 C + 1) * H ^ 8 * X ^ 8 * V := by
  have hH₀ : 0 ≤ H := by linarith
  have hcoeff : (1 : ℝ) ≤ max 1 C + 1 := by linarith [le_max_left (1 : ℝ) C]
  have hXpow : 1 ≤ X ^ 8 := one_le_pow₀ hX
  have hbase : 2000000 * H ^ 8 ≤ 2000000 * (max 1 C + 1) * H ^ 8 * X ^ 8 * V := by
    calc
      _ ≤ 2000000 * (max 1 C + 1) * H ^ 8 := by
        have hh := mul_le_mul_of_nonneg_left hcoeff (by norm_num : (0 : ℝ) ≤ 2000000)
        simpa only [mul_one] using mul_le_mul_of_nonneg_right hh (pow_nonneg hH₀ 8)
      _ ≤ (2000000 * (max 1 C + 1) * H ^ 8) * X ^ 8 := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hXpow
          (by positivity : 0 ≤ 2000000 * (max 1 C + 1) * H ^ 8)
      _ ≤ _ := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hV
          (by positivity : 0 ≤ 2000000 * (max 1 C + 1) * H ^ 8 * X ^ 8)
  constructor
  · apply le_trans ?_ hbase
    have hA' : A + 1 ≤ 8 * H := by linarith
    calc
      _ ≤ 18 * (8 * H) * (13824 * H ^ 7) := by gcongr
      _ = 1990656 * H ^ 8 := by ring
      _ ≤ _ := by gcongr <;> norm_num
  · apply le_trans ?_ hbase
    have hHpow : H ≤ H ^ 8 := le_self_pow₀ hH (by norm_num : 8 ≠ 0)
    nlinarith only [hA, hHpow, hH]

theorem discovery_filling_constant_le {H C X V : ℝ}
    (hH : 1 ≤ H) (hC : 0 ≤ C) (hV : 0 ≤ V) :
    64800 * C * H ^ 6 * X ^ 8 * V ≤
      2000000 * (max 1 C + 1) * H ^ 8 * X ^ 8 * V := by
  have hC' : C ≤ max 1 C + 1 := by linarith [le_max_right (1 : ℝ) C]
  have hcoeff : 64800 * C ≤ 2000000 * (max 1 C + 1) := by
    nlinarith only [hC', hC]
  have hHpow : H ^ 6 ≤ H ^ 8 := pow_le_pow_right₀ hH (by norm_num : 6 ≤ 8)
  gcongr

/-- The exact scalar-support constant is a fixed polynomial envelope.
Here Q is the SECOND-grid ratio, introduced only after common choice. -/
theorem discovery_scalar_support_bound_le {H Hrow C X V Q d : ℝ}
    (hH : 1 ≤ H) (hHrow : 0 ≤ Hrow) (hHrowH : Hrow ≤ H)
    (hX : 1 ≤ X) (hV : 1 ≤ V) (hQ : 1 ≤ Q) (hd : d ≤ 1) :
    ((4 * (3 + 2 * Hrow) + 3) *
        (10648 * (2000000 * (max 1 C + 1) * H ^ 8 * X ^ 8 * V) ^ 3)) * (Q ^ 2) ^ d ≤
      3000000000000000000000000 * (max 1 C + 1) ^ 3 * H ^ 25 * X ^ 24 * V ^ 3 * Q ^ 2 := by
  have hH₀ : 0 ≤ H := by linarith
  have hX₀ : 0 ≤ X := by linarith
  have hV₀ : 0 ≤ V := by linarith
  have hfactor : 4 * (3 + 2 * Hrow) + 3 ≤ 23 * H := by linarith
  have hQpow : (Q ^ 2) ^ d ≤ Q ^ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ hQ) hd
  calc
    _ ≤ (23 * H) * (10648 * (2000000 * (max 1 C + 1) * H ^ 8 * X ^ 8 * V) ^ 3) * Q ^ 2 := by
      gcongr
    _ = (10648 * 23 * 2000000 ^ 3) * (max 1 C + 1) ^ 3 * H ^ 25 * X ^ 24 * V ^ 3 * Q ^ 2 := by ring
    _ ≤ _ := by gcongr <;> norm_num

theorem discovery_cut_scalar_budget {H η : ℝ} (hH : 1 ≤ H) (hη : 0 ≤ η)
    {n : ℕ} (hn : 1 ≤ n) :
    H * (32 * n * η) +
      (H * (n * (6860 * H * η)) +
        ((η * H + (n * η * H + n * η * (512 * H * H))) +
          n * ((5000 * 111 ^ 3) * η))) ≤
      10000000000 * n * H ^ 2 * η := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hHsq : H ≤ H ^ 2 := by nlinarith
  have hHsq' : 1 ≤ H ^ 2 := by nlinarith
  have h₁ : (n : ℝ) * H ≤ n * H ^ 2 := mul_le_mul_of_nonneg_left hHsq (by positivity)
  have h₂ : H ≤ n * H ^ 2 := by
    have hh := mul_le_mul_of_nonneg_right hnR (sq_nonneg H)
    exact hHsq.trans (by simpa only [one_mul] using hh)
  have h₃ : (n : ℝ) ≤ n * H ^ 2 := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hHsq' (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  have hinside : 33 * n * H + 7372 * n * H ^ 2 + H + (5000 * 111 ^ 3) * n ≤
      10000000000 * n * H ^ 2 := by nlinarith only [h₁, h₂, h₃]
  convert mul_le_mul_of_nonneg_right hinside hη using 1 <;> ring

end Submission.Obl.k4_scalar_graph_residual_discovery
