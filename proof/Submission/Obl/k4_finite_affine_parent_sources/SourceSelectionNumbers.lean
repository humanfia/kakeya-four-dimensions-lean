-- Adapted from o232 (k4_finite_positive_prepared_models), session branches merged: x0812 f7bed5fb, x0891 a669339c, x0923 e8a77b3e, x0807 989bea46 (SourceParentPalette: x0812's version); namespace and module path renamed to k4_finite_affine_parent_sources.
import Mathlib

/-!
# Numerics of the outer selection schedule

Inequalities in powers of a large `N ≥ 1` with a slack `1 ≤ κ ≤ N^σ`, used by
`SourceSelectionProof` to check the per-sample hypotheses of x0812's `SelectionSample`.

Written by x0891 for o232.
-/

namespace Submission.Obl.k4_finite_affine_parent_sources

namespace SelectionNumbers

theorem rpow_mul_rpow_le {N x y z : ℝ} (hN : 1 ≤ N) (h : x + y ≤ z) :
    N ^ x * N ^ y ≤ N ^ z := by
  rw [← Real.rpow_add (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hN h

/-- The mask and prune budget of `masked_residual`. -/
theorem budget {N κ σ c S a τt X m : ℝ} (hN : 1 ≤ N) (hκ : 1 ≤ κ) (hκσ : κ ≤ N ^ σ)
    (hσc : σ ≤ c / 8) (hσa : σ ≤ S * a / 24) (hτ : 2 * τt ≤ S * a / 4) (hX : 0 ≤ X)
    (hm : 0 ≤ m) (h1 : 12 * X ≤ N ^ (7 * c / 8)) (h2 : 1560 * m ≤ N ^ (S * a / 2))
    (h3 : 48 * m ≤ N ^ (3 * c / 4)) :
    X * N ^ (-c) + m * (130 * κ ^ 5 * N ^ (-S * a + 2 * τt) + 2 * κ * (2 * N ^ (-c))) ≤
      (4 * κ)⁻¹ := by
  have hSa : -S * a = -(S * a) := by ring
  rw [hSa]
  set Sa := S * a with hSa'
  have hN0 : 0 < N := by linarith
  have hκ0 : 0 < κ := by linarith
  -- κ powers
  have hk1 : κ ≤ N ^ σ := hκσ
  have hk2 : κ ^ 2 ≤ N ^ (2 * σ) := by
    calc κ ^ 2 ≤ (N ^ σ) ^ 2 := pow_le_pow_left₀ hκ0.le hk1 2
      _ = N ^ (2 * σ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  have hk6 : κ ^ 6 ≤ N ^ (6 * σ) := by
    calc κ ^ 6 ≤ (N ^ σ) ^ 6 := pow_le_pow_left₀ hκ0.le hk1 6
      _ = N ^ (6 * σ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  -- three terms after multiplying by 4κ
  have t1 : 4 * κ * (X * N ^ (-c)) ≤ 1 / 3 := by
    have e : N ^ σ * N ^ (-c) ≤ N ^ (-(7 * c / 8)) := rpow_mul_rpow_le hN (by linarith)
    have hinv : N ^ (-(7 * c / 8)) = (N ^ (7 * c / 8))⁻¹ := Real.rpow_neg hN0.le _
    have hpos : 0 < N ^ (7 * c / 8) := Real.rpow_pos_of_pos hN0 _
    calc 4 * κ * (X * N ^ (-c)) ≤ 4 * X * (N ^ σ * N ^ (-c)) := by
          have := mul_le_mul_of_nonneg_right hk1 (mul_nonneg hX (Real.rpow_nonneg hN0.le (-c)))
          nlinarith
      _ ≤ 4 * X * N ^ (-(7 * c / 8)) := mul_le_mul_of_nonneg_left e (by positivity)
      _ = 4 * X / N ^ (7 * c / 8) := by rw [hinv]; ring
      _ ≤ 1 / 3 := by rw [div_le_iff₀ hpos]; linarith
  have t2 : 4 * κ * (m * (130 * κ ^ 5 * N ^ (-Sa + 2 * τt))) ≤ 1 / 3 := by
    have e : N ^ (6 * σ) * N ^ (-Sa + 2 * τt) ≤ N ^ (-(Sa / 2)) :=
      rpow_mul_rpow_le hN (by linarith)
    have hinv : N ^ (-(Sa / 2)) = (N ^ (Sa / 2))⁻¹ := Real.rpow_neg hN0.le _
    have hpos : 0 < N ^ (Sa / 2) := Real.rpow_pos_of_pos hN0 _
    have hNe : 0 ≤ N ^ (-Sa + 2 * τt) := Real.rpow_nonneg hN0.le _
    calc 4 * κ * (m * (130 * κ ^ 5 * N ^ (-Sa + 2 * τt)))
        = 520 * m * (κ ^ 6 * N ^ (-Sa + 2 * τt)) := by ring
      _ ≤ 520 * m * (N ^ (6 * σ) * N ^ (-Sa + 2 * τt)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk6 hNe) (by positivity)
      _ ≤ 520 * m * N ^ (-(Sa / 2)) := mul_le_mul_of_nonneg_left e (by positivity)
      _ = 520 * m / N ^ (Sa / 2) := by rw [hinv]; ring
      _ ≤ 1 / 3 := by rw [div_le_iff₀ hpos]; linarith
  have t3 : 4 * κ * (m * (2 * κ * (2 * N ^ (-c)))) ≤ 1 / 3 := by
    have e : N ^ (2 * σ) * N ^ (-c) ≤ N ^ (-(3 * c / 4)) := rpow_mul_rpow_le hN (by linarith)
    have hinv : N ^ (-(3 * c / 4)) = (N ^ (3 * c / 4))⁻¹ := Real.rpow_neg hN0.le _
    have hpos : 0 < N ^ (3 * c / 4) := Real.rpow_pos_of_pos hN0 _
    have hNe : 0 ≤ N ^ (-c) := Real.rpow_nonneg hN0.le _
    calc 4 * κ * (m * (2 * κ * (2 * N ^ (-c)))) = 16 * m * (κ ^ 2 * N ^ (-c)) := by ring
      _ ≤ 16 * m * (N ^ (2 * σ) * N ^ (-c)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hk2 hNe) (by positivity)
      _ ≤ 16 * m * N ^ (-(3 * c / 4)) := mul_le_mul_of_nonneg_left e (by positivity)
      _ = 16 * m / N ^ (3 * c / 4) := by rw [hinv]; ring
      _ ≤ 1 / 3 := by rw [div_le_iff₀ hpos]; linarith
  have hsum : 4 * κ * (X * N ^ (-c) + m * (130 * κ ^ 5 * N ^ (-Sa + 2 * τt) +
      2 * κ * (2 * N ^ (-c)))) ≤ 1 := by
    have := add_le_add (add_le_add t1 t2) t3
    nlinarith
  rw [inv_eq_one_div, le_div_iff₀ (by positivity : (0 : ℝ) < 4 * κ)]
  linarith [hsum]

theorem pow_le_rpow {N κ σ : ℝ} (hN : 1 ≤ N) (hκ : 0 ≤ κ) (hκσ : κ ≤ N ^ σ) (k : ℕ) :
    κ ^ k ≤ N ^ (k * σ) := by
  have hN0 : 0 < N := by linarith
  calc κ ^ k ≤ (N ^ σ) ^ k := pow_le_pow_left₀ hκ hκσ k
    _ = N ^ (k * σ) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf

/-- The constant budget `κ²⁰ K⁴ C ≤ N^b` of `SelectionSample`. -/
theorem const_budget {N κ σ K C b : ℝ} (hN : 1 ≤ N) (hκ : 0 ≤ κ) (hκσ : κ ≤ N ^ σ)
    (hσ : σ ≤ b / 80) (hK : 0 ≤ K) (hKb : K ≤ N ^ (b / 16)) (hC : 0 ≤ C)
    (hCb : C ≤ N ^ (b / 2)) : κ ^ 20 * K ^ 4 * C ≤ N ^ b := by
  have hN0 : 0 < N := by linarith
  have h1 : κ ^ 20 ≤ N ^ (b / 4) := (pow_le_rpow hN hκ hκσ 20).trans
    (Real.rpow_le_rpow_of_exponent_le hN (by push_cast; linarith))
  have h2 : K ^ 4 ≤ N ^ (b / 4) := by
    calc K ^ 4 ≤ (N ^ (b / 16)) ^ 4 := pow_le_pow_left₀ hK hKb 4
      _ = N ^ (b / 4) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]; ring_nf
  calc κ ^ 20 * K ^ 4 * C ≤ N ^ (b / 4) * N ^ (b / 4) * N ^ (b / 2) := by
        apply mul_le_mul (mul_le_mul h1 h2 (by positivity) (by positivity)) hCb hC
        positivity
    _ = N ^ b := by rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf

/-- The room of the floor `τ = N^(-a)`: `τ A κ¹² ≤ 1`. -/
theorem floor_room {N κ σ a A : ℝ} (hN : 1 ≤ N) (hκ : 0 ≤ κ) (hκσ : κ ≤ N ^ σ)
    (hσ : σ ≤ a / 24) (hA : 0 ≤ A) (hAa : A ≤ N ^ (a / 2)) :
    N ^ (-a) * (A * κ ^ 12) ≤ 1 := by
  have hN0 : 0 < N := by linarith
  have h1 : κ ^ 12 ≤ N ^ (a / 2) := (pow_le_rpow hN hκ hκσ 12).trans
    (Real.rpow_le_rpow_of_exponent_le hN (by push_cast; linarith))
  calc N ^ (-a) * (A * κ ^ 12) ≤ N ^ (-a) * (N ^ (a / 2) * N ^ (a / 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hAa h1 (by positivity) (by positivity))
          (by positivity)
    _ = 1 := by rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]; ring_nf; exact Real.rpow_zero N

/-- `2 κ ≤ N` from `κ ≤ N^σ`, `σ ≤ 1/4`, `2 ≤ N^(3/4)`. -/
theorem two_kappa {N κ σ : ℝ} (hN : 1 ≤ N) (hκσ : κ ≤ N ^ σ) (hσ : σ ≤ 1 / 4)
    (h2 : 2 ≤ N ^ (3 / 4 : ℝ)) : 2 * κ ≤ N ^ (1 : ℝ) := by
  have hN0 : 0 < N := by linarith
  have h1 : κ ≤ N ^ (1 / 4 : ℝ) := hκσ.trans (Real.rpow_le_rpow_of_exponent_le hN hσ)
  calc 2 * κ ≤ 2 * N ^ (1 / 4 : ℝ) := by linarith
    _ ≤ N ^ (3 / 4 : ℝ) * N ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hN0.le _)
    _ = N ^ (1 : ℝ) := by rw [← Real.rpow_add hN0]; norm_num

/-- The fullness premise `4 / N^e ≤ N^(-a) κ` of the axis prune, `e = 2a`. -/
theorem axis_full {N a e κ : ℝ} (hN : 1 ≤ N) (he : e = 2 * a) (hκ : 1 ≤ κ)
    (h4 : 4 ≤ N ^ a) : 4 / N ^ e ≤ N ^ (-a) * κ := by
  have hN0 : 0 < N := by linarith
  have hpos : 0 < N ^ e := Real.rpow_pos_of_pos hN0 _
  rw [div_le_iff₀ hpos, he]
  have : N ^ (-a) * N ^ (2 * a) = N ^ a := by rw [← Real.rpow_add hN0]; ring_nf
  calc (4 : ℝ) ≤ N ^ a := h4
    _ = N ^ (-a) * N ^ (2 * a) := this.symm
    _ ≤ N ^ (-a) * κ * N ^ (2 * a) := by
        have : 0 ≤ N ^ (-a) * N ^ (2 * a) := by positivity
        nlinarith [Real.rpow_pos_of_pos hN0 (-a), Real.rpow_pos_of_pos hN0 (2 * a)]

/-- The inverse of the floor `N^(-a)` is `N^a`. -/
theorem floor_inv_le {N a x : ℝ} (hN : 1 ≤ N) (hax : a ≤ x) : (N ^ (-a))⁻¹ ≤ N ^ x := by
  have hN0 : 0 < N := by linarith
  rw [Real.rpow_neg hN0.le, inv_inv]
  exact Real.rpow_le_rpow_of_exponent_le hN hax

end SelectionNumbers

end Submission.Obl.k4_finite_affine_parent_sources
