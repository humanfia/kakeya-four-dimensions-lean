import Submission.Obl.k4_horizontal_supercritical_three_projections.RawIndex

/-!
# Fixed-power margins of the raw chart estimates

All scale relations needed by the support count and the cell caps, as
explicit inequalities between powers of `N`, at one index.
-/

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

noncomputable section

section Margins

variable {N K κ δ s₀ M e₀ : ℝ}

theorem rpow_neg_le_rpow_neg (hN : 1 ≤ N) {x y : ℝ} (hxy : y ≤ x) : N ^ (-x) ≤ N ^ (-y) :=
  Real.rpow_le_rpow_of_exponent_le hN (by linarith)

theorem rpow_neg_sq (hN : 0 < N) (x : ℝ) : (N ^ (-x)) ^ 2 = N ^ (-(2 * x)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]; congr 1; push_cast; ring

theorem rpow_neg_mul_rpow_neg (hN : 0 < N) (x y : ℝ) :
    N ^ (-x) * N ^ (-y) = N ^ (-(x + y)) := by
  rw [← Real.rpow_add hN]; congr 1; ring

/-- `C ≤ N^(x-y)` gives `C N^(-x) ≤ N^(-y)`. -/
theorem const_mul_rpow_neg_le (hN : 0 < N) {C x y : ℝ} (hC : C ≤ N ^ (x - y)) :
    C * N ^ (-x) ≤ N ^ (-y) := mul_rpow_le_of_le hN hC

theorem margin_q_half (hN : 0 < N) (_hK : 1 ≤ K) {q : ℝ} (hq : q ≤ K * N ^ (-(κ * δ)))
    (n1 : 2 * K ≤ N ^ (κ * δ)) : q ≤ 1 / 2 := by
  have h := const_mul_rpow_neg_le hN (x := κ * δ) (y := 0) (C := 2 * K) (by simpa using n1)
  simp only [neg_zero, Real.rpow_zero] at h
  linarith

theorem margin_δc (hN : 0 < N) (hK : 1 ≤ K) {q : ℝ} (hq : N ^ (-(κ * δ)) / K ≤ q)
    (n2 : K ^ 2 ≤ N ^ s₀) : N ^ (-(2 * (κ * δ) + s₀)) ≤ q ^ 2 := by
  have hK0 : 0 < K := by linarith
  have hg : 0 < N ^ (-(κ * δ)) / K := by positivity
  have hq2 : (N ^ (-(κ * δ)) / K) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hg.le hq 2
  have e : (N ^ (-(κ * δ)) / K) ^ 2 = N ^ (-(2 * (κ * δ))) / K ^ 2 := by
    rw [div_pow, rpow_neg_sq hN]
  rw [e] at hq2
  refine le_trans ?_ hq2
  rw [le_div_iff₀ (by positivity)]
  have h := const_mul_rpow_neg_le hN (x := 2 * (κ * δ) + s₀) (y := 2 * (κ * δ)) (C := K ^ 2)
    (by ring_nf; ring_nf at n2; exact n2)
  linarith

theorem margin_σq (hN : 0 < N) (hK : 1 ≤ K) {q : ℝ} (hq : N ^ (-(κ * δ)) / K ≤ q)
    (n3 : 2 * K ≤ N ^ (20 * s₀ - κ * δ)) : N ^ (-(20 * s₀)) ≤ q / 2 := by
  have hK0 : 0 < K := by linarith
  have h := const_mul_rpow_neg_le hN (x := 20 * s₀) (y := κ * δ) (C := 2 * K) n3
  have : N ^ (-(20 * s₀)) ≤ N ^ (-(κ * δ)) / K / 2 := by
    rw [div_div, le_div_iff₀ (by positivity)]; linarith
  linarith

theorem margin_σ_half (hN : 0 < N) (n4 : 2 ≤ N ^ (20 * s₀)) : N ^ (-(20 * s₀)) ≤ 1 / 2 := by
  have h := const_mul_rpow_neg_le hN (x := 20 * s₀) (y := 0) (C := 2) (by simpa using n4)
  simp only [neg_zero, Real.rpow_zero] at h
  linarith

theorem margin_Dq (hN : 0 < N) (hK : 1 ≤ K) {q : ℝ} (hq : N ^ (-(κ * δ)) / K ≤ q)
    (n5 : 8 * K ≤ N ^ (2 * κ * s₀ - κ * δ)) : N ^ (-(2 * κ * s₀)) ≤ q / 8 := by
  have hK0 : 0 < K := by linarith
  have h := const_mul_rpow_neg_le hN (x := 2 * κ * s₀) (y := κ * δ) (C := 8 * K) n5
  have : N ^ (-(2 * κ * s₀)) ≤ N ^ (-(κ * δ)) / K / 8 := by
    rw [div_div, le_div_iff₀ (by positivity)]; linarith
  linarith

theorem margin_small (hN : 0 < N) (hK : 1 ≤ K) {q : ℝ} (hq : N ^ (-(κ * δ)) / K ≤ q)
    (n6 : 12 * K ^ 2 ≤ N ^ (2 * κ * s₀ + 20 * s₀ - 2 * κ * δ))
    (n7 : 32 * K ^ 3 ≤ N ^ (e₀ - 2 * κ * δ))
    (n8 : 32 * K ^ 3 ≤ N ^ (M - 2 * κ * δ)) :
    2 * N ^ (-(2 * κ * s₀)) * N ^ (-(20 * s₀)) + N ^ (-e₀) + N ^ (-M) ≤ q ^ 2 / 2 := by
  have hK0 : 0 < K := by linarith
  have hg : 0 < N ^ (-(κ * δ)) / K := by positivity
  have hq2 : (N ^ (-(κ * δ)) / K) ^ 2 ≤ q ^ 2 := pow_le_pow_left₀ hg.le hq 2
  have e : (N ^ (-(κ * δ)) / K) ^ 2 = N ^ (-(2 * κ * δ)) / K ^ 2 := by
    rw [div_pow, rpow_neg_sq hN]; ring_nf
  rw [e] at hq2
  have hK23 : 6 * K ^ 2 ≤ 32 * K ^ 3 := by nlinarith
  have h1 := const_mul_rpow_neg_le hN (x := 2 * κ * s₀ + 20 * s₀) (y := 2 * κ * δ)
    (C := 12 * K ^ 2) n6
  have h2 := const_mul_rpow_neg_le hN (x := e₀) (y := 2 * κ * δ) (C := 6 * K ^ 2)
    (hK23.trans n7)
  have h3 := const_mul_rpow_neg_le hN (x := M) (y := 2 * κ * δ) (C := 6 * K ^ 2)
    (hK23.trans n8)
  have hDσ : N ^ (-(2 * κ * s₀)) * N ^ (-(20 * s₀)) = N ^ (-(2 * κ * s₀ + 20 * s₀)) :=
    rpow_neg_mul_rpow_neg hN _ _
  have hfin : 2 * N ^ (-(2 * κ * s₀)) * N ^ (-(20 * s₀)) + N ^ (-e₀) + N ^ (-M) ≤
      N ^ (-(2 * κ * δ)) / K ^ 2 / 2 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    have : 2 * N ^ (-(2 * κ * s₀)) * N ^ (-(20 * s₀)) = 2 * N ^ (-(2 * κ * s₀ + 20 * s₀)) := by
      rw [mul_assoc, hDσ]
    rw [this]
    nlinarith
  linarith

/-- The common bound `1 + a/q² ≤ 2K² N^((2κ-1)δ)`. -/
theorem margin_one_add (hN : 1 ≤ N) (hK : 1 ≤ K) (hκ : 1 < 2 * κ) (hδ : 0 < δ) {q : ℝ}
    (hq : N ^ (-(κ * δ)) / K ≤ q) :
    1 + N ^ (-δ) / q ^ 2 ≤ 2 * K ^ 2 * (N ^ (-δ) / N ^ (-(2 * (κ * δ)))) := by
  have hN0 : 0 < N := by linarith
  have h := one_add_div_sq_le (a := N ^ (-δ)) (q := q) (g := N ^ (-(κ * δ))) (K := K)
    (Real.rpow_pos_of_pos hN0 _) (Real.rpow_pos_of_pos hN0 _) hK hq ?_
  · rwa [rpow_neg_sq hN0] at h
  · rw [rpow_neg_sq hN0]
    have h1 : N ^ (-(2 * (κ * δ))) ≤ N ^ (-δ) := rpow_neg_le_rpow_neg hN (by nlinarith)
    have h2 : N ^ (-δ) ≤ N ^ (-δ) * K ^ 2 :=
      le_mul_of_one_le_right (Real.rpow_nonneg hN0.le _) (one_le_pow₀ hK)
    linarith

theorem margin_contact (hN : 1 ≤ N) (hK : 1 ≤ K) (hκ : 1 < 2 * κ) (hδ : 0 < δ) {q : ℝ}
    (hq : N ^ (-(κ * δ)) / K ≤ q)
    (n7 : 32 * K ^ 3 ≤ N ^ (e₀ - 2 * κ * δ))
    (n8 : 32 * K ^ 3 ≤ N ^ (M - 2 * κ * δ)) :
    8 * K ^ 2 * (1 + N ^ (-δ) / q ^ 2) * (N ^ (-M) + N ^ (-e₀)) ≤ K * N ^ (-δ) := by
  have hN0 : 0 < N := by linarith
  have hK0 : 0 < K := by linarith
  have h1 := margin_one_add hN hK hκ hδ hq
  have hg2 : 0 < N ^ (-(2 * (κ * δ))) := Real.rpow_pos_of_pos hN0 _
  have hχζ : 0 ≤ N ^ (-M) + N ^ (-e₀) := by positivity
  have h2 := const_mul_rpow_neg_le hN0 (x := M) (y := 2 * κ * δ) (C := 32 * K ^ 3) n8
  have h3 := const_mul_rpow_neg_le hN0 (x := e₀) (y := 2 * κ * δ) (C := 32 * K ^ 3) n7
  have e : N ^ (-(2 * (κ * δ))) = N ^ (-(2 * κ * δ)) := by ring_nf
  rw [e] at h1 hg2
  calc 8 * K ^ 2 * (1 + N ^ (-δ) / q ^ 2) * (N ^ (-M) + N ^ (-e₀))
      ≤ 8 * K ^ 2 * (2 * K ^ 2 * (N ^ (-δ) / N ^ (-(2 * κ * δ)))) * (N ^ (-M) + N ^ (-e₀)) := by
        gcongr
    _ = K * N ^ (-δ) * (16 * K ^ 3 * (N ^ (-M) + N ^ (-e₀)) / N ^ (-(2 * κ * δ))) := by
        field_simp <;> ring
    _ ≤ K * N ^ (-δ) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_one hg2]
        nlinarith
    _ = K * N ^ (-δ) := mul_one _

theorem margin_cell (hN : 1 ≤ N) (hK : 1 ≤ K) (hκ : 1 < 2 * κ) (hδ : 0 < δ) {q : ℝ}
    (hq : N ^ (-(κ * δ)) / K ≤ q)
    (n9 : 96 * K ^ 4 ≤ N ^ (20 * s₀ - 2 * κ * δ)) :
    8 * K ^ 2 * (1 + N ^ (-δ) / q ^ 2) * N ^ (-(20 * s₀)) * (4 + 2 * K) ≤ K * N ^ (-δ) := by
  have hN0 : 0 < N := by linarith
  have hK0 : 0 < K := by linarith
  have h1 := margin_one_add hN hK hκ hδ hq
  have hg2 : 0 < N ^ (-(2 * (κ * δ))) := Real.rpow_pos_of_pos hN0 _
  have h2 := const_mul_rpow_neg_le hN0 (x := 20 * s₀) (y := 2 * κ * δ) (C := 96 * K ^ 4) n9
  have e : N ^ (-(2 * (κ * δ))) = N ^ (-(2 * κ * δ)) := by ring_nf
  rw [e] at h1 hg2
  have hσ : 0 ≤ N ^ (-(20 * s₀)) := Real.rpow_nonneg hN0.le _
  have h4K : 4 + 2 * K ≤ 6 * K := by linarith
  calc 8 * K ^ 2 * (1 + N ^ (-δ) / q ^ 2) * N ^ (-(20 * s₀)) * (4 + 2 * K)
      ≤ 8 * K ^ 2 * (2 * K ^ 2 * (N ^ (-δ) / N ^ (-(2 * κ * δ)))) * N ^ (-(20 * s₀)) *
          (6 * K) := by gcongr
    _ = K * N ^ (-δ) * (96 * K ^ 4 * N ^ (-(20 * s₀)) / N ^ (-(2 * κ * δ))) := by
        field_simp; ring
    _ ≤ K * N ^ (-δ) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [div_le_one hg2]
        exact h2
    _ = K * N ^ (-δ) := mul_one _

end Margins

end

end Submission.Obl.k4_horizontal_supercritical_three_projections
