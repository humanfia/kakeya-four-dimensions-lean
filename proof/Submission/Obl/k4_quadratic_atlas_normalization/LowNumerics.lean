import Submission.Obl.k4_quadratic_atlas_normalization.Curvature
import Submission.Obl.k4_quadratic_atlas_normalization.Thickness
import Submission.Obl.k4_quadratic_atlas_normalization.StepInterface

namespace Submission.Obl.k4_quadratic_atlas_normalization

open Set MvPolynomial

lemma curv_eq_curvature (R : MvPolynomial (Fin 4) ℝ) : curv R = curvature R 3 := by
  simp [curv, curvature, MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]

/-- Scalar form of the discriminant estimate at small curvature. -/
theorem low_scalar_derivative_floor {B δ₀ κ z c p q : ℝ}
    (hB : 0 < B) (hδ : 0 < δ₀) (hκ : 1 ≤ κ) (hz : 4 * κ ^ 2 ≤ z)
    (hc : |c| ≤ B ^ 2 / (δ₀ * z ^ 8)) (hp : |p| ≤ κ * δ₀ * z)
    (hd : B ^ 2 / (κ * z) ≤ |q ^ 2 - 2 * c * p|) : B / z ≤ |q| := by
  have hκpos : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have hz1 : 1 ≤ z := by nlinarith [sq_nonneg (κ - 1)]
  have hzpos : 0 < z := zero_lt_one.trans_le hz1
  have hz6 : 4 * κ ^ 2 ≤ z ^ 6 := by
    exact hz.trans (by simpa using pow_le_pow_right₀ hz1 (by norm_num : 1 ≤ 6))
  have h2κ : 2 * κ ≤ z := by nlinarith [sq_nonneg (κ - 1)]
  have hcp : |c * p| ≤ κ * B ^ 2 / z ^ 7 := by
    rw [abs_mul]
    calc
      _ ≤ (B ^ 2 / (δ₀ * z ^ 8)) * (κ * δ₀ * z) :=
        mul_le_mul hc hp (abs_nonneg _) (by positivity)
      _ = κ * B ^ 2 / z ^ 7 := by field_simp
  have hsmall' : 2 * (κ * B ^ 2 / z ^ 7) ≤ (B ^ 2 / (κ * z)) / 2 := by
    rw [show 2 * (κ * B ^ 2 / z ^ 7) = (2 * κ * B ^ 2) / z ^ 7 by ring,
      div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < z ^ 7) (by positivity : 0 < κ * z * 2)).mpr
    calc
      _ = (B ^ 2 * z) * (4 * κ ^ 2) := by ring
      _ ≤ (B ^ 2 * z) * z ^ 6 := mul_le_mul_of_nonneg_left hz6 (by positivity)
      _ = _ := by ring
  have hsmall : 2 * |c * p| ≤ (B ^ 2 / (κ * z)) / 2 :=
    (mul_le_mul_of_nonneg_left hcp (by norm_num)).trans hsmall'
  have hq := (low_curvature_derivative_floor (by positivity : 0 < B ^ 2 / (κ * z)) hd hsmall).2
  have hfloor : (B / z) ^ 2 ≤ (B ^ 2 / (κ * z)) / 2 := by
    rw [div_pow, div_div]
    apply (div_le_div_iff₀ (by positivity : 0 < z ^ 2) (by positivity : 0 < κ * z * 2)).mpr
    calc
      _ = (B ^ 2 * z) * (2 * κ) := by ring
      _ ≤ (B ^ 2 * z) * z := mul_le_mul_of_nonneg_left h2κ (by positivity)
      _ = _ := by ring
  apply (sq_le_sq₀ (by positivity : 0 ≤ B / z) (abs_nonneg q)).mp
  simpa only [sq_abs] using hfloor.trans hq

/-- A small-curvature rough chart has a polynomially nonzero hidden derivative. -/
theorem low_chart_derivative_witness
    {N κ j L a B : ℝ} {M D T : ℕ} {E : Set Incidence}
    {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Line} {F : Set Incidence} {ex : Prop}
    (hN : 1 ≤ N) (ha : 0 < a) (hκ : 1 ≤ κ) (hB : 0 < B)
    (hlarge : 4 * κ ^ 2 ≤ N ^ a) (hlow : lowCase N L a B R)
    (h : rough N M D κ T j L a B E c u Q R A F ex) :
    ∀ l ∈ A, N ^ (-2 * a) ≤
      derivativeMax R (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) l / B := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hδ : 0 < δ N L := by unfold δ; positivity
  rcases h with ⟨_, _, _, _, hdeg, _, _, _, _, hwhole, _, hdisc, _⟩
  intro l hl
  obtain ⟨t, ht, hdisc⟩ := hdisc l hl
  have hval := (hwhole l hl).2.2 t ht
  have hcurv : |curvature R 3| ≤ B ^ 2 / (δ N L * (N ^ a) ^ 8) := by
    rw [lowCase, curv_eq_curvature] at hlow
    convert hlow using 1
    rw [← Real.rpow_mul_natCast hNpos.le, Real.rpow_neg hNpos.le]
    field_simp
    ring
  have hd : B ^ 2 / (κ * N ^ a) ≤
      |(eval (x l t) (pderiv (3 : Fin 4) R)) ^ 2 -
        2 * curvature R 3 * eval (x l t) R| := by
    simpa only [second_pderiv_eq_curvature R hdeg 3, eval_C] using hdisc
  have hf := low_scalar_derivative_floor hB hδ hκ hlarge hcurv hval.2.1 hd
  have hfin : B * N ^ (-2 * a) ≤
      derivativeMax R (j / (2 : ℝ) ^ T) ((j + 1) / (2 : ℝ) ^ T) l := by
    calc
      _ ≤ B * N ^ (-a) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) hB.le
      _ = B / N ^ a := by rw [Real.rpow_neg hNpos.le, div_eq_mul_inv]
      _ ≤ |eval (x l t) (pderiv (3 : Fin 4) R)| := hf
      _ ≤ _ := derivative_le_max R hdeg l ht
  apply (le_div_iff₀ hB).mpr
  simpa only [mul_comm] using hfin

/-- The fixed output exponent for the low-curvature refinement. -/
noncomputable def lowOutputExponent (M : ℕ) (a : ℝ) : ℕ := M + ⌈2 * a⌉₊ + 4

lemma lowOutputExponent_ge (M : ℕ) (a : ℝ) : M ≤ lowOutputExponent M a := by
  unfold lowOutputExponent
  omega

lemma add_ten_budget {N : ℝ} (hN : 2 ≤ N) (M : ℕ) :
    N ^ M + 10 ≤ N ^ (M + 4) := by
  have hN1 : 1 ≤ N := (by norm_num : (1 : ℝ) ≤ 2).trans hN
  have hp : 1 ≤ N ^ M := one_le_pow₀ hN1
  have h4 : (16 : ℝ) ≤ N ^ 4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hN 4
    norm_num at hh
    exact hh
  calc
    _ ≤ N ^ M * 16 := by nlinarith
    _ ≤ N ^ M * N ^ 4 := mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := (pow_add _ _ _).symm

lemma low_format_budget {N : ℝ} (hN : 2 ≤ N) (M : ℕ) (a : ℝ) :
    N ^ M + 10 ≤ N ^ lowOutputExponent M a := by
  apply (add_ten_budget hN M).trans
  apply pow_le_pow_right₀ ((by norm_num : (1 : ℝ) ≤ 2).trans hN)
  unfold lowOutputExponent
  omega

lemma low_scaled_coefficient_budget {N a v : ℝ} (hN : 1 ≤ N)
    (hv : N ^ (-2 * a) ≤ v) (M : ℕ) :
    N ^ M / v ≤ N ^ lowOutputExponent M a := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hp : 0 < N ^ (-2 * a) := Real.rpow_pos_of_pos hNpos _
  calc
    _ ≤ N ^ M / N ^ (-2 * a) := div_le_div_of_nonneg_left (by positivity) hp hv
    _ = N ^ ((M : ℝ) + 2 * a) := by
      rw [← Real.rpow_natCast N M, ← Real.rpow_sub hNpos]
      congr 1
      ring
    _ ≤ N ^ ((M : ℝ) + (⌈2 * a⌉₊ : ℝ) + 4) := by
      apply Real.rpow_le_rpow_of_exponent_le hN
      have h := Nat.le_ceil (2 * a)
      linarith
    _ = N ^ lowOutputExponent M a := by
      rw [lowOutputExponent, ← Real.rpow_natCast]
      congr 1
      push_cast
      ring

lemma low_scaled_thickness_bound {N a v : ℝ} (hN : 1 ≤ N)
    (hNa : 2 ≤ N ^ a) (hv : N ^ (-2 * a) ≤ v) (L : ℝ) :
    δ N L * N ^ a / v ≤ δ N (L - 4 * a) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hp : 0 < N ^ (-2 * a) := Real.rpow_pos_of_pos hNpos _
  calc
    _ ≤ δ N L * N ^ a / N ^ (-2 * a) := by
      apply div_le_div_of_nonneg_left _ hp hv
      unfold δ
      positivity
    _ = δ N L * N ^ (3 * a) := by
      rw [mul_div_assoc, ← Real.rpow_sub hNpos]
      congr 2
      ring
    _ ≤ δ N (L - 4 * a) := by
      convert delta_absorb_power hNpos hNa L (3 * a) using 1 <;> congr 1 <;> ring

lemma low_scaled_curvature_bound {N a B v L : ℝ} (hN : 1 ≤ N) (ha : 0 ≤ a)
    (hNa : 2 ≤ N ^ a) (hv : N ^ (-2 * a) ≤ v)
    (R : MvPolynomial (Fin 4) ℝ) (hlow : lowCase N L a B R) :
    |curvature R 3| / v ≤ B ^ 2 / δ N (L - 4 * a) := by
  have hNpos : 0 < N := zero_lt_one.trans_le hN
  have hp : 0 < N ^ (-2 * a) := Real.rpow_pos_of_pos hNpos _
  have hvpos : 0 < v := hp.trans_le hv
  have hδ : 0 < δ N L := by unfold δ; positivity
  have hδr : 0 < δ N (L - 4 * a) := by unfold δ; positivity
  have hpow : 2 ≤ N ^ (2 * a) := hNa.trans
    (Real.rpow_le_rpow_of_exponent_le hN (by linarith))
  have hδup : δ N (L - 4 * a) ≤ δ N L * N ^ (6 * a) := by
    calc
      _ ≤ 2 * δ N L * N ^ (4 * a) := delta_shift_upper hNpos L (4 * a)
      _ ≤ N ^ (2 * a) * δ N L * N ^ (4 * a) := by gcongr
      _ = δ N L * N ^ (6 * a) := by
        rw [mul_comm (N ^ (2 * a)), mul_assoc, ← Real.rpow_add hNpos]
        congr 2
        ring
  have hc : |curvature R 3| ≤ B ^ 2 * N ^ (-(8 * a)) / δ N L := by
    simpa only [lowCase, curv_eq_curvature] using hlow
  apply (div_le_div_iff₀ hvpos hδr).mpr
  calc
    _ ≤ (B ^ 2 * N ^ (-(8 * a)) / δ N L) * (δ N L * N ^ (6 * a)) :=
      mul_le_mul hc hδup hδr.le (by positivity)
    _ = B ^ 2 * (N ^ (-(8 * a)) * N ^ (6 * a)) := by field_simp
    _ = B ^ 2 * N ^ (-2 * a) := by
      rw [← Real.rpow_add hNpos]
      congr 2
      ring
    _ ≤ B ^ 2 * v := mul_le_mul_of_nonneg_left hv (sq_nonneg _)

end Submission.Obl.k4_quadratic_atlas_normalization
