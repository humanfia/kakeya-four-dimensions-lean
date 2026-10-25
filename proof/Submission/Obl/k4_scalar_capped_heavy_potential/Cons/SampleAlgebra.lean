import Mathlib

/-!
# Real-number estimates for one sample

The parameter choices of the conservativity step at one sample, and the
elementary inequalities between them: switch errors, the enlarged cell
radius, the height tolerance, and the final residual variation.
Throughout `X = N_k ≥ 2`, `Y = H_k ≥ 1` and `X^{-κ}/Y ≤ h ≤ 1`.
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

/-- A fixed polynomial of `Y` below a fixed power of `X`, obtained from one big
comparison. -/
theorem cond_of_big {X Y Cb c η γ : ℝ} {mb n : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hc0 : 0 ≤ c)
    (hc : c ≤ Cb) (hn : n ≤ mb) (hη : η ≤ γ) (hbig : Cb * Y ^ mb ≤ X ^ η) :
    c * Y ^ n ≤ X ^ γ := by
  have hY0 : 0 ≤ Y := by linarith
  calc
    c * Y ^ n ≤ Cb * Y ^ mb :=
      mul_le_mul hc (pow_le_pow_right₀ hY hn) (pow_nonneg hY0 _) (hc0.trans hc)
    _ ≤ X ^ η := hbig
    _ ≤ X ^ γ := Real.rpow_le_rpow_of_exponent_le hX hη

theorem switch_error_le {X Y h κ B Z lam : ℝ} (hX : 2 ≤ X) (hY : 1 ≤ Y) (hh : 0 < h)
    (hhlo : X ^ (-κ) / Y ≤ h) (hlam : 1 ≤ lam) (ha : 5 * Y ^ 2 ≤ X ^ (B - κ - Z - 1)) :
    max ((Y + 1) * X ^ (-B) / (h * lam)) ((4 * Y + 1) * X ^ (-B) / h) ≤ X ^ (-(Z + 1)) := by
  have hX0 : 0 < X := by linarith
  have hY0 : 0 < Y := by linarith
  have hδs : 0 < X ^ (-B) := Real.rpow_pos_of_pos hX0 _
  -- 1/h ≤ Y X^κ
  have hinv : 1 / h ≤ Y * X ^ κ := by
    rw [div_le_iff₀ hh]
    have h1 : X ^ (-κ) = (X ^ κ)⁻¹ := Real.rpow_neg hX0.le κ
    have hXk : 0 < X ^ κ := Real.rpow_pos_of_pos hX0 _
    rw [h1, inv_div_left] at hhlo
    have : 1 ≤ h * (Y * X ^ κ) := by
      have h2 := mul_le_mul_of_nonneg_right hhlo (le_of_lt (mul_pos hY0 hXk))
      rwa [inv_mul_cancel₀ (ne_of_gt (mul_pos hY0 hXk))] at h2
    linarith
  have hsecond : (4 * Y + 1) * X ^ (-B) / h ≤ X ^ (-(Z + 1)) := by
    calc
      (4 * Y + 1) * X ^ (-B) / h = (4 * Y + 1) * X ^ (-B) * (1 / h) := by ring
      _ ≤ (5 * Y) * X ^ (-B) * (Y * X ^ κ) := by
        apply mul_le_mul _ hinv (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith) hδs.le
      _ = 5 * Y ^ 2 * X ^ (κ - B) := by
        rw [show κ - B = -B + κ by ring, Real.rpow_add hX0]
        ring
      _ ≤ X ^ (B - κ - Z - 1) * X ^ (κ - B) :=
        mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg hX0.le _)
      _ = X ^ (-(Z + 1)) := by
        rw [← Real.rpow_add hX0]
        ring_nf
  apply max_le _ hsecond
  refine le_trans ?_ hsecond
  rw [div_le_div_iff₀ (mul_pos hh (by linarith)) hh]
  have : (Y + 1) * X ^ (-B) * h ≤ (4 * Y + 1) * X ^ (-B) * (h * lam) := by
    have h1 : (Y + 1) * X ^ (-B) ≤ (4 * Y + 1) * X ^ (-B) :=
      mul_le_mul_of_nonneg_right (by linarith) hδs.le
    have h2 : h ≤ h * lam := le_mul_of_one_le_right hh.le hlam
    calc
      (Y + 1) * X ^ (-B) * h ≤ (4 * Y + 1) * X ^ (-B) * h :=
        mul_le_mul_of_nonneg_right h1 hh.le
      _ ≤ (4 * Y + 1) * X ^ (-B) * (h * lam) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
  linarith

/-- `h εT` is a power below `N^{-1}`. -/
theorem h_mul_epsT_le {X Y h κ cs : ℝ} (hX0 : 0 < X) (hY1 : 1 ≤ Y) (hh0 : 0 < h)
    (hhhi : h ≤ Y * X ^ (-κ)) (hF1 : 3 * Y ^ 2 ≤ X ^ (κ / 4 - 2 * cs)) :
    h * (Y * X ^ (-1 : ℝ) * h ^ (-(3 : ℝ) / 4)) ≤ X ^ (-1 - 2 * cs) / 3 := by
  have hY0 : 0 < Y := by linarith
  have hpow : h * h ^ (-(3 : ℝ) / 4) = h ^ ((1 : ℝ) / 4) := by
    have h1 := Real.rpow_add hh0 (1 : ℝ) (-(3 : ℝ) / 4)
    rw [Real.rpow_one] at h1
    rw [← h1]
    congr 1
    norm_num
  have hq : h ^ ((1 : ℝ) / 4) ≤ Y * X ^ (-κ / 4) := by
    calc
      h ^ ((1 : ℝ) / 4) ≤ (Y * X ^ (-κ)) ^ ((1 : ℝ) / 4) :=
        Real.rpow_le_rpow hh0.le hhhi (by norm_num)
      _ = Y ^ ((1 : ℝ) / 4) * X ^ (-κ / 4) := by
        rw [Real.mul_rpow hY0.le (Real.rpow_nonneg hX0.le _), ← Real.rpow_mul hX0.le]
        ring_nf
      _ ≤ Y * X ^ (-κ / 4) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX0.le _)
        calc
          Y ^ ((1 : ℝ) / 4) ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
          _ = Y := Real.rpow_one Y
  have hXm : 0 < X ^ (-1 : ℝ) := Real.rpow_pos_of_pos hX0 _
  calc
    h * (Y * X ^ (-1 : ℝ) * h ^ (-(3 : ℝ) / 4)) = Y * X ^ (-1 : ℝ) * (h * h ^ (-(3 : ℝ) / 4)) := by
      ring
    _ = Y * X ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 4) := by rw [hpow]
    _ ≤ Y * X ^ (-1 : ℝ) * (Y * X ^ (-κ / 4)) :=
      mul_le_mul_of_nonneg_left hq (by positivity)
    _ = (3 * Y ^ 2) * (X ^ (-1 : ℝ) * X ^ (-κ / 4)) / 3 := by ring
    _ ≤ X ^ (κ / 4 - 2 * cs) * (X ^ (-1 : ℝ) * X ^ (-κ / 4)) / 3 := by
      gcongr
    _ = X ^ (-1 - 2 * cs) / 3 := by
      rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
      ring_nf

/-- The base-cell budget times the enlarged cell area. -/
theorem Jb_area_le {X Y h d Z ξ lam ρE w₁ : ℝ} (hX0 : 0 < X) (hY1 : 1 ≤ Y) (hh0 : 0 < h)
    (hξ : ξ = X ^ (-Z)) (hlam : lam = 2 * Y) (hρ0 : 0 ≤ ρE) (hρ : ρE ≤ ξ / lam)
    (hw : w₁ = X ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8)) :
    Y * X ^ (2 * Z) * (X ^ (-1 : ℝ) / w₁) ^ d * (2 * ρE) ^ 2 ≤ h ^ (-d / 8) := by
  have hY0 : 0 < Y := by linarith
  have hXm : 0 < X ^ (-1 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hh8 : 0 < h ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hh0 _
  have hratio : (X ^ (-1 : ℝ) / w₁) ^ d = h ^ (-d / 8) := by
    rw [hw, div_mul_cancel_left₀ hXm.ne', ← Real.rpow_neg_one, ← Real.rpow_mul hh0.le,
      ← Real.rpow_mul hh0.le]
    ring_nf
  have harea : (2 * ρE) ^ 2 ≤ X ^ (-2 * Z) / Y ^ 2 := by
    have h1 : 2 * ρE ≤ ξ / Y := by
      rw [hlam] at hρ
      have : ξ / (2 * Y) * 2 = ξ / Y := by field_simp
      linarith
    calc
      (2 * ρE) ^ 2 ≤ (ξ / Y) ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
      _ = X ^ (-2 * Z) / Y ^ 2 := by
        rw [div_pow, hξ, ← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
        congr 2
        push_cast
        ring
  have hXZ : X ^ (2 * Z) * X ^ (-2 * Z) = 1 := by
    rw [← Real.rpow_add hX0]
    simp
  have hhd : 0 < h ^ (-d / 8) := Real.rpow_pos_of_pos hh0 _
  calc
    Y * X ^ (2 * Z) * (X ^ (-1 : ℝ) / w₁) ^ d * (2 * ρE) ^ 2 ≤
        Y * X ^ (2 * Z) * h ^ (-d / 8) * (X ^ (-2 * Z) / Y ^ 2) := by
      rw [hratio]
      gcongr
    _ = h ^ (-d / 8) / Y * (X ^ (2 * Z) * X ^ (-2 * Z)) := by
      field_simp
    _ ≤ h ^ (-d / 8) := by
      rw [hXZ, mul_one]
      exact div_le_self hhd.le hY1

theorem rpow_le_mul_rpow {X Y h κ q : ℝ} (hX0 : 0 < X) (hY1 : 1 ≤ Y) (hh0 : 0 < h)
    (hhhi : h ≤ Y * X ^ (-κ)) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    h ^ q ≤ Y * X ^ (-(κ * q)) := by
  have hY0 : 0 < Y := by linarith
  calc
    h ^ q ≤ (Y * X ^ (-κ)) ^ q := Real.rpow_le_rpow hh0.le hhhi hq0
    _ = Y ^ q * X ^ (-(κ * q)) := by
      rw [Real.mul_rpow hY0.le (Real.rpow_nonneg hX0.le _), ← Real.rpow_mul hX0.le]
      ring_nf
    _ ≤ Y * X ^ (-(κ * q)) := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX0.le _)
      calc
        Y ^ q ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY1 hq1
        _ = Y := Real.rpow_one Y

/-- The height tolerance is at most one hidden-coordinate bin in units of `h`. -/
theorem epsilon_le {X Y h κ Z b C K cK bsw δv εT w₁ lam : ℝ} {D : ℕ} (hX0 : 0 < X)
    (hY1 : 1 ≤ Y) (hh0 : 0 < h) (hh1 : h ≤ 1) (hhhi : h ≤ Y * X ^ (-κ))
    (hlam : lam = 2 * Y) (hεT : εT = Y * X ^ (-1 : ℝ) * h ^ (-(3 : ℝ) / 4))
    (hw : w₁ = X ^ (-1 : ℝ) * h ^ ((1 : ℝ) / 8))
    (hbsw0 : 0 ≤ bsw) (hbsw : bsw ≤ δv) (hδv : δv = X ^ (-(Z + 1)))
    (hK1 : 1 ≤ K) (hK : K ≤ cK * Y ^ (D + 2) * X ^ b) (hC : 0 ≤ C) (hcK : 0 ≤ cK)
    (cd : 64 * Y ^ 3 ≤ X ^ (κ / 8))
    (ce : (768 * C * cK ^ 2) * Y ^ (2 * D + 4) ≤ X ^ (Z - 2 * b))
    (cf : (16 * cK) * Y ^ (D + 2) ≤ X ^ (Z - b)) (cg : 32 * Y ^ 0 ≤ X ^ Z) :
    w₁ / (2 * h) + (4 * (lam * εT + (1 + K) * (2 * C * K) * (4 * bsw + 4 * (δv / 2)) +
      K * (δv / 2)) + 3 * bsw) + bsw ≤ w₁ / h := by
  have hY0 : 0 < Y := by linarith
  have hXm : 0 < X ^ (-1 : ℝ) := Real.rpow_pos_of_pos hX0 _
  -- the unit `U = X^{-1}/8`, with `U ≤ w₁/(2h)/4`
  set U := X ^ (-1 : ℝ) / 8 with hUdef
  have hW : 4 * U ≤ w₁ / (2 * h) := by
    have h78 : 1 ≤ h ^ (-(7 : ℝ) / 8) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh0 hh1 (by norm_num)
    have heq : w₁ / (2 * h) = X ^ (-1 : ℝ) * h ^ (-(7 : ℝ) / 8) / 2 := by
      rw [hw]
      have h1 := Real.rpow_add hh0 ((1 : ℝ) / 8) (-1)
      rw [Real.rpow_neg_one] at h1
      rw [show (1 : ℝ) / 8 + -1 = -(7 : ℝ) / 8 by norm_num] at h1
      rw [h1]
      field_simp
    rw [heq, hUdef]
    nlinarith
  -- the δv-sized terms
  have hδvX : δv * X ^ Z = X ^ (-1 : ℝ) := by
    rw [hδv, ← Real.rpow_add hX0]
    ring_nf
  have hXZ0 : 0 < X ^ Z := Real.rpow_pos_of_pos hX0 _
  have hδv0 : 0 ≤ δv := by rw [hδv]; exact Real.rpow_nonneg hX0.le _
  have hT4 : 4 * bsw ≤ U := by
    have : 4 * δv ≤ U := by
      have h1 : 4 * δv * 32 ≤ 4 * δv * X ^ Z := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        simpa using cg
      have h2 : 4 * δv * X ^ Z = 4 * X ^ (-1 : ℝ) := by rw [mul_assoc, hδvX]
      rw [hUdef]
      nlinarith
    linarith
  have hKX : K * X ^ (-b) ≤ cK * Y ^ (D + 2) := by
    have hXb : X ^ b * X ^ (-b) = 1 := by rw [← Real.rpow_add hX0]; simp
    calc
      K * X ^ (-b) ≤ cK * Y ^ (D + 2) * X ^ b * X ^ (-b) :=
        mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hX0.le _)
      _ = cK * Y ^ (D + 2) := by rw [mul_assoc, hXb, mul_one]
  have hT3 : 4 * (K * (δv / 2)) ≤ U := by
    -- `2 K δv ≤ 2 cK Y^{D+2} X^b X^{-Z-1} ≤ X^{-1}/8`
    have h1 : K * δv * X ^ (Z - b) ≤ cK * Y ^ (D + 2) * X ^ (-1 : ℝ) := by
      have : K * δv * X ^ (Z - b) = (K * X ^ (-b)) * (δv * X ^ Z) := by
        rw [show Z - b = -b + Z by ring, Real.rpow_add hX0]
        ring
      rw [this, hδvX]
      exact mul_le_mul_of_nonneg_right hKX hXm.le
    have h2 : 16 * (K * δv) * X ^ (Z - b) ≤ X ^ (Z - b) * X ^ (-1 : ℝ) := by
      calc
        16 * (K * δv) * X ^ (Z - b) = 16 * (K * δv * X ^ (Z - b)) := by ring
        _ ≤ 16 * (cK * Y ^ (D + 2) * X ^ (-1 : ℝ)) := by linarith
        _ = (16 * cK) * Y ^ (D + 2) * X ^ (-1 : ℝ) := by ring
        _ ≤ X ^ (Z - b) * X ^ (-1 : ℝ) := mul_le_mul_of_nonneg_right cf hXm.le
    have hXZb : 0 < X ^ (Z - b) := Real.rpow_pos_of_pos hX0 _
    have h3 : 16 * (K * δv) ≤ X ^ (-1 : ℝ) := by
      have := h2
      rw [mul_comm (X ^ (Z - b)) _] at this
      exact le_of_mul_le_mul_right this hXZb
    rw [hUdef]
    linarith
  have hT2 : 4 * ((1 + K) * (2 * C * K) * (4 * bsw + 4 * (δv / 2))) ≤ U := by
    have hsw : 4 * bsw + 4 * (δv / 2) ≤ 6 * δv := by linarith
    have hK0 : 0 ≤ K := by linarith
    have h1 : (1 + K) * (2 * C * K) * (4 * bsw + 4 * (δv / 2)) ≤ 24 * C * K ^ 2 * δv := by
      have hA : (1 + K) * (2 * C * K) ≤ 4 * C * K ^ 2 := by
        have h0 : 0 ≤ 2 * C * K * (K - 1) :=
          mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) hK0) (by linarith)
        have hid : 4 * C * K ^ 2 - (1 + K) * (2 * C * K) = 2 * C * K * (K - 1) := by ring
        linarith
      calc
        (1 + K) * (2 * C * K) * (4 * bsw + 4 * (δv / 2)) ≤ (4 * C * K ^ 2) * (6 * δv) :=
          mul_le_mul hA hsw (by positivity) (by positivity)
        _ = 24 * C * K ^ 2 * δv := by ring
    have hK2 : K ^ 2 * X ^ (-2 * b) ≤ cK ^ 2 * Y ^ (2 * D + 4) := by
      have hsq : (X ^ (-b)) ^ 2 = X ^ (-2 * b) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
        norm_num
        ring_nf
      have : K ^ 2 * X ^ (-2 * b) = (K * X ^ (-b)) ^ 2 := by
        rw [mul_pow, hsq]
      rw [this, show 2 * D + 4 = (D + 2) * 2 by ring, pow_mul, ← mul_pow]
      exact pow_le_pow_left₀ (by positivity) hKX 2
    have h2 : 96 * C * K ^ 2 * δv * X ^ (Z - 2 * b) ≤
        (768 * C * cK ^ 2) * Y ^ (2 * D + 4) * X ^ (-1 : ℝ) / 8 := by
      have : 96 * C * K ^ 2 * δv * X ^ (Z - 2 * b) =
          96 * C * (K ^ 2 * X ^ (-2 * b)) * (δv * X ^ Z) := by
        rw [show Z - 2 * b = -2 * b + Z by ring, Real.rpow_add hX0]
        ring
      rw [this, hδvX]
      have := mul_le_mul_of_nonneg_left hK2 (by positivity : (0 : ℝ) ≤ 96 * C)
      nlinarith [hXm]
    have h3 : 96 * C * K ^ 2 * δv * X ^ (Z - 2 * b) ≤ X ^ (Z - 2 * b) * X ^ (-1 : ℝ) / 8 := by
      have := mul_le_mul_of_nonneg_right ce hXm.le
      linarith
    have hXZb : 0 < X ^ (Z - 2 * b) := Real.rpow_pos_of_pos hX0 _
    have h4 : 96 * C * K ^ 2 * δv ≤ X ^ (-1 : ℝ) / 8 := by
      have h5 : 96 * C * K ^ 2 * δv * X ^ (Z - 2 * b) ≤ X ^ (-1 : ℝ) / 8 * X ^ (Z - 2 * b) := by
        linarith
      exact le_of_mul_le_mul_right h5 hXZb
    rw [hUdef]
    linarith
  have hT1 : 4 * (lam * εT) ≤ U * h ^ (-(7 : ℝ) / 8) := by
    have h18 := rpow_le_mul_rpow hX0 hY1 hh0 hhhi (q := (1 : ℝ) / 8) (by norm_num) (by norm_num)
    have hsplit : h ^ (-(3 : ℝ) / 4) = h ^ ((1 : ℝ) / 8) * h ^ (-(7 : ℝ) / 8) := by
      rw [← Real.rpow_add hh0]
      norm_num
    have h78 : 0 < h ^ (-(7 : ℝ) / 8) := Real.rpow_pos_of_pos hh0 _
    have hcd : 64 * Y ^ 2 * h ^ ((1 : ℝ) / 8) ≤ 1 := by
      have hk : X ^ (-(κ * (1 / 8))) = (X ^ (κ / 8))⁻¹ := by
        rw [← Real.rpow_neg hX0.le]
        ring_nf
      have hpos : 0 < X ^ (κ / 8) := Real.rpow_pos_of_pos hX0 _
      calc
        64 * Y ^ 2 * h ^ ((1 : ℝ) / 8) ≤ 64 * Y ^ 2 * (Y * X ^ (-(κ * (1 / 8)))) :=
          mul_le_mul_of_nonneg_left h18 (by positivity)
        _ = 64 * Y ^ 3 / X ^ (κ / 8) := by rw [hk]; ring
        _ ≤ 1 := by rw [div_le_one hpos]; exact cd
    rw [hlam, hεT, hsplit, hUdef]
    have : 4 * (2 * Y * (Y * X ^ (-1 : ℝ) * (h ^ ((1 : ℝ) / 8) * h ^ (-(7 : ℝ) / 8)))) =
        (64 * Y ^ 2 * h ^ ((1 : ℝ) / 8)) * (X ^ (-1 : ℝ) / 8 * h ^ (-(7 : ℝ) / 8)) := by ring
    rw [this]
    have hpos : 0 ≤ X ^ (-1 : ℝ) / 8 * h ^ (-(7 : ℝ) / 8) := by positivity
    calc
      (64 * Y ^ 2 * h ^ ((1 : ℝ) / 8)) * (X ^ (-1 : ℝ) / 8 * h ^ (-(7 : ℝ) / 8)) ≤
          1 * (X ^ (-1 : ℝ) / 8 * h ^ (-(7 : ℝ) / 8)) := mul_le_mul_of_nonneg_right hcd hpos
      _ = X ^ (-1 : ℝ) / 8 * h ^ (-(7 : ℝ) / 8) := one_mul _
  -- assemble: each of the four terms is below `w₁/(2h)/4`
  have h78 : 1 ≤ h ^ (-(7 : ℝ) / 8) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hh0 hh1 (by norm_num)
  have hU0 : 0 ≤ U := by positivity
  have hUh : U ≤ U * h ^ (-(7 : ℝ) / 8) := le_mul_of_one_le_right hU0 h78
  have hWh : 4 * (U * h ^ (-(7 : ℝ) / 8)) ≤ w₁ / (2 * h) := by
    have heq : w₁ / (2 * h) = X ^ (-1 : ℝ) * h ^ (-(7 : ℝ) / 8) / 2 := by
      rw [hw]
      have h1 := Real.rpow_add hh0 ((1 : ℝ) / 8) (-1)
      rw [Real.rpow_neg_one] at h1
      rw [show (1 : ℝ) / 8 + -1 = -(7 : ℝ) / 8 by norm_num] at h1
      rw [h1]
      field_simp
    rw [heq, hUdef]
    apply le_of_eq
    ring
  have hsum : 4 * (lam * εT + (1 + K) * (2 * C * K) * (4 * bsw + 4 * (δv / 2)) +
      K * (δv / 2)) + 3 * bsw + bsw ≤ w₁ / (2 * h) := by
    linarith [hT1, hT2, hT3, hT4, hUh, hWh]
  have heq2 : w₁ / h = w₁ / (2 * h) + w₁ / (2 * h) := by
    field_simp
    ring
  rw [heq2]
  linarith

/-- The final residual variation from the block curl bound. -/
theorem final_variation_le {X Y h κ d b cs Z Ccurl cK K L M JA ε KP ξl lam A₁ A₂ : ℝ}
    {D n₁ n₂ : ℕ} (hX0 : 0 < X) (hY1 : 1 ≤ Y) (hh0 : 0 < h) (hh1 : h ≤ 1)
    (hhhi : h ≤ Y * X ^ (-κ)) (hd0 : 0 ≤ d) (hd1 : d < 1) (hC : 0 ≤ Ccurl) (hcK : 0 ≤ cK)
    (hK0 : 0 ≤ K) (hK : K ≤ cK * Y ^ (D + 2) * X ^ b)
    (hL : L = 2 ^ 28 * Y ^ 16) (hM : M = 4 * Y ^ 4)
    (hJA0 : 0 ≤ JA) (hJA : JA ≤ h ^ (-d / 8)) (hε0 : 0 ≤ ε)
    (hε : ε ≤ X ^ (-1 : ℝ) * h ^ (-(7 : ℝ) / 8))
    (hKP : KP = 2 ^ (D + 2) * ((((D + 1) ^ 2 : ℕ) : ℝ) * (2 * ((D : ℝ) + 1))) * Y ^ (D + 3))
    (hξl0 : 0 ≤ ξl) (hξl : ξl ≤ X ^ (-Z)) (hlam : 1 ≤ lam)
    (hA₁ : A₁ = Ccurl * cK ^ 4 * ((2 : ℝ) ^ 28) ^ (6 * D + 1) * (4 : ℝ) ^ (2 * D) *
      (2 : ℝ) ^ (6 * D + 1))
    (hn₁ : n₁ = 4 * (D + 2) + 16 * (6 * D + 1) + 4 * (2 * D))
    (hA₂ : A₂ = Ccurl * ((2 : ℝ) ^ (D + 2) * ((((D + 1) ^ 2 : ℕ) : ℝ) * (2 * ((D : ℝ) + 1)))) *
      ((2 : ℝ) ^ 28) ^ (2 * D) * (4 : ℝ) ^ (2 * D) * (2 : ℝ) ^ (2 * D))
    (hn₂ : n₂ = (D + 3) + 16 * (2 * D) + 4 * (2 * D))
    (cF2 : (3 * ((D : ℝ) + 1) ^ 2 * A₁) * Y ^ (n₁ + 1) ≤ X ^ (κ * (1 - d) / 8 - 4 * b - 2 * cs))
    (cF3 : (3 * ((D : ℝ) + 1) ^ 2 * A₂) * Y ^ n₂ ≤ X ^ (Z - 1 - 2 * cs)) :
    h * ((((D + 1) ^ 2 : ℕ) : ℝ) * (Ccurl * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * JA * ε /
      (1 / 2) ^ (6 * D + 1) + Ccurl * KP * ξl * L ^ (2 * D) * M ^ (2 * D) / (1 / 2) ^ (2 * D)) /
        lam) ≤ 2 * (X ^ (-1 - 2 * cs) / 3) := by
  have hY0 : 0 < Y := by linarith
  have hXb : 0 < X ^ b := Real.rpow_pos_of_pos hX0 _
  have hXm : 0 < X ^ (-1 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hD1 : (((D + 1) ^ 2 : ℕ) : ℝ) = ((D : ℝ) + 1) ^ 2 := by push_cast; ring
  have hL0 : 0 ≤ L := by rw [hL]; positivity
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have hKP0 : 0 ≤ KP := by rw [hKP]; positivity
  set E1 := Ccurl * K ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) * JA * ε / (1 / 2) ^ (6 * D + 1)
    with hE1def
  set E2 := Ccurl * KP * ξl * L ^ (2 * D) * M ^ (2 * D) / (1 / 2) ^ (2 * D) with hE2def
  have hE10 : 0 ≤ E1 := by positivity
  have hE20 : 0 ≤ E2 := by positivity
  -- the first term
  have hX4b : (X ^ b) ^ 4 = X ^ (4 * b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
    norm_num
    ring_nf
  have hE1 : E1 ≤ A₁ * Y ^ n₁ * X ^ (4 * b) * X ^ (-1 : ℝ) * (h ^ (-d / 8) * h ^ (-(7 : ℝ) / 8)) := by
    have h1 : E1 ≤ Ccurl * (cK * Y ^ (D + 2) * X ^ b) ^ 4 * L ^ (6 * D + 1) * M ^ (2 * D) *
        h ^ (-d / 8) * (X ^ (-1 : ℝ) * h ^ (-(7 : ℝ) / 8)) / (1 / 2) ^ (6 * D + 1) := by
      rw [hE1def]
      gcongr
    refine h1.trans (le_of_eq ?_)
    rw [hL, hM, hA₁, hn₁, mul_pow, mul_pow, hX4b, one_div_pow]
    field_simp
    ring
  have hpow : h * (h ^ (-d / 8) * h ^ (-(7 : ℝ) / 8)) = h ^ ((1 - d) / 8) := by
    rw [← Real.rpow_add hh0]
    have h1 := Real.rpow_add hh0 (1 : ℝ) (-d / 8 + -(7 : ℝ) / 8)
    rw [Real.rpow_one] at h1
    rw [← h1]
    congr 1
    ring
  have hq := rpow_le_mul_rpow hX0 hY1 hh0 hhhi (q := (1 - d) / 8) (by linarith) (by linarith)
  have hhE1 : h * E1 ≤ A₁ * Y ^ (n₁ + 1) * X ^ (4 * b - κ * (1 - d) / 8 - 1) := by
    calc
      h * E1 ≤ h * (A₁ * Y ^ n₁ * X ^ (4 * b) * X ^ (-1 : ℝ) *
          (h ^ (-d / 8) * h ^ (-(7 : ℝ) / 8))) := mul_le_mul_of_nonneg_left hE1 hh0.le
      _ = A₁ * Y ^ n₁ * X ^ (4 * b) * X ^ (-1 : ℝ) * h ^ ((1 - d) / 8) := by
        rw [← hpow]; ring
      _ ≤ A₁ * Y ^ n₁ * X ^ (4 * b) * X ^ (-1 : ℝ) * (Y * X ^ (-(κ * ((1 - d) / 8)))) := by
        apply mul_le_mul_of_nonneg_left hq
        rw [hA₁]; positivity
      _ = A₁ * Y ^ (n₁ + 1) * X ^ (4 * b - κ * (1 - d) / 8 - 1) := by
        rw [pow_succ, show 4 * b - κ * (1 - d) / 8 - 1 = 4 * b + (-1) + (-(κ * ((1 - d) / 8))) by ring,
          Real.rpow_add hX0, Real.rpow_add hX0]
        ring
  have hF2 : ((D : ℝ) + 1) ^ 2 * (h * E1) ≤ X ^ (-1 - 2 * cs) / 3 := by
    have h1 : ((D : ℝ) + 1) ^ 2 * (h * E1) ≤
        ((D : ℝ) + 1) ^ 2 * (A₁ * Y ^ (n₁ + 1) * X ^ (4 * b - κ * (1 - d) / 8 - 1)) :=
      mul_le_mul_of_nonneg_left hhE1 (by positivity)
    have h2 : (3 * ((D : ℝ) + 1) ^ 2 * A₁) * Y ^ (n₁ + 1) * X ^ (4 * b - κ * (1 - d) / 8 - 1) ≤
        X ^ (κ * (1 - d) / 8 - 4 * b - 2 * cs) * X ^ (4 * b - κ * (1 - d) / 8 - 1) :=
      mul_le_mul_of_nonneg_right cF2 (Real.rpow_nonneg hX0.le _)
    have h3 : X ^ (κ * (1 - d) / 8 - 4 * b - 2 * cs) * X ^ (4 * b - κ * (1 - d) / 8 - 1) =
        X ^ (-1 - 2 * cs) := by
      rw [← Real.rpow_add hX0]; ring_nf
    rw [h3] at h2
    linarith
  -- the second term
  have hE2 : E2 ≤ A₂ * Y ^ n₂ * X ^ (-Z) := by
    have h1 : E2 ≤ Ccurl * KP * X ^ (-Z) * L ^ (2 * D) * M ^ (2 * D) / (1 / 2) ^ (2 * D) := by
      rw [hE2def]; gcongr
    refine h1.trans (le_of_eq ?_)
    rw [hL, hM, hKP, hA₂, hn₂, mul_pow, mul_pow, one_div_pow]
    field_simp
    ring
  have hF3 : ((D : ℝ) + 1) ^ 2 * (h * E2) ≤ X ^ (-1 - 2 * cs) / 3 := by
    have h0 : h * E2 ≤ E2 := mul_le_of_le_one_left hE20 hh1
    have h1 : ((D : ℝ) + 1) ^ 2 * (h * E2) ≤ ((D : ℝ) + 1) ^ 2 * (A₂ * Y ^ n₂ * X ^ (-Z)) :=
      mul_le_mul_of_nonneg_left (h0.trans hE2) (by positivity)
    have h2 : (3 * ((D : ℝ) + 1) ^ 2 * A₂) * Y ^ n₂ * X ^ (-Z) ≤ X ^ (Z - 1 - 2 * cs) * X ^ (-Z) :=
      mul_le_mul_of_nonneg_right cF3 (Real.rpow_nonneg hX0.le _)
    have h3 : X ^ (Z - 1 - 2 * cs) * X ^ (-Z) = X ^ (-1 - 2 * cs) := by
      rw [← Real.rpow_add hX0]; ring_nf
    rw [h3] at h2
    linarith
  -- combine
  rw [hD1]
  have hdiv : ((D : ℝ) + 1) ^ 2 * (E1 + E2) / lam ≤ ((D : ℝ) + 1) ^ 2 * (E1 + E2) :=
    div_le_self (by positivity) hlam
  calc
    h * (((D : ℝ) + 1) ^ 2 * (E1 + E2) / lam) ≤ h * (((D : ℝ) + 1) ^ 2 * (E1 + E2)) :=
      mul_le_mul_of_nonneg_left hdiv hh0.le
    _ = ((D : ℝ) + 1) ^ 2 * (h * E1) + ((D : ℝ) + 1) ^ 2 * (h * E2) := by ring
    _ ≤ X ^ (-1 - 2 * cs) / 3 + X ^ (-1 - 2 * cs) / 3 := add_le_add hF2 hF3
    _ = 2 * (X ^ (-1 - 2 * cs) / 3) := by ring

theorem rhoE_le {X Y Z δv ξ lam bsw : ℝ} (hX0 : 0 < X) (hY0 : 0 < Y)
    (hδv : δv = X ^ (-(Z + 1))) (hξ : ξ = X ^ (-Z)) (hlam : lam = 2 * Y) (hbsw : bsw ≤ δv)
    (hX24 : 24 * Y ≤ X) : ξ / (2 * lam) + (4 * bsw + 4 * (δv / 2)) ≤ ξ / lam := by
  have hδvξX : δv * X = ξ := by
    have h1 : δv * X = X ^ (-(Z + 1)) * X ^ (1 : ℝ) := by rw [Real.rpow_one, hδv]
    rw [h1, ← Real.rpow_add hX0, hξ]
    ring_nf
  have hδv0 : 0 ≤ δv := by rw [hδv]; exact Real.rpow_nonneg hX0.le _
  have h6 : 6 * δv ≤ ξ / (4 * Y) := by
    rw [le_div_iff₀ (by positivity)]
    have : 6 * δv * (4 * Y) ≤ δv * X := by
      have := mul_le_mul_of_nonneg_left hX24 hδv0
      linarith
    linarith
  rw [hlam]
  have e1 : ξ / (2 * (2 * Y)) = ξ / (4 * Y) := by ring
  have e2 : ξ / (2 * Y) = ξ / (4 * Y) + ξ / (4 * Y) := by field_simp; ring
  rw [e1, e2]
  linarith

theorem K_le_bound {X Y b : ℝ} {D : ℕ} (hX1 : 1 ≤ X) (hY1 : 1 ≤ Y) (hb : 0 ≤ b) :
    (2 * Y) ^ (D + 1) * ((((D + 1) ^ 2 : ℕ) : ℝ) * Y) + 2 * Y + 2 * X ^ b + 1 ≤
      (2 ^ (D + 1) * (((D + 1) ^ 2 : ℕ) : ℝ) + 5) * Y ^ (D + 2) * X ^ b := by
  have hYD : 1 ≤ Y ^ (D + 2) := one_le_pow₀ hY1
  have hXb1 : 1 ≤ X ^ b := Real.one_le_rpow hX1 hb
  have hpow : (2 * Y) ^ (D + 1) * ((((D + 1) ^ 2 : ℕ) : ℝ) * Y) =
      2 ^ (D + 1) * (((D + 1) ^ 2 : ℕ) : ℝ) * Y ^ (D + 2) := by
    rw [mul_pow, show D + 2 = (D + 1) + 1 by ring, pow_succ Y (D + 1)]; ring
  have hpos : 0 ≤ 2 ^ (D + 1) * (((D + 1) ^ 2 : ℕ) : ℝ) := by positivity
  rw [hpow]
  set P := Y ^ (D + 2) with hP
  set Q := X ^ b with hQ
  have hPQ : 1 ≤ P * Q := one_le_mul_of_one_le_of_one_le hYD hXb1
  have e1 : 2 ^ (D + 1) * (((D + 1) ^ 2 : ℕ) : ℝ) * P ≤
      2 ^ (D + 1) * (((D + 1) ^ 2 : ℕ) : ℝ) * P * Q :=
    le_mul_of_one_le_right (by positivity) hXb1
  have hYP : Y ≤ P := by
    calc Y = Y ^ 1 := (pow_one Y).symm
      _ ≤ Y ^ (D + 2) := pow_le_pow_right₀ hY1 (by omega)
  have e2 : 2 * Y ≤ 2 * (P * Q) := by
    have : P ≤ P * Q := le_mul_of_one_le_right (by linarith) hXb1
    linarith
  have e3 : 2 * Q ≤ 2 * (P * Q) := by
    have : Q ≤ P * Q := le_mul_of_one_le_left (by linarith) hYD
    linarith
  have hexp : (2 ^ (D + 1) * (((D + 1) ^ 2 : ℕ) : ℝ) + 5) * P * Q =
      2 ^ (D + 1) * (((D + 1) ^ 2 : ℕ) : ℝ) * P * Q + 5 * (P * Q) := by ring
  rw [hexp]
  linarith

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
