-- Ported from this LOT tree, o287 (k4_physical_parent_potential_source), session x1037,
-- branch x1037, commit 7d0ae380, file Submission/Obl/k4_physical_parent_potential_source/Cartesian/CartesianField.lean;
-- only the namespace prefix is renamed. Earlier attributions in the file are kept.
/- Adapted from this LOT tree, o285, session x1022, commit 3118a01b648b6fe31c1ad302109f3ffc3507ef6f,
Submission/Obl/k4_original_interpolated_field_source/Cart/CartesianField.lean.
This is the signal-independent interpolation kernel, not the refuted o285 theorem.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_physical_row_packet_potential.Cartesian.WholeStateRow

/-!
# The interpolated physical field on whole states, with subpower bookkeeping

Paper tex-06 display `a05:interpolated-field`: one polynomial row `T` of degree
at most `3 M`, in the normalized base coordinates `z` of the old packet, fits
the state rows on a union `S` of whole states that keeps a `(C K^e)⁻¹`
fraction of the family's original mass; its coefficients are at most `C K^e`
and the fit error is at most `C K^e p`.  Here `C` and `e` depend only on the
qualification degree `M`; `K` collects all subpower inputs and `p` is the
field-list resolution (`ξ ≤ p`), chosen after `K`.
-/

namespace Submission.Obl.k4_physical_row_packet_potential.Cartesian

open MeasureTheory Set MvPolynomial Matrix
open Submission.Lib.K4CommonLocalChoice (cell)
open Submission.Lib.K4ChartLifting (coeffL1 coeffL1_nonneg abs_coeff_le_coeffL1
  coeffL1_le_of_coeff_le)

noncomputable section

private theorem pow_le_pow_of_one_le {K : ℝ} (hK : 1 ≤ K) {a b : ℕ} (h : a ≤ b) :
    K ^ a ≤ K ^ b := pow_le_pow_right₀ hK h

/-- Size of the symmetric grid covering `[-3K², 3K²]` at mesh `ξ`. -/
theorem card_symGrid_bounds {K ξ : ℝ} (hK : 1 ≤ K) (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) :
    6 / ξ ≤ ((symGrid ξ ⌈3 * K ^ 2 / ξ⌉₊).card : ℝ) ∧
      ((symGrid ξ ⌈3 * K ^ 2 / ξ⌉₊).card : ℝ) ≤ 9 * K ^ 2 / ξ := by
  rw [card_symGrid hξ]
  have hle := Nat.le_ceil (3 * K ^ 2 / ξ)
  have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 * K ^ 2 / ξ by positivity)
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have h3 : 3 / ξ ≤ 3 * K ^ 2 / ξ := div_le_div_of_nonneg_right (by linarith) hξ.le
  have h3' : (3 : ℝ) ≤ 3 * K ^ 2 / ξ := by
    rw [le_div_iff₀ hξ]; nlinarith
  push_cast
  constructor
  · have : 6 / ξ = 2 * (3 / ξ) := by ring
    rw [this]; linarith
  · have : 9 * K ^ 2 / ξ = 2 * (3 * K ^ 2 / ξ) + 3 * K ^ 2 / ξ := by ring
    rw [this]; linarith

/-- The budget of the kernel for the explicit choices of `δ`, `U` and `a`. -/
theorem cartesian_budget {Bsel K ξ m Scard : ℝ} (e₁ : ℕ) (hB : 0 < Bsel) (hK : 1 ≤ K)
    (hξ : 0 < ξ) (hm : 0 < m) (hS : 0 < Scard) (hS9 : Scard ≤ 9 * K ^ 2 / ξ) :
    (2 * 19683 * Bsel * 4 ^ e₁ * K ^ (10 + 2 * e₁))⁻¹ * (27 * K ^ 4 * ξ ^ 3 * m) * Scard ^ 3 +
      Scard ^ 3 * (m / (2 * Scard ^ 3 * (Bsel * (4 * K ^ 2) ^ e₁))) ≤
    m / (Bsel * (4 * K ^ 2) ^ e₁) := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hBK : 0 < Bsel * (4 * K ^ 2) ^ e₁ := by positivity
  have hS3 : Scard ^ 3 ≤ (9 * K ^ 2 / ξ) ^ 3 := pow_le_pow_left₀ hS.le hS9 3
  have h4 : (4 * K ^ 2) ^ e₁ = 4 ^ e₁ * K ^ (2 * e₁) := by rw [mul_pow, pow_mul]
  have hfirst : (2 * 19683 * Bsel * 4 ^ e₁ * K ^ (10 + 2 * e₁))⁻¹ * (27 * K ^ 4 * ξ ^ 3 * m) *
      Scard ^ 3 ≤ m / (2 * (Bsel * (4 * K ^ 2) ^ e₁)) := by
    calc _ ≤ (2 * 19683 * Bsel * 4 ^ e₁ * K ^ (10 + 2 * e₁))⁻¹ * (27 * K ^ 4 * ξ ^ 3 * m) *
          (9 * K ^ 2 / ξ) ^ 3 := by gcongr
      _ = m / (2 * (Bsel * (4 * K ^ 2) ^ e₁)) := by
          rw [h4, pow_add]
          field_simp
          ring
  have hsecond : Scard ^ 3 * (m / (2 * Scard ^ 3 * (Bsel * (4 * K ^ 2) ^ e₁))) =
      m / (2 * (Bsel * (4 * K ^ 2) ^ e₁)) := by
    field_simp
  rw [hsecond]
  have : m / (2 * (Bsel * (4 * K ^ 2) ^ e₁)) + m / (2 * (Bsel * (4 * K ^ 2) ^ e₁)) =
      m / (Bsel * (4 * K ^ 2) ^ e₁) := by field_simp; ring
  linarith

/-- The gap of the anchor sampling for the explicit anchor separation. -/
theorem cartesian_gap {M : ℕ} {ξ δn Scard : ℝ} (hξ : 0 < ξ) (hδn : 0 < δn)
    (hS : 6 / ξ ≤ Scard) (hsmall : 4 * ((M : ℝ) + 1) ^ 2 * ξ ≤ δn) :
    3 * ((M + 1 : ℕ) : ℝ) ^ 2 * ((2 * (δn / (4 * ((M : ℝ) + 1) ^ 2)) / ξ + 1) / Scard) ≤
      3 * δn / 8 := by
  push_cast
  have hM : 0 < ((M : ℝ) + 1) ^ 2 := by positivity
  have hSpos : 0 < Scard := lt_of_lt_of_le (by positivity) hS
  have hinv : 1 / Scard ≤ ξ / 6 := by
    rw [div_le_div_iff₀ hSpos (by norm_num)]
    have := (div_le_iff₀ hξ).mp hS
    linarith
  have hnum : 0 ≤ 2 * (δn / (4 * ((M : ℝ) + 1) ^ 2)) / ξ + 1 := by positivity
  calc 3 * ((M : ℝ) + 1) ^ 2 * ((2 * (δn / (4 * ((M : ℝ) + 1) ^ 2)) / ξ + 1) / Scard)
      = 3 * ((M : ℝ) + 1) ^ 2 * ((2 * (δn / (4 * ((M : ℝ) + 1) ^ 2)) / ξ + 1) * (1 / Scard)) := by
        ring
    _ ≤ 3 * ((M : ℝ) + 1) ^ 2 * ((2 * (δn / (4 * ((M : ℝ) + 1) ^ 2)) / ξ + 1) * (ξ / 6)) := by
        gcongr
    _ = δn / 4 + ((M : ℝ) + 1) ^ 2 * ξ / 2 := by
        field_simp
        ring
    _ ≤ 3 * δn / 8 := by nlinarith

theorem mul_le_one_of_le_of_mul_le_one {c a ξ : ℝ} (hca : c ≤ a) (hξ : 0 ≤ ξ)
    (h : a * ξ ≤ 1) : c * ξ ≤ 1 :=
  (mul_le_mul_of_nonneg_right hca hξ).trans h

theorem le_mul_pow_of_le {c C K : ℝ} {m e : ℕ} (hK : 1 ≤ K) (hc : 0 ≤ c) (hcC : c ≤ C)
    (hm : m ≤ e) : c * K ^ m ≤ C * K ^ e :=
  mul_le_mul hcC (pow_le_pow_right₀ hK hm) (by positivity) (hc.trans hcC)

/-- The inner error term of the kernel, in units of `p`. -/
theorem kernel_inner_error_le (M : ℕ) {K p ξ ε err : ℝ} (hK : 1 ≤ K) (hp1 : p ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξp : ξ ≤ p) (hε0 : 0 ≤ ε) (hεξ : ε ≤ ξ) (herr : err ≤ p) :
    p + (err + ((M : ℝ) + 1) * M * K * K ^ M * ε) + ((M : ℝ) + 1) * p * (3 * (4 * K ^ 2)) ^ M +
        3 * ((M : ℝ) + 1) * M * (4 * K ^ 2 + p) * (3 * (4 * K ^ 2)) ^ M * ξ ≤
      (2 + ((M : ℝ) + 1) * M + ((M : ℝ) + 1) * 12 ^ M + 15 * ((M : ℝ) + 1) * M * 12 ^ M) *
        K ^ (2 * M + 2) * p := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hp0 : 0 ≤ p := hξ0.trans hξp
  have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h12 : (3 * (4 * K ^ 2)) ^ M = 12 ^ M * K ^ (2 * M) := by
    rw [show 3 * (4 * K ^ 2) = 12 * K ^ 2 by ring, mul_pow, ← pow_mul]
  have hKa : ∀ a : ℕ, a ≤ 2 * M + 2 → K ^ a ≤ K ^ (2 * M + 2) :=
    fun a ha => pow_le_pow_right₀ hK ha
  have hK1 : 1 ≤ K ^ (2 * M + 2) := one_le_pow₀ hK
  have hKK : K * K ^ M ≤ K ^ (2 * M + 2) := by
    rw [← pow_succ']; exact hKa _ (by omega)
  have hK2M : K ^ (2 * M) ≤ K ^ (2 * M + 2) := hKa _ (by omega)
  have h4K : 4 * K ^ 2 + p ≤ 5 * K ^ 2 := by nlinarith [one_le_pow₀ (n := 2) hK]
  have h2K : K ^ 2 * K ^ (2 * M) = K ^ (2 * M + 2) := by rw [← pow_add]; ring_nf
  rw [h12]
  have t1 : err ≤ p := herr
  have t2 : ((M : ℝ) + 1) * M * K * K ^ M * ε ≤ ((M : ℝ) + 1) * M * K ^ (2 * M + 2) * p := by
    have : K * K ^ M * ε ≤ K ^ (2 * M + 2) * p :=
      mul_le_mul hKK (hεξ.trans hξp) hε0 (by positivity)
    calc ((M : ℝ) + 1) * M * K * K ^ M * ε = ((M : ℝ) + 1) * M * (K * K ^ M * ε) := by ring
      _ ≤ ((M : ℝ) + 1) * M * (K ^ (2 * M + 2) * p) := by gcongr
      _ = _ := by ring
  have t3 : ((M : ℝ) + 1) * p * (12 ^ M * K ^ (2 * M)) ≤
      ((M : ℝ) + 1) * 12 ^ M * K ^ (2 * M + 2) * p := by
    calc ((M : ℝ) + 1) * p * (12 ^ M * K ^ (2 * M)) =
        ((M : ℝ) + 1) * 12 ^ M * K ^ (2 * M) * p := by ring
      _ ≤ _ := by gcongr
  have t4 : 3 * ((M : ℝ) + 1) * M * (4 * K ^ 2 + p) * (12 ^ M * K ^ (2 * M)) * ξ ≤
      15 * ((M : ℝ) + 1) * M * 12 ^ M * K ^ (2 * M + 2) * p := by
    calc 3 * ((M : ℝ) + 1) * M * (4 * K ^ 2 + p) * (12 ^ M * K ^ (2 * M)) * ξ ≤
        3 * ((M : ℝ) + 1) * M * (5 * K ^ 2) * (12 ^ M * K ^ (2 * M)) * p := by gcongr
      _ = 15 * ((M : ℝ) + 1) * M * 12 ^ M * (K ^ 2 * K ^ (2 * M)) * p := by ring
      _ = _ := by rw [h2K]
  have t5 : p ≤ K ^ (2 * M + 2) * p := le_mul_of_one_le_left hp0 hK1
  have t6 : err ≤ K ^ (2 * M + 2) * p := t1.trans t5
  calc _ ≤ K ^ (2 * M + 2) * p + (K ^ (2 * M + 2) * p +
          ((M : ℝ) + 1) * M * K ^ (2 * M + 2) * p) +
        ((M : ℝ) + 1) * 12 ^ M * K ^ (2 * M + 2) * p +
        15 * ((M : ℝ) + 1) * M * 12 ^ M * K ^ (2 * M + 2) * p := by
          gcongr
    _ = _ := by ring

/-- The outer error factor of the kernel for an anchor separation `r` with
`2 Kk / r = A K^a`. -/
theorem kernel_outer_factor_le (M : ℕ) {K X A : ℝ} {a : ℕ} (hK : 1 ≤ K) (hA : 0 ≤ A)
    (hX : X = A * K ^ a) :
    3 * (1 + ((M : ℝ) + 1) * X ^ M) ^ 3 ≤
      3 * (1 + ((M : ℝ) + 1) * A ^ M) ^ 3 * K ^ (3 * a * M) := by
  have hK1 : 1 ≤ K ^ (a * M) := one_le_pow₀ hK
  have hin : 1 + ((M : ℝ) + 1) * X ^ M ≤ (1 + ((M : ℝ) + 1) * A ^ M) * K ^ (a * M) := by
    rw [hX, mul_pow, ← pow_mul]
    have : 0 ≤ ((M : ℝ) + 1) * A ^ M := by positivity
    nlinarith
  have h0 : 0 ≤ 1 + ((M : ℝ) + 1) * X ^ M := by
    rw [hX]; positivity
  calc 3 * (1 + ((M : ℝ) + 1) * X ^ M) ^ 3 ≤
      3 * ((1 + ((M : ℝ) + 1) * A ^ M) * K ^ (a * M)) ^ 3 := by gcongr
    _ = 3 * (1 + ((M : ℝ) + 1) * A ^ M) ^ 3 * K ^ (3 * a * M) := by
      rw [mul_pow, ← pow_mul]; ring_nf

/-- The coefficient bound of the kernel row for the explicit anchor separation. -/
theorem kernel_coeff_bound_le (M : ℕ) {Ck c₁ K p r δn : ℝ} {n m₁ : ℕ} (hK : 1 ≤ K)
    (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hCk : 0 ≤ Ck) (hc₁ : 0 ≤ c₁)
    (hr : r = δn / (4 * ((M : ℝ) + 1) ^ 2)) (hδinv : δn⁻¹ = c₁ ^ n * K ^ m₁) (hδn : 0 < δn) :
    Ck * (((M : ℝ) + 1) ^ 3 * (4 * K ^ 2 + p) * ((1 + 4 * K ^ 2) / r) ^ (3 * M)) ≤
      (Ck * ((M : ℝ) + 1) ^ 3 * 5 * (20 * ((M : ℝ) + 1) ^ 2 * c₁ ^ n) ^ (3 * M)) *
        K ^ (2 + 3 * M * (m₁ + 2)) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hM : 0 < ((M : ℝ) + 1) ^ 2 := by positivity
  have hdiv : (1 + 4 * K ^ 2) / r = (1 + 4 * K ^ 2) * (4 * ((M : ℝ) + 1) ^ 2) *
      (c₁ ^ n * K ^ m₁) := by
    rw [hr, ← hδinv]
    field_simp
  have h1 : (1 + 4 * K ^ 2) / r ≤ 20 * ((M : ℝ) + 1) ^ 2 * c₁ ^ n * K ^ (m₁ + 2) := by
    rw [hdiv, pow_add]
    have : 1 + 4 * K ^ 2 ≤ 5 * K ^ 2 := by linarith
    calc (1 + 4 * K ^ 2) * (4 * ((M : ℝ) + 1) ^ 2) * (c₁ ^ n * K ^ m₁) ≤
        (5 * K ^ 2) * (4 * ((M : ℝ) + 1) ^ 2) * (c₁ ^ n * K ^ m₁) := by gcongr
      _ = _ := by ring
  have h2 : 4 * K ^ 2 + p ≤ 5 * K ^ 2 := by linarith
  have h0 : 0 ≤ (1 + 4 * K ^ 2) / r := by rw [hdiv]; positivity
  calc Ck * (((M : ℝ) + 1) ^ 3 * (4 * K ^ 2 + p) * ((1 + 4 * K ^ 2) / r) ^ (3 * M)) ≤
      Ck * (((M : ℝ) + 1) ^ 3 * (5 * K ^ 2) *
        (20 * ((M : ℝ) + 1) ^ 2 * c₁ ^ n * K ^ (m₁ + 2)) ^ (3 * M)) := by gcongr
    _ = (Ck * ((M : ℝ) + 1) ^ 3 * 5 * (20 * ((M : ℝ) + 1) ^ 2 * c₁ ^ n) ^ (3 * M)) *
        (K ^ 2 * K ^ ((m₁ + 2) * (3 * M))) := by
        rw [mul_pow (20 * ((M : ℝ) + 1) ^ 2 * c₁ ^ n), ← pow_mul]; ring
    _ = _ := by rw [← pow_add]; ring_nf

/-- The mass bound of the kernel for the explicit choices. -/
theorem kernel_mass_le {Bsel K δn G a mΩ mS Scard c₁ : ℝ} {e₁ n m₁ : ℕ} (hB : 0 < Bsel)
    (hK : 1 ≤ K) (hδn : 0 < δn) (hG : G ≤ 3 * δn / 8) (hS : 0 < Scard) (hm : 0 ≤ mΩ)
    (ha : a = mΩ / (2 * Scard ^ 3 * (Bsel * (4 * K ^ 2) ^ e₁)))
    (hδinv : δn⁻¹ = c₁ ^ n * K ^ m₁)
    (hmass : (δn - G) / 2 * a * Scard ^ 3 ≤ mS) :
    mΩ ≤ (7 * Bsel * 4 ^ e₁ * c₁ ^ n) * K ^ (2 * e₁ + m₁) * mS := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hD : 0 < 2 * Scard ^ 3 * (Bsel * (4 * K ^ 2) ^ e₁) := by positivity
  have haS : a * Scard ^ 3 = mΩ / (2 * (Bsel * (4 * K ^ 2) ^ e₁)) := by
    rw [ha]; field_simp
  have h1 : 5 * δn / 16 * (mΩ / (2 * (Bsel * (4 * K ^ 2) ^ e₁))) ≤ mS := by
    have hge : 5 * δn / 16 ≤ (δn - G) / 2 := by linarith
    have hnn : 0 ≤ mΩ / (2 * (Bsel * (4 * K ^ 2) ^ e₁)) := by positivity
    calc 5 * δn / 16 * (mΩ / (2 * (Bsel * (4 * K ^ 2) ^ e₁))) ≤
        (δn - G) / 2 * (mΩ / (2 * (Bsel * (4 * K ^ 2) ^ e₁))) :=
          mul_le_mul_of_nonneg_right hge hnn
      _ = (δn - G) / 2 * a * Scard ^ 3 := by rw [mul_assoc, haS]
      _ ≤ mS := hmass
  have hc : 0 < c₁ ^ n * K ^ m₁ := by rw [← hδinv]; positivity
  have h4 : (4 * K ^ 2) ^ e₁ = 4 ^ e₁ * K ^ (2 * e₁) := by rw [mul_pow, ← pow_mul]
  have hδ : δn = (c₁ ^ n * K ^ m₁)⁻¹ := by rw [← hδinv, inv_inv]
  rw [hδ, h4] at h1
  set X : ℝ := c₁ ^ n * K ^ m₁ with hX
  set B : ℝ := Bsel * (4 ^ e₁ * K ^ (2 * e₁)) with hBdef
  have hB4 : 0 < B := by positivity
  have hmS : 0 ≤ mS := le_trans (by positivity) h1
  have hY : 0 ≤ mS * (B * X) := by positivity
  calc mΩ = 5 * X⁻¹ / 16 * (mΩ / (2 * B)) * (32 / 5 * B * X) := by
        field_simp; ring
    _ ≤ mS * (32 / 5 * B * X) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = 32 / 5 * (mS * (B * X)) := by ring
    _ ≤ 7 * (mS * (B * X)) := mul_le_mul_of_nonneg_right (by norm_num) hY
    _ = (7 * Bsel * 4 ^ e₁ * c₁ ^ n) * K ^ (2 * e₁ + m₁) * mS := by
        rw [hBdef, hX, pow_add]; ring

/-- The kernel error for the explicit anchor separation, in units of `p`. -/
theorem kernel_err_le (M : ℕ) {K p ξ ε err r δn c₁ : ℝ} {n m₁ : ℕ} (hK : 1 ≤ K)
    (hp1 : p ≤ 1) (hξ0 : 0 ≤ ξ) (hξp : ξ ≤ p) (hε0 : 0 ≤ ε) (hεξ : ε ≤ ξ) (herr0 : 0 ≤ err)
    (herr : err ≤ p)
    (hc₁ : 0 ≤ c₁) (hr : r = δn / (4 * ((M : ℝ) + 1) ^ 2)) (hδinv : δn⁻¹ = c₁ ^ n * K ^ m₁)
    (hδn : 0 < δn) :
    p + 3 * (1 + ((M : ℝ) + 1) * ((2 * (4 * K ^ 2)) / r) ^ M) ^ 3 *
        (p + (err + ((M : ℝ) + 1) * M * K * K ^ M * ε) + ((M : ℝ) + 1) * p * (3 * (4 * K ^ 2)) ^ M +
          3 * ((M : ℝ) + 1) * M * (4 * K ^ 2 + p) * (3 * (4 * K ^ 2)) ^ M * ξ) ≤
      (1 + 3 * (1 + ((M : ℝ) + 1) * (32 * ((M : ℝ) + 1) ^ 2 * c₁ ^ n) ^ M) ^ 3 *
        (2 + ((M : ℝ) + 1) * M + ((M : ℝ) + 1) * 12 ^ M + 15 * ((M : ℝ) + 1) * M * 12 ^ M)) *
        K ^ (3 * (m₁ + 2) * M + 2 * M + 2) * p := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hp0 : 0 ≤ p := hξ0.trans hξp
  have hM : 0 < ((M : ℝ) + 1) ^ 2 := by positivity
  have hX : (2 * (4 * K ^ 2)) / r = (32 * ((M : ℝ) + 1) ^ 2 * c₁ ^ n) * K ^ (m₁ + 2) := by
    rw [hr, pow_add]
    have : (c₁ ^ n * K ^ m₁) = δn⁻¹ := hδinv.symm
    calc (2 * (4 * K ^ 2)) / (δn / (4 * ((M : ℝ) + 1) ^ 2)) =
        32 * ((M : ℝ) + 1) ^ 2 * K ^ 2 * δn⁻¹ := by field_simp; ring
      _ = _ := by rw [← this]; ring
  have houter := kernel_outer_factor_le M hK (by positivity) hX
  have hinner := kernel_inner_error_le M hK hp1 hξ0 hξp hε0 hεξ herr
  set cE : ℝ := 2 + ((M : ℝ) + 1) * M + ((M : ℝ) + 1) * 12 ^ M + 15 * ((M : ℝ) + 1) * M * 12 ^ M
  set c₃ : ℝ := 3 * (1 + ((M : ℝ) + 1) * (32 * ((M : ℝ) + 1) ^ 2 * c₁ ^ n) ^ M) ^ 3
  have hcE : 0 ≤ cE := by positivity
  have hc₃ : 0 ≤ c₃ := by positivity
  set I := p + (err + ((M : ℝ) + 1) * M * K * K ^ M * ε) + ((M : ℝ) + 1) * p * (3 * (4 * K ^ 2)) ^ M +
          3 * ((M : ℝ) + 1) * M * (4 * K ^ 2 + p) * (3 * (4 * K ^ 2)) ^ M * ξ with hI
  have hI0 : 0 ≤ I := by rw [hI]; positivity
  have hprod : 3 * (1 + ((M : ℝ) + 1) * ((2 * (4 * K ^ 2)) / r) ^ M) ^ 3 * I ≤
      c₃ * K ^ (3 * (m₁ + 2) * M) * (cE * K ^ (2 * M + 2) * p) :=
    mul_le_mul houter hinner hI0 (by positivity)
  have hp' : p ≤ K ^ (3 * (m₁ + 2) * M + 2 * M + 2) * p :=
    le_mul_of_one_le_left hp0 (one_le_pow₀ hK)
  calc p + 3 * (1 + ((M : ℝ) + 1) * ((2 * (4 * K ^ 2)) / r) ^ M) ^ 3 * I ≤
      K ^ (3 * (m₁ + 2) * M + 2 * M + 2) * p +
        c₃ * K ^ (3 * (m₁ + 2) * M) * (cE * K ^ (2 * M + 2) * p) := add_le_add hp' hprod
    _ = (1 + c₃ * cE) * K ^ (3 * (m₁ + 2) * M + 2 * M + 2) * p := by
        rw [show 3 * (m₁ + 2) * M + 2 * M + 2 = 3 * (m₁ + 2) * M + (2 * M + 2) by ring, pow_add]
        ring

/-- The Lipschitz transfer from the grid point to the actual base point. -/
theorem lip_part_le {L B K ξ p : ℝ} {M eQ d : ℕ} (hK : 1 ≤ K) (hξ0 : 0 ≤ ξ) (hξp : ξ ≤ p)
    (hL0 : 0 ≤ L) (hL : L ≤ B * K ^ eQ) (hd : d ≤ 3 * M) :
    L * (1 + 4 * K ^ 2) ^ d * (4 * K * ξ) ≤ (B * 5 ^ (3 * M) * 4) * K ^ (eQ + 6 * M + 1) * p := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have h1 : (1 + 4 * K ^ 2) ^ d ≤ (5 * K ^ 2) ^ (3 * M) :=
    (pow_le_pow_right₀ (by linarith) hd).trans (pow_le_pow_left₀ (by positivity) (by linarith) _)
  have h2 : 4 * K * ξ ≤ 4 * K * p := by gcongr
  have hB : 0 ≤ B * K ^ eQ := hL0.trans hL
  calc L * (1 + 4 * K ^ 2) ^ d * (4 * K * ξ) ≤ (B * K ^ eQ) * (5 * K ^ 2) ^ (3 * M) * (4 * K * p) := by
        gcongr
    _ = (B * 5 ^ (3 * M) * 4) * (K ^ eQ * K ^ (6 * M) * K) * p := by
        rw [mul_pow, ← pow_mul]; ring_nf
    _ = (B * 5 ^ (3 * M) * 4) * K ^ (eQ + 6 * M + 1) * p := by
        rw [pow_add, pow_add, pow_one]

set_option maxHeartbeats 4000000 in
/-- **The interpolated field on whole states** (paper `a05:interpolated-field`), with
constants depending only on the qualification degree `M`. -/
theorem cartesian_whole_state_row (M : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ e : ℕ,
    ∀ {Λ σ : Type} [MeasurableSpace Λ] [MeasurableSpace σ] [Countable σ]
      [MeasurableSingletonClass σ]
      (μ : Measure (Λ × ℝ)) [IsFiniteMeasure μ]
      (E0 Eref : Set (Λ × ℝ)), MeasurableSet E0 → E0 ⊆ Eref →
      ∀ (st : Λ × ℝ → σ), Measurable st →
      ∀ (Gs cz : σ → Fin 3 → ℝ) (z : Λ × ℝ → Fin 3 → ℝ) (v : Λ → Fin 2 → ℝ) (t0 h : ℝ),
      0 < h →
      (∀ l t, z (l, t) 0 = (t - t0) / h) →
      (∀ l t t', z (l, t') = z (l, t) + ((t' - t) / h) • lift (v l)) →
      ∀ (J : Fin 3 → Fin 2 → ℝ) (Ainv : Matrix (Fin 3) (Fin 3) ℝ),
      liftMatrix J * Ainv = 1 →
      ∀ (K ξ ε η p err : ℝ), 1 ≤ K → 0 < ξ → C * K ^ e * ξ ≤ 1 → 0 ≤ ε → ε ≤ ξ →
      0 ≤ η → η ≤ ξ → ξ ≤ p → p ≤ 1 → 0 ≤ err → err ≤ p →
      (∀ i k, |J i k| ≤ K) → (∀ i k, |Ainv i k| ≤ K) →
      (∀ x ∈ Eref, ∀ i, |z x i - cz (st x) i| ≤ ε) →
      ∀ (Ωst : Set σ),
      (∀ D ∈ Ωst, ∀ i, |cz D i| ≤ K) →
      (∀ D ∈ Ωst, ∀ j, |Gs D j| ≤ K) →
      (∀ D ∈ Ωst, ∀ axis : Fin 3, ∃ w ∈ Eref, st w = D ∧ (∀ k, |v w.1 k - J axis k| ≤ η) ∧
        t0 ≤ w.2 ∧ w.2 ≤ t0 + h ∧ QualWitness Eref st Gs t0 h M K err (1 / K) w) →
      (∀ c : Fin 3 → ℝ, ∃ F : Finset (Fin 3 → ℤ), (F.card : ℝ) ≤ K ∧
        ∀ x ∈ Eref, (∀ i, |z x i - c i| ≤ 30 * K ^ 2 * ξ) → cell p (Gs (st x)) ∈ F) →
      (∀ (c : Fin 3 → ℝ) (r : ℝ), 0 < r →
        μ.real (E0 ∩ st ⁻¹' Ωst ∩ {x | ∀ i, |z x i - c i| ≤ r}) ≤
          K * r ^ 3 * μ.real (E0 ∩ st ⁻¹' Ωst)) →
      0 < μ.real (E0 ∩ st ⁻¹' Ωst) →
      ∃ (T : Fin 3 → MvPolynomial (Fin 3) ℝ) (S : Set (Λ × ℝ)),
        MeasurableSet S ∧ S ⊆ E0 ∩ st ⁻¹' Ωst ∧
        (∀ x ∈ E0, ∀ y ∈ S, st x = st y → x ∈ S) ∧
        (∀ j, (T j).totalDegree ≤ 3 * M) ∧ (∀ j d, |(T j).coeff d| ≤ C * K ^ e) ∧
        μ.real (E0 ∩ st ⁻¹' Ωst) ≤ C * K ^ e * μ.real S ∧
        ∀ x ∈ S, ∀ j, |Gs (st x) j - eval (z x) (T j)| ≤ C * K ^ e * p := by
  classical
  obtain ⟨Bsel, hBsel, Ck, hCk, hrow⟩ := original_polynomial_row M 3
  set e₁ : ℕ := 1 + 3 * (3 + 3 * M * (3 * (M + 1))) with he₁
  set n : ℕ := (M + 2) ^ 3 with hn
  set c₁ : ℝ := 2 * 19683 * Bsel * 4 ^ e₁ with hc₁
  set m₁ : ℕ := (10 + 2 * e₁) * n with hm₁
  set Mr : ℝ := (M : ℝ) + 1 with hMr
  set cQ : ℝ := Ck * Mr ^ 3 * 5 * (20 * Mr ^ 2 * c₁ ^ n) ^ (3 * M) with hcQ
  set eQ : ℕ := 2 + 3 * M * (m₁ + 2) with heQ
  set c₃ : ℝ := 3 * (1 + Mr * (32 * Mr ^ 2 * c₁ ^ n) ^ M) ^ 3 with hc₃
  set cE : ℝ := 2 + Mr * M + Mr * 12 ^ M + 15 * Mr * M * 12 ^ M with hcE
  set eErr : ℕ := 3 * (m₁ + 2) * M + 2 * M + 2 with heErr
  set cS : ℝ := (((3 * M + 1) ^ 3 : ℕ) : ℝ) with hcS
  set C : ℝ := 4 * Mr ^ 2 * c₁ ^ n + 4 + (1 + c₃ * cE) + cS * cQ * 5 ^ (3 * M) * 4 +
    cS * cQ * 3 ^ (3 * M) + 7 * Bsel * 4 ^ e₁ * c₁ ^ n with hC
  set e : ℕ := m₁ + 1 + eErr + (eQ + 6 * M + 1) + (eQ + 3 * M) + (2 * e₁ + m₁) with he
  have hMr0 : 0 < Mr := by positivity
  have hc₁0 : 0 < c₁ := by positivity
  have hcQ0 : 0 ≤ cQ := by positivity
  have hc₃0 : 0 ≤ c₃ := by positivity
  have hcE0 : 0 ≤ cE := by positivity
  have hcS0 : 0 ≤ cS := by positivity
  have hC4 : 4 ≤ C := by
    have : 0 ≤ 4 * Mr ^ 2 * c₁ ^ n := by positivity
    have : 0 ≤ 1 + c₃ * cE := by positivity
    have : 0 ≤ cS * cQ * 5 ^ (3 * M) * 4 := by positivity
    have : 0 ≤ cS * cQ * 3 ^ (3 * M) := by positivity
    have : 0 ≤ 7 * Bsel * 4 ^ e₁ * c₁ ^ n := by positivity
    linarith
  refine ⟨C, by linarith, e, ?_⟩
  intro Λ σ _ _ _ _ μ _ E0 Eref hE0 hE0ref st hst Gs cz z v t0 h hh hz0 hzline J Ainv hA
    K ξ ε η p err hK hξ hCξ hε hεξ hη hηξ hξp hp1 herr herrp hJ hAinv hcz Ωst hczK hGK hwit
    hfield hdens hpos
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hp0 : 0 < p := lt_of_lt_of_le hξ hξp
  set mΩ : ℝ := μ.real (E0 ∩ st ⁻¹' Ωst) with hmΩ
  -- smallness of the grid mesh
  have hξ1 : ξ ≤ 1 := by
    have h1 : (1 : ℝ) * K ^ 0 ≤ C * K ^ e :=
      le_mul_pow_of_le hK zero_le_one (by linarith) (Nat.zero_le _)
    have := mul_le_one_of_le_of_mul_le_one h1 hξ.le hCξ
    simpa using this
  have h4Kξ : 4 * K * ξ ≤ 1 := by
    have h1 : (4 : ℝ) * K ^ 1 ≤ C * K ^ e :=
      le_mul_pow_of_le hK (by norm_num) hC4 (by omega)
    have := mul_le_one_of_le_of_mul_le_one h1 hξ.le hCξ
    simpa using this
  set δ : ℝ := (c₁ * K ^ (10 + 2 * e₁))⁻¹ with hδ
  set δn : ℝ := δ ^ n with hδn
  have hδn_eq : δn = (c₁ ^ n * K ^ m₁)⁻¹ := by
    rw [hδn, hδ, inv_pow, mul_pow, ← pow_mul]
  have hδ0 : 0 < δ := by positivity
  have hδn0 : 0 < δn := by positivity
  have hξδ : 4 * Mr ^ 2 * ξ ≤ δn := by
    have h1 : (4 * Mr ^ 2 * c₁ ^ n) * K ^ m₁ ≤ C * K ^ e :=
      le_mul_pow_of_le hK (by positivity) (by
        have : 0 ≤ 4 + (1 + c₃ * cE) + cS * cQ * 5 ^ (3 * M) * 4 +
          cS * cQ * 3 ^ (3 * M) + 7 * Bsel * 4 ^ e₁ * c₁ ^ n := by positivity
        rw [hC]; linarith) (by omega)
    have h2 := mul_le_one_of_le_of_mul_le_one h1 hξ.le hCξ
    rw [hδn_eq, ← one_div, le_div_iff₀ (by positivity)]
    calc 4 * Mr ^ 2 * ξ * (c₁ ^ n * K ^ m₁) = 4 * Mr ^ 2 * c₁ ^ n * K ^ m₁ * ξ := by ring
      _ ≤ 1 := h2
  -- the kernel parameters
  set Kk : ℝ := 4 * K ^ 2 with hKk
  set r : ℝ := δn / (4 * Mr ^ 2) with hr
  set Scard : ℝ := ((symGrid ξ ⌈3 * K ^ 2 / ξ⌉₊).card : ℝ) with hScard
  set U : ℝ := 27 * K ^ 4 * ξ ^ 3 * mΩ with hU
  set a : ℝ := mΩ / (2 * Scard ^ 3 * (Bsel * Kk ^ e₁)) with ha
  obtain ⟨hS6, hS9⟩ := card_symGrid_bounds hK hξ hξ1
  have hSpos : 0 < Scard := lt_of_lt_of_le (by positivity) hS6
  have hgapb := cartesian_gap (M := M) hξ hδn0 hS6 hξδ
  have hbudget := cartesian_budget e₁ hBsel hK hξ hpos hSpos hS9
  have hU0 : 0 < U := mul_pos (by positivity) hpos
  have hKk0 : 0 < Kk := by positivity
  have ha0 : 0 < a := div_pos hpos (mul_pos (mul_pos two_pos (pow_pos hSpos 3))
    (mul_pos hBsel (pow_pos hKk0 _)))
  have hr0 : 0 < r := div_pos hδn0 (mul_pos four_pos (pow_pos hMr0 2))
  obtain ⟨Q, S, hSm, hSsub, hSsat, hQdeg, hQcoef, hSmass, hSerr⟩ :=
    whole_state_row_core M (Bsel := Bsel) (Ck := Ck) hrow μ E0 Eref hE0 hE0ref st hst Gs cz z v
      t0 h hh hz0 hzline J Ainv hA K ξ ε η p err hK hξ hξ1 hε hεξ hη hηξ hp0 herr herrp hJ hAinv
      hcz Ωst hczK hGK hwit hfield U a δ r hU0 ha0 hδ0.le hr0
      (fun c => by
        have := hdens c (3 * K * ξ) (by positivity)
        calc _ ≤ K * (3 * K * ξ) ^ 3 * mΩ := this
          _ = U := by rw [hU]; ring)
      hbudget
      (lt_of_le_of_lt hgapb (by linarith))
  -- the reciprocal of the anchor separation
  have hδinv : δn⁻¹ = c₁ ^ n * K ^ m₁ := by rw [hδn_eq, inv_inv]
  have hKk2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
  have hrdiv : ∀ y : ℝ, y / r = y * (4 * Mr ^ 2) * (c₁ ^ n * K ^ m₁) := by
    intro y
    rw [hr, ← hδinv]
    field_simp
  have hpow2 : ∀ a : ℕ, K ^ 2 * K ^ a = K ^ (a + 2) := fun a => by rw [← pow_add]; ring_nf
  -- the coefficient bound of the grid row
  have hCqb := kernel_coeff_bound_le M (Ck := Ck) (c₁ := c₁) (K := K) (p := p) (r := r)
    (δn := δn) (n := n) (m₁ := m₁) hK hp0.le hp1 hCk.le hc₁0.le hr hδinv hδn0
  have hcQK : (Ck * ((M : ℝ) + 1) ^ 3 * 5 * (20 * ((M : ℝ) + 1) ^ 2 * c₁ ^ n) ^ (3 * M)) *
      K ^ (2 + 3 * M * (m₁ + 2)) = cQ * K ^ eQ := rfl
  rw [hcQK] at hCqb
  have hL1 : ∀ j, coeffL1 (Q j) ≤ cS * (cQ * K ^ eQ) := by
    intro j
    have h1 := coeffL1_le_of_coeff_le (Q j) (hQdeg j) _ (hQcoef j)
    exact h1.trans (mul_le_mul_of_nonneg_left hCqb hcS0)
  -- the pieces of `C`
  have hA1 : 0 ≤ 4 * Mr ^ 2 * c₁ ^ n :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg Mr)) (pow_nonneg hc₁0.le n)
  have hA2 : 0 ≤ 1 + c₃ * cE := by
    have := mul_nonneg hc₃0 hcE0; linarith only [this]
  have hA3 : 0 ≤ cS * cQ * 5 ^ (3 * M) * 4 :=
    mul_nonneg (mul_nonneg (mul_nonneg hcS0 hcQ0) (pow_nonneg (by norm_num) _)) (by norm_num)
  have hA4 : 0 ≤ cS * cQ * 3 ^ (3 * M) :=
    mul_nonneg (mul_nonneg hcS0 hcQ0) (pow_nonneg (by norm_num) _)
  have hA5 : 0 ≤ 7 * Bsel * 4 ^ e₁ * c₁ ^ n :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hBsel.le) (pow_nonneg (by norm_num) _))
      (pow_nonneg hc₁0.le _)
  have hcoefC : cS * cQ * 3 ^ (3 * M) ≤ C := by
    rw [hC]; linarith only [hA1, hA2, hA3, hA4, hA5]
  have hmassC : 7 * Bsel * 4 ^ e₁ * c₁ ^ n ≤ C := by
    rw [hC]; linarith only [hA1, hA2, hA3, hA4, hA5]
  have herrC : (1 + c₃ * cE) + cS * cQ * 5 ^ (3 * M) * 4 ≤ C := by
    rw [hC]; linarith only [hA1, hA2, hA3, hA4, hA5]
  have hξR : ξ * (⌈3 * K ^ 2 / ξ⌉₊ : ℝ) ≤ 4 * K ^ 2 := by
    have hlt := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 3 * K ^ 2 / ξ by positivity)
    have hK2 : 1 ≤ K ^ 2 := one_le_pow₀ hK
    calc ξ * (⌈3 * K ^ 2 / ξ⌉₊ : ℝ) ≤ ξ * (3 * K ^ 2 / ξ + 1) :=
          mul_le_mul_of_nonneg_left hlt.le hξ.le
      _ = 3 * K ^ 2 + ξ := by field_simp
      _ ≤ 4 * K ^ 2 := by linarith only [hK2, hξ1]
  refine ⟨fun j => framePullback Ainv (Q j), S, hSm, hSsub, hSsat, ?_, ?_, ?_, ?_⟩
  · intro j
    exact (totalDegree_framePullback_le Ainv (Q j)).trans (hQdeg j)
  · intro j d
    calc |(framePullback Ainv (Q j)).coeff d| ≤ coeffL1 (framePullback Ainv (Q j)) :=
          abs_coeff_le_coeffL1 _ _
      _ ≤ coeffL1 (Q j) * (3 * K) ^ (3 * M) :=
          coeffL1_framePullback_le hK hAinv (Q j) (hQdeg j)
      _ ≤ (cS * (cQ * K ^ eQ)) * (3 ^ (3 * M) * K ^ (3 * M)) := by
          rw [mul_pow]; exact mul_le_mul_of_nonneg_right (hL1 j) (by positivity)
      _ = (cS * cQ * 3 ^ (3 * M)) * K ^ (eQ + 3 * M) := by rw [pow_add]; ring
      _ ≤ C * K ^ e := le_mul_pow_of_le hK hA4 hcoefC (by omega)
  · have hm := kernel_mass_le (Bsel := Bsel) (e₁ := e₁) (n := n) (m₁ := m₁) (c₁ := c₁)
      (G := 3 * ((M + 1 : ℕ) : ℝ) ^ 2 *
        ((2 * r / ξ + 1) / ((symGrid ξ ⌈3 * K ^ 2 / ξ⌉₊).card : ℝ)))
      hBsel hK hδn0 hgapb hSpos hpos.le rfl hδinv hSmass
    calc mΩ ≤ (7 * Bsel * 4 ^ e₁ * c₁ ^ n) * K ^ (2 * e₁ + m₁) * μ.real S := hm
      _ ≤ C * K ^ e * μ.real S :=
          mul_le_mul_of_nonneg_right (le_mul_pow_of_le hK hA5 hmassC (by omega)) measureReal_nonneg
  · intro x hx j
    have hxS := hSsub hx
    have hD : st x ∈ Ωst := hxS.2
    have hxref : x ∈ Eref := hE0ref hxS.1
    set gp := gridPoint (roundGrid3 ξ ⌈3 * K ^ 2 / ξ⌉₊ (Ainv *ᵥ cz (st x))) with hgpdef
    have herrQ := hSerr x hx j
    have hErr := kernel_err_le M (K := K) (p := p) (ξ := ξ) (ε := ε) (err := err) (r := r)
      (δn := δn) (c₁ := c₁) (n := n) (m₁ := m₁) hK hp1 hξ.le hξp hε hεξ herr herrp hc₁0.le hr
      hδinv hδn0
    have hgp : ∀ i, |gp i| ≤ 4 * K ^ 2 := fun i => (abs_gridPoint_le hξ.le _ i).trans hξR
    have huS : ∀ k, |(Ainv *ᵥ cz (st x)) k| ≤ ξ * (⌈3 * K ^ 2 / ξ⌉₊ : ℝ) := by
      intro k
      have h1 := abs_mulVec_le Ainv (cz (st x)) hAinv (hczK (st x) hD) k
      have hle := Nat.le_ceil (3 * K ^ 2 / ξ)
      have h2 : 3 * K ^ 2 ≤ ξ * (⌈3 * K ^ 2 / ξ⌉₊ : ℝ) := by
        rw [div_le_iff₀ hξ] at hle; linarith only [hle]
      calc |(Ainv *ᵥ cz (st x)) k| ≤ 3 * K * K := h1
        _ = 3 * K ^ 2 := by ring
        _ ≤ _ := h2
    have hclose : ∀ i, |(Ainv *ᵥ z x) i - gp i| ≤ 4 * K * ξ := by
      intro i
      have h1 : |(Ainv *ᵥ (z x - cz (st x))) i| ≤ 3 * K * ε :=
        abs_mulVec_le Ainv _ hAinv (fun k => by simpa using hcz x hxref k) i
      have h2 : |(Ainv *ᵥ cz (st x)) i - gp i| ≤ ξ / 2 :=
        abs_sub_gridPoint_roundGrid3_le hξ huS i
      have hsplit : (Ainv *ᵥ z x) i - gp i =
          (Ainv *ᵥ (z x - cz (st x))) i + ((Ainv *ᵥ cz (st x)) i - gp i) := by
        rw [mulVec_sub]; simp only [Pi.sub_apply]; ring
      rw [hsplit]
      have h3 : 3 * K * ε ≤ 3 * K * ξ := by gcongr
      calc |(Ainv *ᵥ (z x - cz (st x))) i + ((Ainv *ᵥ cz (st x)) i - gp i)| ≤
          |(Ainv *ᵥ (z x - cz (st x))) i| + |(Ainv *ᵥ cz (st x)) i - gp i| := abs_add_le _ _
        _ ≤ 3 * K * ξ + ξ / 2 := add_le_add (h1.trans h3) h2
        _ ≤ 4 * K * ξ := by nlinarith only [hK, hξ]
    have hlip := Submission.Lib.K4ContactTransfer.abs_eval_sub_le (Q j) (Ainv *ᵥ z x) gp
      (R := 4 * K ^ 2) (δ := 4 * K * ξ) (by positivity) hgp (by positivity) h4Kξ hclose
    have hlip2 := lip_part_le (M := M) (eQ := eQ) (B := cS * cQ) hK hξ.le hξp
      (coeffL1_nonneg (Q j)) (by rw [mul_assoc]; exact hL1 j) (hQdeg j)
    show |Gs (st x) j - eval (z x) (framePullback Ainv (Q j))| ≤ C * K ^ e * p
    rw [eval_framePullback]
    have hp0' : 0 ≤ p := hp0.le
    calc |Gs (st x) j - eval (Ainv *ᵥ z x) (Q j)| ≤
        |Gs (st x) j - eval gp (Q j)| + |eval gp (Q j) - eval (Ainv *ᵥ z x) (Q j)| :=
          abs_sub_le _ _ _
      _ ≤ (1 + c₃ * cE) * K ^ eErr * p + (cS * cQ * 5 ^ (3 * M) * 4) * K ^ (eQ + 6 * M + 1) * p :=
          add_le_add (herrQ.trans hErr) (by rw [abs_sub_comm]; exact hlip.trans hlip2)
      _ ≤ (1 + c₃ * cE) * K ^ e * p + (cS * cQ * 5 ^ (3 * M) * 4) * K ^ e * p := by
          gcongr
          all_goals first | exact hK | omega
      _ = ((1 + c₃ * cE) + cS * cQ * 5 ^ (3 * M) * 4) * K ^ e * p := by ring
      _ ≤ C * K ^ e * p := by gcongr

end

end Submission.Obl.k4_physical_row_packet_potential.Cartesian
