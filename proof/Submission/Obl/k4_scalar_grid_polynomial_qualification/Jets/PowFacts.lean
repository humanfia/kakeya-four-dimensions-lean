import Mathlib

set_option autoImplicit false

/-!
# Elementary power facts for the assembly

Real powers of `N ≥ 1` and of dyadic lengths `h = 2⁻ᵀ`, in the forms the assembly uses.
-/

namespace Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets

noncomputable section

theorem pow_mul_rpow_inv_natCast {x : ℝ} (hx : 0 ≤ x) {n : ℕ} (hn : n ≠ 0) (b : ℕ) :
    (x ^ (n * b)) ^ ((n : ℝ)⁻¹) = x ^ b := by
  rw [mul_comm, pow_mul, Real.pow_rpow_inv_natCast (pow_nonneg hx _) hn]

/-- `N^a N^b = N^(a+b)` for `N ≥ 1`. -/
theorem rpow_add_of_one_le {N : ℝ} (hN : 1 ≤ N) (a b : ℝ) : N ^ a * N ^ b = N ^ (a + b) :=
  (Real.rpow_add (lt_of_lt_of_le one_pos hN) a b).symm

theorem rpow_le_rpow_of_le_exp {N : ℝ} (hN : 1 ≤ N) {a b : ℝ} (h : a ≤ b) : N ^ a ≤ N ^ b :=
  Real.rpow_le_rpow_of_exponent_le hN h

theorem rpow_le_one_of_nonpos {N : ℝ} (hN : 1 ≤ N) {a : ℝ} (h : a ≤ 0) : N ^ a ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hN h

theorem one_le_rpow_of_nonneg {N : ℝ} (hN : 1 ≤ N) {a : ℝ} (h : 0 ≤ a) : 1 ≤ N ^ a :=
  Real.one_le_rpow hN h

/-- `(N^a)^n = N^(a n)`. -/
theorem rpow_pow_eq {N : ℝ} (hN : 0 ≤ N) (a : ℝ) (n : ℕ) : (N ^ a) ^ n = N ^ (a * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hN]

/-- Natural powers of a two-sided bound. -/
theorem pow_bounds {h a K : ℝ} (ha : 0 ≤ a) (hK : 1 ≤ K) (hlo : a / K ≤ h) (hhi : h ≤ K * a)
    {m L : ℕ} (hmL : m ≤ L) :
    a ^ m / K ^ L ≤ h ^ m ∧ h ^ m ≤ K ^ L * a ^ m := by
  have hK0 : 0 < K := lt_of_lt_of_le one_pos hK
  have hKm : K ^ m ≤ K ^ L := pow_le_pow_right₀ hK hmL
  have hKm0 : 0 < K ^ m := pow_pos hK0 _
  have h0 : 0 ≤ h := le_trans (div_nonneg ha hK0.le) hlo
  constructor
  · calc a ^ m / K ^ L ≤ a ^ m / K ^ m := div_le_div_of_nonneg_left (pow_nonneg ha _) hKm0 hKm
      _ = (a / K) ^ m := (div_pow a K m).symm
      _ ≤ h ^ m := pow_le_pow_left₀ (div_nonneg ha hK0.le) hlo m
  · calc h ^ m ≤ (K * a) ^ m := pow_le_pow_left₀ h0 hhi m
      _ = K ^ m * a ^ m := mul_pow K a m
      _ ≤ K ^ L * a ^ m := by gcongr

/-- The dyadic length at a multiple level. -/
theorem two_pow_mul_inv (T m : ℕ) : ((2 : ℝ) ^ (T * m))⁻¹ = (((2 : ℝ) ^ T)⁻¹) ^ m := by
  rw [pow_mul, inv_pow]

/-! ### The numbers of the assembly -/

/-- `h ≤ N^{-c_h/2}` when `h ≤ K N^{-c_h}` and `K ≤ N^α`, `α ≤ c_h / 2`. -/
theorem h_le_rpow {N K h c_h α : ℝ} (hN1 : 1 ≤ N) (hhhi : h ≤ K * N ^ (-c_h)) (hKα : K ≤ N ^ α)
    (hα : α ≤ c_h / 2) : h ≤ N ^ (-(c_h / 2)) := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  calc h ≤ K * N ^ (-c_h) := hhhi
    _ ≤ N ^ α * N ^ (-c_h) := by gcongr
    _ = N ^ (α + -c_h) := rpow_add_of_one_le hN1 _ _
    _ ≤ N ^ (-(c_h / 2)) := rpow_le_rpow_of_le_exp hN1 (by linarith)

/-- `ℓ Q^E ≤ 1` for `ℓ = h^{1/(10 s)}`, `Q = N^{ε₃}`. -/
theorem ell_mul_Q_pow_le {N h c_h ε₃ : ℝ} {s Eb : ℕ} (hN1 : 1 ≤ N) (hh0 : 0 < h)
    (hhN : h ≤ N ^ (-(c_h / 2))) (hch : 0 < c_h) (hs : 1 ≤ s) (hε₃0 : 0 ≤ ε₃)
    (hε₃c : ε₃ ≤ c_h / (20 * s * (Eb + 1))) :
    h ^ (((10 * s : ℕ) : ℝ)⁻¹) * (N ^ ε₃) ^ Eb ≤ 1 := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have hellN : h ^ (((10 * s : ℕ) : ℝ)⁻¹) ≤ N ^ (-(c_h / 2) * ((10 * s : ℕ) : ℝ)⁻¹) := by
    calc h ^ (((10 * s : ℕ) : ℝ)⁻¹) ≤ (N ^ (-(c_h / 2))) ^ (((10 * s : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow hh0.le hhN (by positivity)
      _ = N ^ (-(c_h / 2) * ((10 * s : ℕ) : ℝ)⁻¹) := (Real.rpow_mul hN0.le _ _).symm
  have hexp : ε₃ * Eb ≤ c_h / 2 * ((10 * s : ℕ) : ℝ)⁻¹ := by
    have hEb0 : (0 : ℝ) ≤ Eb := Nat.cast_nonneg _
    have h1 := hε₃c
    rw [le_div_iff₀ (by positivity)] at h1
    have e : c_h / 2 * ((10 * s : ℕ) : ℝ)⁻¹ = c_h / (20 * s) := by
      push_cast; field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith
  calc h ^ (((10 * s : ℕ) : ℝ)⁻¹) * (N ^ ε₃) ^ Eb
      ≤ N ^ (-(c_h / 2) * ((10 * s : ℕ) : ℝ)⁻¹) * N ^ (ε₃ * Eb) := by
        rw [rpow_pow_eq hN0.le]
        gcongr
    _ = N ^ (-(c_h / 2) * ((10 * s : ℕ) : ℝ)⁻¹ + ε₃ * Eb) := rpow_add_of_one_le hN1 _ _
    _ ≤ 1 := rpow_le_one_of_nonpos hN1 (by linarith)

/-- The fine precision of the first jet is below the leaf width. -/
theorem fine_precision_le {N ε₁ Q ell q₁ d : ℝ} {s w lam0 : ℕ} (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hellQ : ell * Q ≤ 1) (hNQ : N ^ ε₁ ≤ Q) (hN0 : 0 < N) (hs : 1 ≤ s)
    (hds : d ≤ 1 - 1 / (s : ℝ)) (hlam : lam0 = 32 * s * (w + 1))
    (hq : q₁ = ell ^ (10 * s * lam0)) :
    N ^ ε₁ * q₁ ^ ((1 - d) / 32) ≤ ell ^ w := by
  have hs0 : (0 : ℝ) < s := by exact_mod_cast hs
  have h32 : (32 * s : ℕ) ≠ 0 := by omega
  have hq0 : 0 < q₁ := by rw [hq]; positivity
  have hq1 : q₁ ≤ 1 := by rw [hq]; exact pow_le_one₀ hell0.le hell1
  have hexp : (((32 * s : ℕ) : ℝ))⁻¹ ≤ (1 - d) / 32 := by
    push_cast
    have h1 : 1 / (s : ℝ) ≤ 1 - d := by linarith
    have e : ((32 : ℝ) * s)⁻¹ = (1 / (s : ℝ)) / 32 := by field_simp
    rw [e]
    linarith
  have h1 : q₁ ^ ((1 - d) / 32) ≤ q₁ ^ ((((32 * s : ℕ) : ℝ))⁻¹) :=
    Real.rpow_le_rpow_of_exponent_ge hq0 hq1 hexp
  have h2 : q₁ ^ ((((32 * s : ℕ) : ℝ))⁻¹) = ell ^ (10 * s * (w + 1)) := by
    rw [hq, hlam]
    have e : 10 * s * (32 * s * (w + 1)) = (32 * s) * (10 * s * (w + 1)) := by ring
    rw [e, pow_mul_rpow_inv_natCast hell0.le h32]
  have h3 : ell ^ (10 * s * (w + 1)) ≤ ell * ell ^ w := by
    rw [← pow_succ']
    apply pow_le_pow_of_le_one hell0.le hell1
    have : 1 * (w + 1) ≤ 10 * s * (w + 1) := Nat.mul_le_mul_right _ (by omega)
    omega
  have hW0 : 0 ≤ ell ^ w := by positivity
  have hNe : 0 ≤ N ^ ε₁ := by positivity
  calc N ^ ε₁ * q₁ ^ ((1 - d) / 32) ≤ Q * (ell * ell ^ w) := by
        rw [h2] at h1
        exact mul_le_mul hNQ (h1.trans h3) (by positivity) (le_trans hNe hNQ)
    _ = (ell * Q) * ell ^ w := by ring
    _ ≤ 1 * ell ^ w := by gcongr
    _ = ell ^ w := one_mul _

/-- `1 ≤ Q² m*` for `m* = (N^{-ε₁}/4)^{2^D+2}/2`, `ε₁ = ε₃/(2^D+2)`. -/
theorem one_le_Q_sq_mstar {N ε₃ : ℝ} {D : ℕ} (hN0 : 0 < N)
    (hQ4 : 2 * 4 ^ (2 ^ D + 2) ≤ N ^ ε₃) :
    1 ≤ (N ^ ε₃) ^ 2 * ((N ^ (-(ε₃ / (2 ^ D + 2))) / 4) ^ (2 ^ D + 2) / 2) := by
  have hQ0 : 0 < N ^ ε₃ := Real.rpow_pos_of_pos hN0 _
  have e1 : (N ^ (-(ε₃ / (2 ^ D + 2)))) ^ (2 ^ D + 2) = (N ^ ε₃)⁻¹ := by
    rw [rpow_pow_eq hN0.le, ← Real.rpow_neg hN0.le]
    congr 1
    push_cast
    field_simp
  have e2 : (N ^ ε₃) ^ 2 * ((N ^ (-(ε₃ / (2 ^ D + 2))) / 4) ^ (2 ^ D + 2) / 2) =
      N ^ ε₃ / (2 * 4 ^ (2 ^ D + 2)) := by
    rw [div_pow, e1]
    field_simp
  rw [e2, le_div_iff₀ (by positivity), one_mul]
  exact hQ4

/-- The Taylor error of the first jet at a pair level. -/
theorem taylor_err_le {N ε₁ Q ell : ℝ} {T s w : ℕ} (hell0 : 0 < ell) (hell1 : ell ≤ 1)
    (hs : 1 ≤ s) (hℓ : ell ^ (10 * s) = ((2 : ℝ) ^ T)⁻¹) (hNQ : N ^ ε₁ ≤ Q) (hQ0 : 0 ≤ Q) :
    N ^ ε₁ * (((2 : ℝ) ^ (T * (w + 3)))⁻¹) ^ ((11 : ℝ) / 10) ≤
      Q * ell ^ (10 * s * (w + 3)) * ell ^ (w + 3) := by
  have hH : ((2 : ℝ) ^ (T * (w + 3)))⁻¹ = ell ^ (10 * (s * (w + 3))) := by
    rw [two_pow_mul_inv, ← hℓ, ← pow_mul]; ring_nf
  have hH0 : 0 < ell ^ (10 * (s * (w + 3))) := by positivity
  have e11 : ((11 : ℝ) / 10) = 1 + ((10 : ℕ) : ℝ)⁻¹ := by norm_num
  have hpow : (ell ^ (10 * (s * (w + 3)))) ^ ((11 : ℝ) / 10) =
      ell ^ (10 * (s * (w + 3))) * ell ^ (s * (w + 3)) := by
    rw [e11, Real.rpow_add hH0, Real.rpow_one, pow_mul_rpow_inv_natCast hell0.le (by norm_num)]
  have hle : ell ^ (s * (w + 3)) ≤ ell ^ (w + 3) := by
    apply pow_le_pow_of_le_one hell0.le hell1
    exact Nat.le_mul_of_pos_left _ hs
  rw [hH, hpow]
  have e : 10 * s * (w + 3) = 10 * (s * (w + 3)) := by ring
  rw [e]
  calc N ^ ε₁ * (ell ^ (10 * (s * (w + 3))) * ell ^ (s * (w + 3)))
      ≤ Q * (ell ^ (10 * (s * (w + 3))) * ell ^ (w + 3)) := by
        apply mul_le_mul hNQ _ (by positivity) hQ0
        gcongr
    _ = Q * ell ^ (10 * (s * (w + 3))) * ell ^ (w + 3) := by ring

/-- The fit error `h^{M + 1/8}` dominates `ℓ^{10 s M + 2 s}`. -/
theorem theta_ge {ell h : ℝ} {s M : ℕ} (hell0 : 0 < ell) (hell1 : ell ≤ 1) (_hs : 1 ≤ s)
    (hℓ : ell ^ (10 * s) = h) : ell ^ (10 * s * M + 2 * s) ≤ h ^ ((M : ℝ) + 1 / 8) := by
  have hh0 : 0 < h := by rw [← hℓ]; positivity
  have hh1 : h ≤ 1 := by rw [← hℓ]; exact pow_le_one₀ hell0.le hell1
  have h5 : h ^ (((5 : ℕ) : ℝ)⁻¹) = ell ^ (2 * s) := by
    rw [← hℓ]
    have e : 10 * s = 5 * (2 * s) := by ring
    rw [e, pow_mul_rpow_inv_natCast hell0.le (by norm_num)]
  have h18 : h ^ (((5 : ℕ) : ℝ)⁻¹) ≤ h ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_exponent_ge hh0 hh1 (by norm_num)
  have hM : ell ^ (10 * s * M) = h ^ M := by rw [← hℓ, ← pow_mul]
  calc ell ^ (10 * s * M + 2 * s) = ell ^ (10 * s * M) * ell ^ (2 * s) := pow_add _ _ _
    _ = h ^ M * h ^ (((5 : ℕ) : ℝ)⁻¹) := by rw [hM, h5]
    _ ≤ h ^ M * h ^ ((1 : ℝ) / 8) := mul_le_mul_of_nonneg_left h18 (by positivity)
    _ = h ^ ((M : ℝ) + 1 / 8) := by rw [Real.rpow_add hh0, Real.rpow_natCast]

/-- The coefficient allowance. -/
theorem coeff_allow_le {N ε ε₃ B : ℝ} {D G : ℕ} (hN1 : 1 ≤ N) (hε₃0 : 0 ≤ ε₃)
    (hQ : (((D : ℝ) + 2) * 2 ^ (D + 1)) ≤ N ^ ε₃) (hB : B ≤ (N ^ ε₃) ^ G)
    (hε₃ε : ε₃ ≤ ε / (G + 3)) (_hε : 0 < ε) :
    (((D + 1 : ℕ) : ℝ) + 1) * (B * 2 ^ (D + 1)) ≤ N ^ ε := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg _
  have h1 : (((D + 1 : ℕ) : ℝ) + 1) * (B * 2 ^ (D + 1)) ≤ ((D : ℝ) + 2) * 2 ^ (D + 1) * (N ^ ε₃) ^ G := by
    push_cast
    have e : ((D : ℝ) + 1 + 1) * (B * 2 ^ (D + 1)) = ((D : ℝ) + 2) * 2 ^ (D + 1) * B := by ring
    rw [e]
    gcongr
  have h2 : ε₃ * (G + 1) ≤ ε := by
    rw [le_div_iff₀ (by positivity)] at hε₃ε
    nlinarith
  calc (((D + 1 : ℕ) : ℝ) + 1) * (B * 2 ^ (D + 1)) ≤ ((D : ℝ) + 2) * 2 ^ (D + 1) * (N ^ ε₃) ^ G := h1
    _ ≤ N ^ ε₃ * (N ^ ε₃) ^ G := by gcongr
    _ = (N ^ ε₃) ^ (G + 1) := by ring
    _ = N ^ (ε₃ * ((G + 1 : ℕ) : ℝ)) := rpow_pow_eq hN0.le _ _
    _ ≤ N ^ ε := rpow_le_rpow_of_le_exp hN1 (by push_cast; linarith)

/-- The duration allowance. -/
theorem duration_allow_le {N ε ε₃ : ℝ} {G : ℕ} (hN1 : 1 ≤ N) (hε₃0 : 0 ≤ ε₃)
    (hε₃ε : ε₃ ≤ ε / (G + 3)) (_hε : 0 < ε) : N ^ (-ε) * (N ^ ε₃) ^ 3 ≤ 1 := by
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN1
  have hG0 : (0 : ℝ) ≤ G := Nat.cast_nonneg _
  have h2 : ε₃ * 3 ≤ ε := by
    rw [le_div_iff₀ (by positivity)] at hε₃ε
    nlinarith
  rw [rpow_pow_eq hN0.le, rpow_add_of_one_le hN1]
  exact rpow_le_one_of_nonpos hN1 (by push_cast; linarith)

end

end Submission.Obl.k4_scalar_grid_polynomial_qualification.Jets
