import Mathlib

/-!
# The scalar obstruction to long terminal charts

These estimates keep polynomial growth separate from the subpower losses.  The
geometric comparison supplies the factor `q⁻³`, hence the final exponent `3 * h`.
-/

namespace Submission.Obl.k4_discrete_of_terminal_charts

open Filter

/-- An upper bound that is smaller than every positive power of the scale. -/
def SubpowerBound (N K : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε

theorem subpower_const {N : ℕ → ℝ} (hN : Tendsto N atTop atTop) (C : ℝ) :
    SubpowerBound N (fun _ => C) := by
  intro ε hε
  exact ((tendsto_rpow_atTop hε).comp hN).eventually (eventually_ge_atTop C)

theorem subpower_mul {N H K : ℕ → ℝ} (hN : ∀ k, 0 < N k)
    (_hH₀ : ∀ k, 0 ≤ H k) (hK₀ : ∀ k, 0 ≤ K k)
    (hH : SubpowerBound N H) (hK : SubpowerBound N K) :
    SubpowerBound N (fun k => H k * K k) := by
  intro ε hε
  filter_upwards [hH (ε / 2) (by positivity), hK (ε / 2) (by positivity)] with k hkH hkK
  calc
    H k * K k ≤ N k ^ (ε / 2) * N k ^ (ε / 2) :=
      mul_le_mul hkH hkK (hK₀ k) (Real.rpow_pos_of_pos (hN k) _).le
    _ = N k ^ ε := by rw [← Real.rpow_add (hN k)]; congr 1; ring

theorem subpower_pow {N K : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (hK₀ : ∀ k, 0 ≤ K k) (hK : SubpowerBound N K) (p : ℕ) :
    SubpowerBound N (fun k => K k ^ p) := by
  intro ε hε
  by_cases hp : p = 0
  · filter_upwards [] with k
    simpa [hp] using Real.one_le_rpow (hN k) hε.le
  · have hp' : 0 < (p : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hp
    filter_upwards [hK (ε / (p : ℝ)) (by positivity)] with k hk
    calc
      K k ^ p ≤ (N k ^ (ε / (p : ℝ))) ^ p := pow_le_pow_left₀ (hK₀ k) hk p
      _ = N k ^ ε := by
        rw [← Real.rpow_natCast,
          ← Real.rpow_mul (le_trans zero_le_one (hN k))]
        congr 1
        field_simp

theorem subpower_subsequence {N K : ℕ → ℝ} (hK : SubpowerBound N K)
    {ψ : ℕ → ℕ} (hψ : StrictMono ψ) :
    SubpowerBound (N ∘ ψ) (K ∘ ψ) := by
  intro ε hε
  exact hψ.tendsto_atTop.eventually (hK ε hε)

/-- A subpower factor cannot reverse a strict inequality of growth exponents. -/
theorem exponent_le_of_subpower_comparison {N K : ℕ → ℝ}
    (hN : Tendsto N atTop atTop) (hK : SubpowerBound N K) {a b : ℝ}
    (h : ∀ᶠ k in atTop, N k ^ a ≤ K k * N k ^ b) : a ≤ b := by
  by_contra hab
  have he : 0 < (a - b) / 2 := by linarith
  have hN₁ : ∀ᶠ k in atTop, 1 < N k := hN.eventually (eventually_gt_atTop 1)
  obtain ⟨k, hkN, hkK, hk⟩ := (hN₁.and ((hK _ he).and h)).exists
  have hp : N k ^ a ≤ N k ^ ((a - b) / 2 + b) := by
    calc
      N k ^ a ≤ K k * N k ^ b := hk
      _ ≤ N k ^ ((a - b) / 2) * N k ^ b := by gcongr
      _ = N k ^ ((a - b) / 2 + b) := (Real.rpow_add (by linarith) _ _).symm
  have := (Real.rpow_le_rpow_left_iff hkN).mp hp
  linarith

/-- The lower polynomial density gain forces every chart time exponent to be large. -/
theorem horizon_exponent_lower_bound {N K n a q : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK₀ : ∀ k, 0 ≤ K k) (hK : SubpowerBound N K)
    (ha : ∀ k, 0 < a k) (_hq : ∀ k, 0 < q k) {γ h : ℝ}
    (hlower : ∀ᶠ k in atTop, a k * N k ^ γ ≤ n k)
    (hupper : ∀ᶠ k in atTop, n k ≤ K k * a k / q k ^ 3)
    (htime : ∀ᶠ k in atTop, N k ^ (-h) ≤ q k) : γ ≤ 3 * h := by
  apply exponent_le_of_subpower_comparison hNt hK
  filter_upwards [hlower, hupper, htime] with k hkL hkU hkT
  have hNk : 0 < N k := by linarith [hN k]
  have hden : 0 < N k ^ (-h) := Real.rpow_pos_of_pos hNk _
  have hcancel : N k ^ γ ≤ K k / q k ^ 3 := by
    apply (mul_le_mul_iff_right₀ (ha k)).mp
    calc
      a k * N k ^ γ ≤ n k := hkL
      _ ≤ K k * a k / q k ^ 3 := hkU
      _ = a k * (K k / q k ^ 3) := by ring
  calc
    N k ^ γ ≤ K k / q k ^ 3 := hcancel
    _ ≤ K k / (N k ^ (-h)) ^ 3 :=
      div_le_div_of_nonneg_left (hK₀ k) (by positivity)
        (pow_le_pow_left₀ hden.le hkT 3)
    _ = K k * N k ^ (3 * h) := by
      rw [Real.rpow_neg hNk.le, inv_pow, div_inv_eq_mul, ← Real.rpow_natCast,
        ← Real.rpow_mul hNk.le]
      congr 2
      ring

/-- The upper dyadic time exponent is the required lower bound on time length. -/
theorem dyadic_time_lower_bound {N h : ℝ} {T : ℕ} (hN : 0 < N)
    (hT : (2 : ℝ) ^ T ≤ N ^ h) :
    N ^ (-h) ≤ ((2 : ℝ) ^ T)⁻¹ := by
  rw [Real.rpow_neg hN.le]
  simpa only [one_div] using one_div_le_one_div_of_le (by positivity) hT

end Submission.Obl.k4_discrete_of_terminal_charts
