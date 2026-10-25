import Mathlib

open Filter
open scoped Topology ENNReal

namespace Submission.Obl.k4_profile_density_bounds

lemma eventually_const_mul_rpow_lt {N : ℕ → ℝ}
    (hN : Tendsto N atTop atTop) {a b : ℝ} (hab : a < b) (A : ℝ) :
    ∀ᶠ k in atTop, A * N k ^ a < N k ^ b := by
  have ht : Tendsto (fun k => A * N k ^ (-(b - a))) atTop (𝓝 (A * 0)) :=
    tendsto_const_nhds.mul ((tendsto_rpow_neg_atTop (sub_pos.mpr hab)).comp hN)
  have hsmall : ∀ᶠ k in atTop, A * N k ^ (-(b - a)) < 1 :=
    ht.eventually (Iio_mem_nhds (by simpa using (show (0 : ℝ) < 1 by norm_num)))
  filter_upwards [hsmall, hN.eventually (eventually_gt_atTop (0 : ℝ))] with k hk hkN
  have heq : A * N k ^ a = (A * N k ^ (-(b - a))) * N k ^ b := by
    rw [mul_assoc, ← Real.rpow_add hkN]
    congr 2
    ring
  rw [heq]
  simpa using mul_lt_mul_of_pos_right hk (Real.rpow_pos_of_pos hkN b)

lemma eventually_subpower_pow_le {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (p : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k in atTop, K k ^ p ≤ N k ^ ε := by
  by_cases hp : p = 0
  · subst p
    exact Eventually.of_forall fun k => by simpa using Real.one_le_rpow (hN k) hε.le
  have hpR : (0 : ℝ) < p := by exact_mod_cast Nat.pos_of_ne_zero hp
  filter_upwards [hsub (ε / p) (div_pos hε hpR)] with k hk
  calc
    K k ^ p ≤ (N k ^ (ε / p)) ^ p := pow_le_pow_left₀ (by linarith [hK k]) hk p
    _ = N k ^ ε := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith [hN k])]
      congr 1
      exact div_mul_cancel₀ ε (ne_of_gt hpR)

lemma eventually_subpower_mul_rpow_lt {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (p : ℕ) {a b : ℝ} (hab : a < b) {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ k in atTop, A * K k ^ p * N k ^ a < N k ^ b := by
  have hε : 0 < (b - a) / 2 := by linarith
  filter_upwards [eventually_subpower_pow_le hN hK hsub p hε,
    eventually_const_mul_rpow_lt hNt (show (b - a) / 2 + a < b by linarith) A] with k hk hp
  calc
    A * K k ^ p * N k ^ a ≤ A * N k ^ ((b - a) / 2) * N k ^ a := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hA)
        (Real.rpow_nonneg (by linarith [hN k]) _)
    _ = A * N k ^ ((b - a) / 2 + a) := by
      rw [Real.rpow_add (by linarith [hN k])]; ring
    _ < _ := hp

lemma eventually_sum_lt_inv {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop)
    (hK : ∀ k, 1 ≤ K k)
    (hsub : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, K k ≤ N k ^ ε)
    (p : ℕ) {a b A : ℝ} (ha : 0 < a) (hb : 0 < b) (hA : 0 ≤ A) :
    ∀ᶠ k in atTop, A * K k ^ p * N k ^ (-a) + N k ^ (-b) < (K k)⁻¹ := by
  have hfirst := eventually_subpower_mul_rpow_lt hN hNt hK hsub (p + 1)
    (show -a < 0 by linarith) (show 0 ≤ 2 * A by positivity)
  have hsecond := eventually_subpower_mul_rpow_lt hN hNt hK hsub 1
    (show -b < 0 by linarith) (show (0 : ℝ) ≤ 2 by norm_num)
  filter_upwards [hfirst, hsecond] with k hk1 hk2
  simp only [Real.rpow_zero, pow_one, pow_succ] at hk1 hk2
  rw [← one_div]
  apply (lt_div_iff₀ (show 0 < K k by linarith [hK k])).2
  nlinarith

end Submission.Obl.k4_profile_density_bounds
