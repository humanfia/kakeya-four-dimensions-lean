import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Interface
import Submission.Obl.k4_profile_density_bounds.Asymptotics

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing

open Filter

theorem subpower_polynomial {N K : ℕ → ℝ}
    (hN : ∀ k, 1 ≤ N k) (hNt : Tendsto N atTop atTop) (hK : Subpower N K)
    {A : ℝ} (hA : 1 ≤ A) (p : ℕ) :
    Subpower N (fun k => A * K k ^ p) := by
  constructor
  · intro k
    have hp : 1 ≤ K k ^ p := one_le_pow₀ (hK.1 k)
    nlinarith
  · intro ε hε
    have h := Submission.Obl.k4_profile_density_bounds.eventually_subpower_mul_rpow_lt
      hN hNt hK.1 hK.2 p (a := 0) (b := ε) hε (A := A) (by linarith)
    filter_upwards [h] with k hk
    simpa only [Real.rpow_zero, mul_one] using hk.le

theorem subpower_max {N K L : ℕ → ℝ} (hK : Subpower N K) (hL : Subpower N L) :
    Subpower N (fun k => max (K k) (L k)) := by
  constructor
  · intro k
    exact (hK.1 k).trans (le_max_left _ _)
  · intro ε hε
    filter_upwards [hK.2 ε hε, hL.2 ε hε] with k hk hl
    exact max_le hk hl

/-- An eventual power bound extends to every sample by increasing its fixed exponent. -/
theorem uniform_nat_exponent {N f : ℕ → ℝ} (hN : ∀ k, 2 ≤ N k) {A : ℝ}
    (hbound : ∀ᶠ k in atTop, f k ≤ N k ^ A) :
    ∃ M : ℕ, ∀ k, f k ≤ N k ^ (M : ℝ) := by
  classical
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.mp hbound
  let R := ∑ k ∈ Finset.range k₀, |f k|
  obtain ⟨n₀, hn₀⟩ := pow_unbounded_of_one_lt R (by norm_num : (1 : ℝ) < 2)
  obtain ⟨nA, hnA⟩ := exists_nat_ge A
  refine ⟨max n₀ nA, ?_⟩
  intro k
  have hN1 : 1 ≤ N k := by linarith [hN k]
  by_cases hk : k₀ ≤ k
  · exact (hk₀ k hk).trans (Real.rpow_le_rpow_of_exponent_le hN1
      (hnA.trans (by exact_mod_cast (le_max_right n₀ nA))))
  · have hkR : f k ≤ R := (le_abs_self (f k)).trans
      (Finset.single_le_sum (fun i _ => abs_nonneg (f i))
        (Finset.mem_range.mpr (lt_of_not_ge hk)))
    calc
      f k ≤ R := hkR
      _ ≤ (2 : ℝ) ^ n₀ := hn₀.le
      _ ≤ N k ^ n₀ := pow_le_pow_left₀ (by norm_num) (hN k) _
      _ = N k ^ (n₀ : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ N k ^ (max n₀ nA : ℕ) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hN1 (by exact_mod_cast le_max_left n₀ nA)
      _ = N k ^ ((max n₀ nA : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm

theorem mesh_count_polynomial {N K L : ℝ} (hN : 2 ≤ N) (hK : 1 ≤ K)
    (hKN : K ≤ N) (hL : 0 ≤ L) :
    (2 * K / N ^ (-L) + 2) ^ 5 ≤ N ^ (5 * (L + 3)) := by
  have hNp : 0 < N := by linarith
  have hδ : 0 < N ^ (-L) := Real.rpow_pos_of_pos hNp _
  have hδ1 : N ^ (-L) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by linarith)
  have hdiv : K / N ^ (-L) ≤ N / N ^ (-L) :=
    div_le_div_of_nonneg_right hKN hδ.le
  have hdiv1 : 1 ≤ N / N ^ (-L) := (le_div_iff₀ hδ).mpr (by linarith)
  have hbase : 2 * K / N ^ (-L) + 2 ≤ N ^ (L + 3) := by
    calc
      _ ≤ 4 * N / N ^ (-L) := by simp only [mul_div_assoc]; nlinarith
      _ ≤ N ^ (3 : ℕ) / N ^ (-L) := by
        apply div_le_div_of_nonneg_right _ hδ.le
        nlinarith [sq_nonneg (N - 2)]
      _ = N ^ (L + 3) := by
        rw [← Real.rpow_natCast N 3, ← Real.rpow_sub hNp]
        congr 1
        ring
  have hp := pow_le_pow_left₀ (by positivity) hbase 5
  have heq : (N ^ (L + 3)) ^ (5 : ℕ) = N ^ (5 * (L + 3)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]
    congr 1
    ring
  exact hp.trans_eq heq

theorem time_count_polynomial {N m : ℝ} (hN : 2 ≤ N) :
    2 * (N ^ (-m))⁻¹ ≤ N ^ (m + 1) := by
  have hNp : 0 < N := by linarith
  rw [Real.rpow_neg hNp.le, inv_inv, Real.rpow_add hNp, Real.rpow_one]
  nlinarith [Real.rpow_pos_of_pos hNp m]

end Submission.Obl.k4_scalar_marked_coefficient_smoothing
