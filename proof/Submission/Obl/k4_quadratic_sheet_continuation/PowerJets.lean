import Submission.Obl.k4_quadratic_sheet_continuation.CauchyEstimates

namespace Submission.Obl.k4_quadratic_sheet_continuation

open Set Metric
open scoped ContDiff

/-- A fixed finite collection of Cauchy estimates can be absorbed into one
power of `A`, independently of the base dimension. -/
theorem exists_power_jet_ball_bound (q : ℕ) :
    ∃ L : ℝ, 0 < L ∧ ∀ (n : ℕ) (A : ℝ), 2 ≤ A →
      ∀ (a : EuclideanSpace ℂ (Fin n)) (f : EuclideanSpace ℂ (Fin n) → ℂ)
        (V : ℝ), 0 ≤ V → ContDiffOn ℂ ∞ f (ball a A⁻¹) →
        (∀ z ∈ closedBall a ((8 * A)⁻¹), ‖f z‖ ≤ V) →
        ∀ j : ℕ, j ≤ q → ‖iteratedFDeriv ℂ j f a‖ ≤ A ^ L * V := by
  classical
  choose c hc hcauchy using fun i : Fin (q + 1) => exists_iteratedFDeriv_ball_bound (i : ℕ)
  let K := (∑ i : Fin (q + 1), c i * (8 : ℝ) ^ (i : ℕ)) + 1
  have hK1 : 1 ≤ K := by
    dsimp [K]
    have hsum : 0 ≤ ∑ i : Fin (q + 1), c i * (8 : ℝ) ^ (i : ℕ) :=
      Finset.sum_nonneg (fun i _ => mul_nonneg (hc i).le (by positivity))
    linarith
  have hciK (i : Fin (q + 1)) : c i * (8 : ℝ) ^ (i : ℕ) ≤ K := by
    have hi := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin (q + 1) => c j * (8 : ℝ) ^ (j : ℕ))
      (fun j _ => mul_nonneg (hc j).le (by positivity)) (Finset.mem_univ i)
    dsimp [K]
    linarith
  obtain ⟨t, ht, ht'⟩ := exists_nat_pow_near hK1 (by norm_num : (1 : ℝ) < 2)
  let L : ℕ := q + (t + 1)
  refine ⟨(L : ℝ), by dsimp [L]; positivity, ?_⟩
  intro n A hA a f V hV hf hnorm j hj
  have hApos : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  let r := (8 * A)⁻¹
  have hr : 0 < r := by dsimp [r]; positivity
  have h8r : 8 * r = A⁻¹ := by dsimp [r]; field_simp
  have hf2 : ContDiffOn ℂ ∞ f (ball a (2 * r)) :=
    hf.mono (ball_subset_ball (by rw [← h8r]; linarith))
  let i : Fin (q + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  have hnorm' : ∀ z ∈ ball a r, ‖f z‖ ≤ V := fun z hz => hnorm z (ball_subset_closedBall hz)
  have hder := hcauchy i f a r V hr hV hf2 hnorm'
  have hscale : c i * V / r ^ j = (c i * 8 ^ j) * A ^ j * V := by
    simp [r, div_eq_mul_inv, inv_pow, mul_pow]
    ring
  change ‖iteratedFDeriv ℂ j f a‖ ≤ _ at hder
  rw [hscale] at hder
  have hKpow : K ≤ A ^ (t + 1) := ht'.le.trans (pow_le_pow_left₀ (by norm_num) hA _)
  rw [Real.rpow_natCast]
  calc
    ‖iteratedFDeriv ℂ j f a‖ ≤ (c i * 8 ^ j) * A ^ j * V := hder
    _ ≤ K * A ^ q * V := by gcongr; exact hciK i
    _ ≤ A ^ (t + 1) * A ^ q * V := by gcongr
    _ = A ^ L * V := by dsimp [L]; rw [pow_add]; ring

end Submission.Obl.k4_quadratic_sheet_continuation
