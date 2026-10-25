import Mathlib

/-!
# A real anchor point

A nonzero complex polynomial in `n` variables does not vanish at some real point of norm at most
`1/2`: otherwise it vanishes on a product grid of `deg + 1` real points per coordinate, and the
combinatorial Nullstellensatz (`MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`) makes it zero.
-/

namespace Submission.Obl.k4_algebraic_sheet_bound

open MvPolynomial

theorem norm_toLp_ofReal {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) :
    ‖(WithLp.toLp 2 (fun i : Fin n => (x i : ℂ)) : EuclideanSpace ℂ (Fin n))‖ = ‖x‖ := by
  simp [EuclideanSpace.norm_eq]

/-- A nonzero complex polynomial does not vanish at some real point of norm at most `1/2`. -/
theorem exists_real_anchor {n : ℕ} {a : MvPolynomial (Fin n) ℂ} (ha : a ≠ 0) :
    ∃ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 / 2 ∧ eval (fun i => (x i : ℂ)) a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  set m := a.totalDegree
  set ε : ℝ := 1 / (2 * ((m : ℝ) + 1) * ((n : ℝ) + 1)) with hε
  have hεpos : 0 < ε := by positivity
  let g : ℕ → ℂ := fun k => ((k * ε : ℝ) : ℂ)
  let S : Fin n → Finset ℂ := fun _ => (Finset.range (m + 1)).image g
  have hinj : Function.Injective g := by
    intro k l hkl
    have h1 : (k : ℝ) * ε = l * ε := Complex.ofReal_injective hkl
    have h2 : (k : ℝ) = l := mul_right_cancel₀ hεpos.ne' h1
    exact_mod_cast h2
  have hcard : ∀ i, (S i).card = m + 1 := fun i => by
    simp [S, Finset.card_image_of_injective _ hinj]
  apply ha
  apply eq_zero_of_eval_zero_at_prod_finset a S
  · intro i
    rw [hcard i]
    exact Nat.lt_succ_of_le (degreeOf_le_totalDegree a i)
  · intro x hx
    choose k hk hkx using fun i => Finset.mem_image.mp (hx i)
    let y : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => (k i : ℝ) * ε)
    have hmε : (m : ℝ) * ε ≤ 1 / (2 * ((n : ℝ) + 1)) := by
      rw [hε]
      have hm : (m : ℝ) ≤ (m : ℝ) + 1 := by linarith
      rw [mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [(by positivity : (0 : ℝ) ≤ 2 * ((n : ℝ) + 1))]
    have hyi : ∀ i, y i ^ 2 ≤ ((m : ℝ) * ε) ^ 2 := by
      intro i
      have hki : (k i : ℝ) ≤ m := by
        have := Finset.mem_range.mp (hk i)
        exact_mod_cast Nat.lt_succ_iff.mp this
      simp only [y]
      exact pow_le_pow_left₀ (by positivity) (by nlinarith) 2
    have hsq : ‖y‖ ^ 2 ≤ 1 / 4 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ i, y i ^ 2 ≤ ∑ _i : Fin n, ((m : ℝ) * ε) ^ 2 := Finset.sum_le_sum fun i _ => hyi i
        _ = n * ((m : ℝ) * ε) ^ 2 := by simp
        _ ≤ n * (1 / (2 * ((n : ℝ) + 1))) ^ 2 := by
            gcongr
        _ ≤ 1 / 4 := by
            rw [div_pow, one_pow, mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
            nlinarith
    have hy : ‖y‖ ≤ 1 / 2 := by nlinarith [norm_nonneg y]
    have hxy : x = fun i => ((y i : ℝ) : ℂ) := by
      funext i
      simp [y, g, ← hkx i]
    rw [hxy]
    exact hcon y hy

end Submission.Obl.k4_algebraic_sheet_bound
