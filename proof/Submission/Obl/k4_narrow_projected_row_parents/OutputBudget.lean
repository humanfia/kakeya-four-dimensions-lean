import Submission.Obl.k4_narrow_projected_row_parents.Model

/-!
# One subpower bound for the comparison output

`outputBudget H Rstable Llist Λ = 1 + 4H + 2Rstable + 2 Llist Λ` dominates at once the dense mass
floor `4H` after the comparison cut, the natural time and major widths `2Rstable`, and the partner
cardinality `2 Llist Λ^d` (`d ≤ 1`, `Λ ≥ 1`). It is subpower when its inputs are.
-/

namespace Submission.Obl.k4_narrow_projected_row_parents

open Filter

/-- The output budget. -/
def outputBudget (H Rstable Llist Λ : ℝ) : ℝ := 1 + 4 * H + 2 * Rstable + 2 * Llist * Λ

section

variable {H Rstable Llist Λ : ℝ}

theorem one_le_outputBudget (hH : 0 ≤ H) (hR : 0 ≤ Rstable) (hL : 0 ≤ Llist) (hΛ : 0 ≤ Λ) :
    1 ≤ outputBudget H Rstable Llist Λ := by
  unfold outputBudget
  have := mul_nonneg hL hΛ
  nlinarith

theorem mass_le_outputBudget (hR : 0 ≤ Rstable) (hL : 0 ≤ Llist) (hΛ : 0 ≤ Λ) :
    4 * H ≤ outputBudget H Rstable Llist Λ := by
  unfold outputBudget
  have := mul_nonneg hL hΛ
  nlinarith

theorem stable_le_outputBudget (hH : 0 ≤ H) (hL : 0 ≤ Llist) (hΛ : 0 ≤ Λ) :
    2 * Rstable ≤ outputBudget H Rstable Llist Λ := by
  unfold outputBudget
  have := mul_nonneg hL hΛ
  nlinarith

/-- The partner cardinality `2 Llist Λ^d` for `0 ≤ d ≤ 1` and `Λ ≥ 1`. -/
theorem card_le_outputBudget {d : ℝ} (hH : 0 ≤ H) (hR : 0 ≤ Rstable) (hL : 0 ≤ Llist)
    (hΛ : 1 ≤ Λ) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    2 * (Llist * Λ ^ d) ≤ outputBudget H Rstable Llist Λ := by
  unfold outputBudget
  have hΛd : Λ ^ d ≤ Λ := by
    calc Λ ^ d ≤ Λ ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hΛ hd1
      _ = Λ := Real.rpow_one Λ
  have h1 : Llist * Λ ^ d ≤ Llist * Λ := mul_le_mul_of_nonneg_left hΛd hL
  have h2 : 0 ≤ Llist * Λ := mul_nonneg hL (by linarith)
  nlinarith

end

/-- The output budget is subpower when its inputs are. -/
theorem subpow_outputBudget {N H Rstable Llist Λ : ℕ → ℝ} (hN : ∀ k, 1 ≤ N k)
    (hNlim : Tendsto N atTop atTop) (hH0 : ∀ k, 0 ≤ H k) (hR0 : ∀ k, 0 ≤ Rstable k)
    (hL0 : ∀ k, 0 ≤ Llist k) (hΛ0 : ∀ k, 0 ≤ Λ k)
    (hH : Model.Subpow N H) (hR : Model.Subpow N Rstable) (hL : Model.Subpow N Llist)
    (hΛ : Model.Subpow N Λ) :
    Model.Subpow N (fun k => outputBudget (H k) (Rstable k) (Llist k) (Λ k)) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  filter_upwards [hH _ hε2, hR _ hε2, hL _ (half_pos hε2), hΛ _ (half_pos hε2),
    ((tendsto_rpow_atTop hε2).comp hNlim).eventually_ge_atTop 9] with k h1 h2 h3 h4 h9
  simp only [Function.comp_apply] at h9
  have hNk : 0 < N k := lt_of_lt_of_le one_pos (hN k)
  have hhalf : N k ^ (ε / 2 / 2) * N k ^ (ε / 2 / 2) = N k ^ (ε / 2) := by
    rw [← Real.rpow_add hNk]; ring_nf
  have hX : 1 ≤ N k ^ (ε / 2) := by linarith
  have hLΛ : Llist k * Λ k ≤ N k ^ (ε / 2) := by
    rw [← hhalf]
    exact mul_le_mul h3 h4 (hΛ0 k) (Real.rpow_nonneg hNk.le _)
  have hsplit : N k ^ ε = N k ^ (ε / 2) * N k ^ (ε / 2) := by
    rw [← Real.rpow_add hNk]; ring_nf
  unfold outputBudget
  rw [hsplit]
  nlinarith

end Submission.Obl.k4_narrow_projected_row_parents
