import Mathlib
import Submission.Obl.k4_finite_row_graph_assembly.Geometry

/-!
# Two-velocity interpolation: the pair fiber count

A row state `r : Fin 2 → ℤ` is compatible with a velocity `v` and a list `l` of
scalar evaluation bins when `r 0 + v * r 1` lies within `C` of an entry of `l`.
Two velocities separated by `1 / K` determine the row state up to a box of side
`O(K ^ 2 * C)` for each pair of list entries (interpolation), so few states are
compatible with both.
-/

open scoped BigOperators

namespace Submission.Obl.k4_two_velocity_row_list_completion

/-- States compatible with one fixed pair of list entries at two separated velocities
form a box of side `6 * K ^ 2 * C`. -/
theorem pair_entry_fiber_card (states : Finset (Fin 2 → ℤ)) {K C v₁ v₂ L₁ L₂ : ℝ}
    (hK : 1 ≤ K) (hC : 0 ≤ C) (hv₁ : |v₁| ≤ K) (hv₂ : |v₂| ≤ K)
    (hsep : 1 / K ≤ |v₂ - v₁|) :
    ((states.filter (fun r => |(r 0 : ℝ) + v₁ * (r 1 : ℝ) - L₁| ≤ C ∧
        |(r 0 : ℝ) + v₂ * (r 1 : ℝ) - L₂| ≤ C)).card : ℝ) ≤
      (12 * K ^ 2 * C + 2) ^ 2 := by
  have hdiam := Submission.Obl.k4_finite_row_graph_assembly.card_pi_grid_of_diameter
    (states.filter (fun r => |(r 0 : ℝ) + v₁ * (r 1 : ℝ) - L₁| ≤ C ∧
        |(r 0 : ℝ) + v₂ * (r 1 : ℝ) - L₂| ≤ C)) (R := 6 * K ^ 2 * C)
    (by positivity) (by
      intro r hr r' hr' j
      simp only [Finset.mem_filter] at hr hr'
      have h₁ : |((r 0 : ℝ) - r' 0) + v₁ * ((r 1 : ℝ) - r' 1)| ≤ 2 * C := by
        calc
          _ = |((r 0 : ℝ) + v₁ * (r 1 : ℝ) - L₁) - ((r' 0 : ℝ) + v₁ * (r' 1 : ℝ) - L₁)| := by
            congr 1; ring
          _ ≤ |(r 0 : ℝ) + v₁ * (r 1 : ℝ) - L₁| + |(r' 0 : ℝ) + v₁ * (r' 1 : ℝ) - L₁| :=
            abs_sub _ _
          _ ≤ 2 * C := by linarith [hr.2.1, hr'.2.1]
      have h₂ : |((r 0 : ℝ) - r' 0) + v₂ * ((r 1 : ℝ) - r' 1)| ≤ 2 * C := by
        calc
          _ = |((r 0 : ℝ) + v₂ * (r 1 : ℝ) - L₂) - ((r' 0 : ℝ) + v₂ * (r' 1 : ℝ) - L₂)| := by
            congr 1; ring
          _ ≤ |(r 0 : ℝ) + v₂ * (r 1 : ℝ) - L₂| + |(r' 0 : ℝ) + v₂ * (r' 1 : ℝ) - L₂| :=
            abs_sub _ _
          _ ≤ 2 * C := by linarith [hr.2.2, hr'.2.2]
      obtain ⟨hx₀, hx₁⟩ :=
        Submission.Obl.k4_finite_row_graph_assembly.row_error_of_two_evaluations
          hK hv₁ hv₂ hsep h₁ h₂
      have hKC : 0 ≤ K * C := mul_nonneg (by linarith) hC
      fin_cases j
      · simp only [Fin.zero_eta, Fin.isValue]
        linarith
      · simp only [Fin.mk_one, Fin.isValue]
        nlinarith)
  rw [Fintype.card_fin] at hdiam
  calc _ ≤ _ := hdiam
    _ = (12 * K ^ 2 * C + 2) ^ 2 := by ring

/-- The pair fiber: states compatible with both of two separated velocities. -/
theorem pair_fiber_card (states : Finset (Fin 2 → ℤ)) (l₁ l₂ : Finset ℤ)
    {K C v₁ v₂ : ℝ} (hK : 1 ≤ K) (hC : 0 ≤ C) (hv₁ : |v₁| ≤ K) (hv₂ : |v₂| ≤ K)
    (hsep : 1 / K ≤ |v₂ - v₁|) :
    ((states.filter (fun r => (∃ L ∈ l₁, |(r 0 : ℝ) + v₁ * (r 1 : ℝ) - (L : ℝ)| ≤ C) ∧
        (∃ L ∈ l₂, |(r 0 : ℝ) + v₂ * (r 1 : ℝ) - (L : ℝ)| ≤ C))).card : ℝ) ≤
      (l₁.card : ℝ) * l₂.card * (12 * K ^ 2 * C + 2) ^ 2 := by
  classical
  let G : ℤ × ℤ → Finset (Fin 2 → ℤ) := fun LL =>
    states.filter (fun r => |(r 0 : ℝ) + v₁ * (r 1 : ℝ) - (LL.1 : ℝ)| ≤ C ∧
      |(r 0 : ℝ) + v₂ * (r 1 : ℝ) - (LL.2 : ℝ)| ≤ C)
  have hsub : states.filter (fun r => (∃ L ∈ l₁, |(r 0 : ℝ) + v₁ * (r 1 : ℝ) - (L : ℝ)| ≤ C) ∧
        (∃ L ∈ l₂, |(r 0 : ℝ) + v₂ * (r 1 : ℝ) - (L : ℝ)| ≤ C)) ⊆
      (l₁ ×ˢ l₂).biUnion G := by
    intro r hr
    simp only [Finset.mem_filter] at hr
    obtain ⟨hrs, ⟨L₁, hL₁, h₁⟩, ⟨L₂, hL₂, h₂⟩⟩ := hr
    exact Finset.mem_biUnion.mpr ⟨(L₁, L₂), Finset.mem_product.mpr ⟨hL₁, hL₂⟩,
      Finset.mem_filter.mpr ⟨hrs, h₁, h₂⟩⟩
  calc
    _ ≤ (((l₁ ×ˢ l₂).biUnion G).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ LL ∈ l₁ ×ˢ l₂, ((G LL).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _LL ∈ l₁ ×ˢ l₂, (12 * K ^ 2 * C + 2) ^ 2 := by
      apply Finset.sum_le_sum
      intro LL _
      exact pair_entry_fiber_card states hK hC hv₁ hv₂ hsep
    _ = (l₁.card : ℝ) * l₂.card * (12 * K ^ 2 * C + 2) ^ 2 := by
      rw [Finset.sum_const, Finset.card_product, nsmul_eq_mul]
      push_cast
      ring

end Submission.Obl.k4_two_velocity_row_list_completion
