import Submission.Obl.k4_general_wide_layer_offset_comparison.DomainMenus

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Set
open scoped ENNReal

noncomputable section

/-- A width bounded by one loss times the slope mesh can be replaced by
its minimum with that mesh, at the cost of squaring the band loss. -/
theorem band_le_squared_loss {H β g : ℝ} (hH : 1 ≤ H) (hβ : 0 ≤ β)
    (hβg : β ≤ H * g) : H * β ≤ H ^ 2 * min β g := by
  by_cases hb : β ≤ g
  · rw [min_eq_left hb]
    exact mul_le_mul_of_nonneg_right (by nlinarith : H ≤ H ^ 2) hβ
  · rw [min_eq_right (le_of_not_ge hb)]
    exact (mul_le_mul_of_nonneg_left hβg (by linarith : 0 ≤ H)).trans_eq (by ring)

/-- Fixed short-domain codes remain available when the layer width exceeds
the slope mesh by a subpower factor. Their budget costs four powers of loss. -/
theorem exists_moving_domain_menu_relaxed
    {H β h g b : ℝ} (hH : 1 ≤ H) (hh : 0 < h) (hh1 : h ≤ 1)
    (hb : 0 < b) (hbβ : b ≤ β) (hbg : b ≤ g) (hβg : β ≤ H * g) (u v : ℝ) :
    ∃ D : Finset (ℤ × ℤ × ℤ),
      (D.card : ℝ) ≤ 240 * H ^ 4 * β / (h * b) ∧
      ∀ a w t : ℝ, t ∈ Icc (0 : ℝ) 1 →
        (∀ t' ∈ Icc (0 : ℝ) 1, |a + t' * w - u - t' * v| ≤ H * β) →
        movingDomainCode h g b a w t ∈ D := by
  have hβ : 0 ≤ β := hb.le.trans hbβ
  obtain ⟨D, hcard, hcover⟩ := exists_moving_domain_menu
    (H := H ^ 2) (β := min β g) (by nlinarith) hh hh1 hb
    (le_min hbβ hbg) (min_le_right _ _) u v
  refine ⟨D, ?_, ?_⟩
  · calc
      (D.card : ℝ) ≤ 240 * (H ^ 2) ^ 2 * min β g / (h * b) := hcard
      _ = 240 * H ^ 4 * min β g / (h * b) := by ring
      _ ≤ 240 * H ^ 4 * β / (h * b) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity)) (by positivity)
  · intro a w t ht hband
    exact hcover a w t ht (fun t' ht' =>
      (hband t' ht').trans (band_le_squared_loss hH hβ hβg))

/-- All short-code choices retain the original whole-layer width in their
reference budget, even when the slope mesh is smaller than that width. -/
theorem exists_moving_domain_menus_with_budget_relaxed
    {ι : Type*} [Fintype ι] {H h g b : ℝ}
    (hH : 1 ≤ H) (hh : 0 < h) (hh1 : h ≤ 1) (hb : 0 < b) (hbg : b ≤ g)
    (β u v : ι → ℝ) (hbβ : ∀ i, b ≤ β i) (hβg : ∀ i, β i ≤ H * g)
    (w : ι → ℝ≥0∞) :
    ∃ D : ι → Finset (ℤ × ℤ × ℤ),
      (∀ i a v' t, t ∈ Icc (0 : ℝ) 1 →
        (∀ t' ∈ Icc (0 : ℝ) 1, |a + t' * v' - u i - t' * v i| ≤ H * β i) →
        movingDomainCode h g b a v' t ∈ D i) ∧
      (∑ i, ((D i).card : ℝ≥0∞) * (ENNReal.ofReal (h * b) * w i)) ≤
        ENNReal.ofReal (240 * H ^ 4) * ∑ i, ENNReal.ofReal (β i) * w i := by
  obtain ⟨D, hcover, hbudget⟩ := exists_moving_domain_menus_with_budget
    (H := H ^ 2) (by nlinarith) hh hh1 hb (fun i => min (β i) g) u v
    (fun i => le_min (hbβ i) hbg) (fun _ => min_le_right _ _) w
  refine ⟨D, ?_, ?_⟩
  · intro i a v' t ht hband
    exact hcover i a v' t ht (fun t' ht' =>
      (hband t' ht').trans (band_le_squared_loss hH (hb.le.trans (hbβ i)) (hβg i)))
  · calc
      _ ≤ ENNReal.ofReal (240 * (H ^ 2) ^ 2) *
          ∑ i, ENNReal.ofReal (min (β i) g) * w i := hbudget
      _ ≤ ENNReal.ofReal (240 * (H ^ 2) ^ 2) *
          ∑ i, ENNReal.ofReal (β i) * w i := by
        apply mul_le_mul' le_rfl
        exact Finset.sum_le_sum fun i _ =>
          mul_le_mul' (ENNReal.ofReal_le_ofReal (min_le_left _ _)) le_rfl
      _ = _ := by rw [show (240 : ℝ) * (H ^ 2) ^ 2 = 240 * H ^ 4 by ring]

end
end Submission.Obl.k4_general_wide_layer_offset_comparison
