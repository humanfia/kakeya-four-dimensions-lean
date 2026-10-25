import Submission.Obl.k4_horizontal_coefficient_count.Binning
import Submission.Lib.K4ContinuousPlanks.Discretization

namespace Submission.Obl.k4_horizontal_coefficient_count

open MeasureTheory Set

/-- A bounded set of trajectories has finitely many five-coordinate codes,
even though the velocity scale and scalar scale may be different. -/
theorem finite_horizontalCode {α : Type*} (b : α → Fin 6 → ℝ) (G : Set α)
    {χ a L : ℝ} (hχ : 0 < χ) (ha : 0 < a) (hL : 0 ≤ L)
    (hb : ∀ l ∈ G, ∀ i, |b l i| ≤ L) :
    (horizontalCode χ a ∘ b '' G).Finite := by
  let f (l : G) : Fin 5 → ℝ :=
    ![b l 3 / χ, b l 0 / a, b l 1 / a, b l 2 / a, b l 5 / a]
  have hf : ∀ l i, |f l i| ≤ L / χ + L / a := by
    intro l i
    fin_cases i <;> dsimp [f] <;> simp only [abs_div, abs_of_pos hχ, abs_of_pos ha]
    · exact (div_le_div_of_nonneg_right (hb l l.property 3) hχ.le).trans
        (le_add_of_nonneg_right (div_nonneg hL ha.le))
    · exact (div_le_div_of_nonneg_right (hb l l.property 0) ha.le).trans
        (le_add_of_nonneg_left (div_nonneg hL hχ.le))
    · exact (div_le_div_of_nonneg_right (hb l l.property 1) ha.le).trans
        (le_add_of_nonneg_left (div_nonneg hL hχ.le))
    · exact (div_le_div_of_nonneg_right (hb l l.property 2) ha.le).trans
        (le_add_of_nonneg_left (div_nonneg hL hχ.le))
    · exact (div_le_div_of_nonneg_right (hb l l.property 5) ha.le).trans
        (le_add_of_nonneg_left (div_nonneg hL hχ.le))
  have hfin := Submission.Lib.K4ContinuousPlanks.finite_range_floor_code
    f (L / χ + L / a) hf (by norm_num : (0 : ℝ) < 1)
  apply hfin.subset
  rintro q ⟨l, hl, rfl⟩
  refine ⟨⟨l, hl⟩, ?_⟩
  ext i
  fin_cases i <;> simp [f, horizontalCode]

end Submission.Obl.k4_horizontal_coefficient_count
