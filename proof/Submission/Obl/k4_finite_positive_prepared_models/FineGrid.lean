import Submission.Obl.k4_finite_positive_prepared_models.Original

namespace Submission.Obl.k4_finite_positive_prepared_models

/-- A uniform positive grid has exactly the frozen first-depth and mesh bounds. -/
theorem fineGrid_uniform (m : ℕ) (hm : 0 < m) (gain ρ : ℝ)
    (hmesh : 1 / (m : ℝ) ≤ ρ * gain) :
    FineGrid m (fun i => ((i : ℝ) + 1) / m) gain ρ := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨⟨hm, by simpa using div_pos one_pos hm', ?_, ?_⟩, by simpa using hmesh, ?_⟩
  · intro i _
    apply (div_lt_div_iff_of_pos_right hm').mpr
    push_cast
    linarith
  · have hl : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
    have hl' : ((m - 1 : ℕ) : ℝ) + 1 = m := by exact_mod_cast hl
    dsimp only
    rw [hl']
    exact div_self hm'.ne'
  · intro i _
    calc
      ((↑(i + 1) : ℝ) + 1) / m - ((i : ℝ) + 1) / m = 1 / m := by
        push_cast
        ring
      _ ≤ _ := hmesh

/-- The fine finite grids required by any positive requested gain exist. -/
theorem exists_fineGrid (gain ρ : ℝ) (hg : 0 < gain) (hρ : 0 < ρ) :
    ∃ (m : ℕ) (s : ℕ → ℝ), FineGrid m s gain ρ := by
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / (ρ * gain))
  have hm' : (0 : ℝ) < m := (by positivity : (0 : ℝ) < 1 / (ρ * gain)).trans hm
  have hm0 : 0 < m := by exact_mod_cast hm'
  refine ⟨m, _, fineGrid_uniform m hm0 gain ρ ?_⟩
  apply (div_le_iff₀ hm').mpr
  have h := (div_lt_iff₀ (mul_pos hρ hg)).mp hm
  nlinarith only [h]

end Submission.Obl.k4_finite_positive_prepared_models
