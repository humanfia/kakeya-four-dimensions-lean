import Submission.Obl.k4_tempered_grid_selection.Exponents

namespace Submission.Obl.k4_narrow_projected_row_parents

/-- Every mesh in a compact power band is exactly a power at an exponent in
that band. This lets uniform original caps read non-power aligned widths. -/
theorem exists_mesh_exponent {N χ a b : ℝ} (hN : 1 < N)
    (hlo : N ^ (-b) ≤ χ) (hhi : χ ≤ N ^ (-a)) :
    ∃ v : ℝ, a ≤ v ∧ v ≤ b ∧ N ^ (-v) = χ := by
  have hχ : 0 < χ := (Real.rpow_pos_of_pos (zero_lt_one.trans hN) _).trans_le hlo
  let v := Submission.Obl.k4_tempered_grid_selection.logarithmicExponent N χ
  have hv : N ^ (-v) = χ :=
    Submission.Obl.k4_tempered_grid_selection.rpow_neg_logarithmicExponent hN hχ
  have hmono := Real.strictMono_rpow_of_base_gt_one hN
  refine ⟨v, ?_, ?_, hv⟩
  · have h := hmono.le_iff_le.mp (show N ^ (-v) ≤ N ^ (-a) by rw [hv]; exact hhi)
    linarith
  · have h := hmono.le_iff_le.mp (show N ^ (-b) ≤ N ^ (-v) by rw [hv]; exact hlo)
    linarith

end Submission.Obl.k4_narrow_projected_row_parents
