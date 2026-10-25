import Submission.Obl.k4_finite_row_graph_assembly.Projection

-- Relocated from this LOT tree, o072, x0245/3b29ff1,
-- Submission/Obl/k4_row_incidence_graph_construction/Ratios.lean.

namespace Submission.Obl.k4_finite_row_graph_assembly

theorem ratio_bounds {R u₁ u₂ u : ℝ} (hR : 2 ≤ R)
    (h₁ : |u₁| ≤ R) (h₂ : |u₂| ≤ R) (hu : |u| ≤ R)
    (hs₁ : 1 / R ≤ |u - u₁|) (hs₂ : 1 / R ≤ |u₂ - u|) :
    1 / R ^ 3 ≤ |ratio u₁ u₂ u| ∧ |ratio u₁ u₂ u| ≤ R ^ 3 ∧
      |projectionFactor u₁ u₂ u| ≤ R ^ 3 := by
  have hRpos : 0 < R := by linarith
  have hdpos : 0 < |u₂ - u| := (one_div_pos.mpr hRpos).trans_le hs₂
  have hnpos : 0 < |u - u₁| := (one_div_pos.mpr hRpos).trans_le hs₁
  have hnum : |u - u₁| ≤ 2 * R := (abs_sub _ _).trans (by linarith)
  have hden : |u₂ - u| ≤ 2 * R := (abs_sub _ _).trans (by linarith)
  have hbase : |u₂ - u₁| ≤ 2 * R := (abs_sub _ _).trans (by linarith)
  have hR3 : 2 * R ^ 2 ≤ R ^ 3 := by nlinarith [sq_nonneg R]
  have hinv : 1 / R ^ 3 ≤ (1 / R) / (2 * R) := by
    rw [div_div]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [sq_nonneg R])
  have hupper : (2 * R) / (1 / R) = 2 * R ^ 2 := by field_simp
  dsimp [ratio, projectionFactor]
  rw [abs_div, abs_div]
  refine ⟨hinv.trans ?_, ?_, ?_⟩
  · exact div_le_div₀ (by positivity) hs₁ hdpos hden
  · exact (div_le_div₀ (by positivity) hnum (by positivity) hs₂).trans
      (hupper.le.trans hR3)
  · exact (div_le_div₀ (by positivity) hbase (by positivity) hs₂).trans
      (hupper.le.trans hR3)

theorem ratio_inverse_lipschitz {R u₁ u₂ u v : ℝ} (hR : 1 ≤ R)
    (h₁ : |u₁| ≤ R) (h₂ : |u₂| ≤ R) (hu : |u| ≤ R) (hv : |v| ≤ R)
    (hs : 1 / R ≤ |u₂ - u₁|) (hdu : u₂ - u ≠ 0) (hdv : u₂ - v ≠ 0) :
    |u - v| ≤ 4 * R ^ 3 * |ratio u₁ u₂ u - ratio u₁ u₂ v| := by
  have hRpos : 0 < R := by linarith
  have he : (u - v) * (u₂ - u₁) =
      (ratio u₁ u₂ u - ratio u₁ u₂ v) * (u₂ - u) * (u₂ - v) := by
    dsimp [ratio]
    field_simp
    ring
  have heabs := congrArg abs he
  simp only [abs_mul] at heabs
  have hduB : |u₂ - u| ≤ 2 * R := (abs_sub _ _).trans (by linarith)
  have hdvB : |u₂ - v| ≤ 2 * R := (abs_sub _ _).trans (by linarith)
  have hp : |u - v| * |u₂ - u₁| ≤
      |ratio u₁ u₂ u - ratio u₁ u₂ v| * ((2 * R) * (2 * R)) := by
    rw [heabs]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (mul_le_mul hduB hdvB (abs_nonneg _) (by positivity)) (abs_nonneg _)
  have hs' : 1 ≤ R * |u₂ - u₁| := by
    have := (div_le_iff₀ hRpos).mp hs
    nlinarith
  calc
    |u - v| ≤ R * (|u - v| * |u₂ - u₁|) := by
      have := mul_le_mul_of_nonneg_left hs' (abs_nonneg (u - v))
      nlinarith
    _ ≤ R * (|ratio u₁ u₂ u - ratio u₁ u₂ v| * ((2 * R) * (2 * R))) :=
      mul_le_mul_of_nonneg_left hp hRpos.le
    _ = _ := by ring

end Submission.Obl.k4_finite_row_graph_assembly
