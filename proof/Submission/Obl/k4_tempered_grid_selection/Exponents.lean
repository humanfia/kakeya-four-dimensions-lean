import Mathlib

namespace Submission.Obl.k4_tempered_grid_selection

noncomputable def logarithmicExponent (n v : ℝ) : ℝ := -Real.log v / Real.log n

noncomputable def boundedExponent (C n v : ℝ) : ℝ :=
  max (-C) (min C (logarithmicExponent n v))

lemma abs_boundedExponent (C n v : ℝ) (hC : 0 ≤ C) :
    |boundedExponent C n v| ≤ C := by
  exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma boundedExponent_eq {C n v : ℝ} (hn : 1 < n)
    (hlo : n ^ (-C) ≤ v) (hhi : v ≤ n ^ C) :
    boundedExponent C n v = logarithmicExponent n v := by
  have hn0 : 0 < n := by linarith
  have hv : 0 < v := (Real.rpow_pos_of_pos hn0 _).trans_le hlo
  have hlogn : 0 < Real.log n := Real.log_pos hn
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) hlo
  have hu := Real.log_le_log hv hhi
  rw [Real.log_rpow hn0] at hl hu
  have helo : -C ≤ logarithmicExponent n v := by
    rw [logarithmicExponent, le_div_iff₀ hlogn]
    nlinarith
  have hehi : logarithmicExponent n v ≤ C := by
    rw [logarithmicExponent, div_le_iff₀ hlogn]
    nlinarith
  exact max_eq_right (helo.trans_eq (min_eq_right hehi).symm) |>.trans (min_eq_right hehi)

lemma rpow_neg_logarithmicExponent {n v : ℝ} (hn : 1 < n) (hv : 0 < v) :
    n ^ (-logarithmicExponent n v) = v := by
  have hn0 : 0 < n := by linarith
  have hlogn : Real.log n ≠ 0 := (Real.log_pos hn).ne'
  rw [Real.rpow_def_of_pos hn0]
  have heq : Real.log n * -logarithmicExponent n v = Real.log v := by
    unfold logarithmicExponent
    field_simp
  rw [heq, Real.exp_log hv]

lemma power_band_of_exponent_fit {n v a δ : ℝ} (hn : 1 < n) (hv : 0 < v)
    (hfit : |logarithmicExponent n v - a| ≤ δ) :
    n ^ (-a - δ) ≤ v ∧ v ≤ n ^ (-a + δ) := by
  have hfit' := abs_le.mp hfit
  rw [← rpow_neg_logarithmicExponent hn hv]
  exact ⟨Real.rpow_le_rpow_of_exponent_le hn.le (by linarith),
    Real.rpow_le_rpow_of_exponent_le hn.le (by linarith)⟩

end Submission.Obl.k4_tempered_grid_selection
