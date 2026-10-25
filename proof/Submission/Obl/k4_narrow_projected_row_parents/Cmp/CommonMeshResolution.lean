/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/CommonMeshResolution.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomainCaps
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.ParentCommonFrame

/-! One primitive physical mesh resolves all occupied common frames. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

noncomputable section

theorem coordMatrix_rows_resolved {K q χ g m δ σ : ℝ}
    (hK : 1 ≤ K) (hq : 0 < q) (hχ : 0 < χ) (hm : 0 < m) (hδ : 0 ≤ δ)
    (c : Code) (hmajor : |(c 1 : ℝ) * χ| ≤ 2 * K) (hminor : |(c 3 : ℝ) * g| ≤ 2 * K)
    (hδq : (2 * K + 1) * δ ≤ 100 * q * σ)
    (hδχ : (2 * K + 1) * δ ≤ 100 * χ * σ)
    (hδm : (2 * K + 1) * δ ≤ 100 * m * σ) :
    ∀ i, (∑ j, |coordMatrix q χ g m c i j| * δ) ≤ σ := by
  have h100 : (0 : ℝ) < 100 := by norm_num
  have hdenq : 0 < 100 * q := mul_pos h100 hq
  have hdenχ : 0 < 100 * χ := mul_pos h100 hχ
  have hdenm : 0 < 100 * m := mul_pos h100 hm
  have hmajor' : |(c 1 : ℝ)| * χ ≤ 2 * K := by
    simpa only [abs_mul, abs_of_pos hχ] using hmajor
  have hcoef : δ ≤ (2 * K + 1) * δ := by
    have h := mul_le_mul_of_nonneg_right (by linarith only [hK] : (1 : ℝ) ≤ 2 * K + 1) hδ
    simpa only [one_mul] using h
  intro i
  fin_cases i <;> simp only [Fin.sum_univ_three]
  · change |1 / (100 * q)| * δ + |(0 : ℝ)| * δ + |(0 : ℝ)| * δ ≤ σ
    simp only [abs_of_pos (one_div_pos.mpr hdenq), abs_zero, zero_mul, add_zero]
    rw [one_div_mul_eq_div]
    apply (div_le_iff₀ hdenq).mpr
    nlinarith only [hcoef, hδq]
  · change |-(c 1 : ℝ) / 100| * δ + |1 / (100 * χ)| * δ + |(0 : ℝ)| * δ ≤ σ
    simp only [abs_div, abs_neg, abs_of_pos h100, abs_one, abs_of_pos hdenχ,
      abs_zero, zero_mul, add_zero]
    have heq : |(c 1 : ℝ)| / 100 * δ + 1 / (100 * χ) * δ =
        (|(c 1 : ℝ)| * χ + 1) * δ / (100 * χ) := by field_simp
    rw [heq]
    apply (div_le_iff₀ hdenχ).mpr
    have h := (mul_le_mul_of_nonneg_right (add_le_add hmajor' le_rfl) hδ).trans hδχ
    nlinarith only [h]
  · change |-((c 3 : ℝ) * g) / (100 * m)| * δ + |(0 : ℝ)| * δ + |1 / (100 * m)| * δ ≤ σ
    simp only [abs_div, abs_neg, abs_of_pos hdenm, abs_one, abs_zero, zero_mul, add_zero]
    have heq : |(c 3 : ℝ) * g| / (100 * m) * δ + 1 / (100 * m) * δ =
        (|(c 3 : ℝ) * g| + 1) * δ / (100 * m) := by ring
    rw [heq]
    apply (div_le_iff₀ hdenm).mpr
    have h := (mul_le_mul_of_nonneg_right (add_le_add hminor le_rfl) hδ).trans hδm
    nlinarith only [h]

theorem actual_common_mesh_resolution {K q χ g m δ σ t : ℝ}
    (hK : 1 ≤ K) (hq : 0 < q) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hg : 0 < g) (hg1 : g ≤ 1) (hm : 0 < m) (hδ : 0 ≤ δ)
    (b : Fin 6 → ℝ) (hb₃ : |b 3| ≤ K) (hb₄ : |b 4| ≤ K)
    (hδq : (2 * K + 1) * δ ≤ 100 * q * σ)
    (hδχ : (2 * K + 1) * δ ≤ 100 * χ * σ)
    (hδm : (2 * K + 1) * δ ≤ 100 * m * σ) :
    ∀ i, (∑ j, |coordMatrix q χ g m (code q χ g m b t) i j| * δ) ≤ σ := by
  have hminor : |((code q χ g m b t) 3 : ℝ) * g| ≤ 2 * K := by
    have hf := Submission.Lib.K4VelocityStrips.midpoint_floor_center_bound hg (b 4)
    have h := abs_sub_abs_le_abs_sub ((⌊b 4 / g⌋ : ℝ) * g) (b 4)
    rw [abs_sub_comm ((⌊b 4 / g⌋ : ℝ) * g) (b 4)] at h
    change |(⌊b 4 / g⌋ : ℝ) * g| ≤ 2 * K
    linarith only [hf, h, hb₄, hg1, hK]
  exact coordMatrix_rows_resolved hK hq hχ hm hδ _
    (rounded_major_velocity_bound hK hχ hχ1 b hb₃) hminor hδq hδχ hδm

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
