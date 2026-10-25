/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/ParentFrameBounds.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.ParentCommonFrame
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonSheetFrame

/-! The actual common-to-parent matrix is small on sufficiently short domains. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain

noncomputable section

theorem parentFromCommonMatrix_rows_small {K Q q χ g m ρ : ℝ}
    (hK : 1 ≤ K) (hQ : 0 < Q) (hq : 0 < q) (hχ : 0 < χ) (hg : 0 < g)
    (hg1 : g ≤ 1) (hm : 0 < m) (hρ : 0 < ρ)
    (hqsmall : q ≤ ρ * Q / 10000) (hχsmall : χ ≤ ρ * (Q * g) / 10000)
    (hmsmall : m ≤ ρ * (Q * g) / 10000)
    (c : Fin 5 → ℝ) (u : Code) (hc : |c 4| ≤ K)
    (hmajor : |(u 1 : ℝ) * χ| ≤ 2 * K)
    (hslope : |(u 3 : ℝ) * g - c 3 - c 4 * ((u 1 : ℝ) * χ)| ≤ 3 * K * g) :
    ∀ i, (∑ j, |parentFromCommonMatrix K Q q χ g m c u i j|) ≤ ρ / 20 := by
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hQg : 0 < Q * g := mul_pos hQ hg
  have hden32 : 0 < 32 * K * Q := by positivity
  have hden16 : 0 < 16 * K * Q * g := by positivity
  have hratioq : 0 ≤ q / Q := by positivity
  have hratioχ : 0 ≤ χ / (Q * g) := by positivity
  have hratiom : 0 ≤ m / (Q * g) := by positivity
  have hratioq' : q / Q ≤ ρ / 10000 := (div_le_iff₀ hQ).mpr (by nlinarith only [hqsmall])
  have hratioχ' : χ / (Q * g) ≤ ρ / 10000 := (div_le_iff₀ hQg).mpr (by nlinarith only [hχsmall])
  have hratiom' : m / (Q * g) ≤ ρ / 10000 := (div_le_iff₀ hQg).mpr (by nlinarith only [hmsmall])
  have htotal : 100 * (q / Q + χ / (Q * g) + m / (Q * g)) ≤ ρ / 20 := by
    linarith only [hratioq', hratioχ', hratiom', hρ.le]
  have hdenQ : Q ≤ 32 * K * Q := by
    have hh := mul_le_mul_of_nonneg_right hK hQ.le
    nlinarith only [hh, hQ.le]
  have hdenG32 : Q * g ≤ 32 * K * Q := by
    have hh := mul_le_mul_of_nonneg_left (show g ≤ 32 * K by linarith only [hK, hg1]) hQ.le
    nlinarith only [hh]
  have hdenG16 : Q * g ≤ 16 * K * Q * g := by
    have hh := mul_le_mul_of_nonneg_right hK hQg.le
    nlinarith only [hh, hQg.le]
  have h00 : |100 * q / (32 * K * Q)| ≤ 100 * (q / Q) := by
    rw [abs_of_pos (by positivity)]
    calc
      _ ≤ 100 * q / Q := div_le_div_of_nonneg_left (by positivity) hQ hdenQ
      _ = _ := by ring
  have h10 : |100 * q * ((u 1 : ℝ) * χ) / (32 * K * Q)| ≤ 100 * (q / Q) := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 100 * q), abs_of_pos hden32]
    calc
      _ ≤ 100 * q * (2 * K) / (32 * K * Q) := by gcongr
      _ = (25 / 4 : ℝ) * (q / Q) := by field_simp; ring
      _ ≤ _ := by nlinarith only [hratioq]
  have h11 : |100 * χ / (32 * K * Q)| ≤ 100 * (χ / (Q * g)) := by
    rw [abs_of_pos (by positivity)]
    calc
      _ ≤ 100 * χ / (Q * g) := div_le_div_of_nonneg_left (by positivity) hQg hdenG32
      _ = _ := by ring
  have h20 : |100 * q * ((u 3 : ℝ) * g - c 3 - c 4 * ((u 1 : ℝ) * χ)) / (16 * K * Q * g)| ≤
      100 * (q / Q) := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : 0 < 100 * q), abs_of_pos hden16]
    calc
      _ ≤ 100 * q * (3 * K * g) / (16 * K * Q * g) := by gcongr
      _ = (75 / 4 : ℝ) * (q / Q) := by field_simp; ring
      _ ≤ _ := by nlinarith only [hratioq]
  have h21 : |-(100 * c 4 * χ) / (16 * K * Q * g)| ≤ 100 * (χ / (Q * g)) := by
    rw [abs_div, abs_neg, abs_mul, abs_mul, abs_of_pos hden16,
      abs_of_pos (by norm_num : (0 : ℝ) < 100), abs_of_pos hχ]
    calc
      _ ≤ 100 * K * χ / (16 * K * Q * g) := by gcongr
      _ = (25 / 4 : ℝ) * (χ / (Q * g)) := by field_simp; ring
      _ ≤ _ := by nlinarith only [hratioχ]
  have h22 : |100 * m / (16 * K * Q * g)| ≤ 100 * (m / (Q * g)) := by
    rw [abs_of_pos (by positivity)]
    calc
      _ ≤ 100 * m / (Q * g) := div_le_div_of_nonneg_left (by positivity) hQg hdenG16
      _ = _ := by ring
  rw [parentFromCommonMatrix_eq hK0.ne' hQ.ne' hg.ne']
  intro i
  fin_cases i <;> simp only [Fin.sum_univ_three]
  · change |100 * q / (32 * K * Q)| + |(0 : ℝ)| + |(0 : ℝ)| ≤ ρ / 20
    simp only [abs_zero, add_zero]
    linarith only [h00, htotal, hratioχ, hratiom]
  · change |100 * q * ((u 1 : ℝ) * χ) / (32 * K * Q)| +
      |100 * χ / (32 * K * Q)| + |(0 : ℝ)| ≤ ρ / 20
    simp only [abs_zero, add_zero]
    linarith only [h10, h11, htotal, hratiom]
  · change |100 * q * ((u 3 : ℝ) * g - c 3 - c 4 * ((u 1 : ℝ) * χ)) / (16 * K * Q * g)| +
      |-(100 * c 4 * χ) / (16 * K * Q * g)| + |100 * m / (16 * K * Q * g)| ≤ ρ / 20
    linarith only [h20, h21, h22, htotal]

/-- Literal common domains of an actual true packet satisfy the matrix bound.
The row derivative controls the large-looking tilted term after rounding. -/
theorem actual_parent_matrix_rows_small {K Q q χ g m ρ t : ℝ}
    (hK : 1 ≤ K) (hQ : 0 < Q) (hq : 0 < q) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hg : 0 < g) (hg1 : g ≤ 1) (hχg : χ ≤ g) (hm : 0 < m) (hρ : 0 < ρ)
    (hqsmall : q ≤ ρ * Q / 10000) (hχsmall : χ ≤ ρ * (Q * g) / 10000)
    (hmsmall : m ≤ ρ * (Q * g) / 10000)
    (b : Fin 6 → ℝ) (c : Fin 5 → ℝ) (hc : |c 4| ≤ K) (hb : |b 3| ≤ K)
    (hslope : |b 4 - c 3 - c 4 * b 3| ≤ K * g) :
    ∀ i, (∑ j, |parentFromCommonMatrix K Q q χ g m c (code q χ g m b t) i j|) ≤ ρ / 20 :=
  parentFromCommonMatrix_rows_small hK hQ hq hχ hg hg1 hm hρ hqsmall hχsmall hmsmall c _ hc
    (rounded_major_velocity_bound hK hχ hχ1 b hb) (rounded_parent_slope hK hχ hg hχg b c hc hslope)

/-- Actual true-packet incidences give the full complex-ball containment needed
by affine sheet composition. The center is exactly the old native-frame point. -/
theorem actual_parent_sheet_ball {K Q q χ g m ρ t : ℝ}
    (hK : 1 ≤ K) (hQ : 0 < Q) (hq : 0 < q) (hχ : 0 < χ) (hχ1 : χ ≤ 1)
    (hg : 0 < g) (hg1 : g ≤ 1) (hχg : χ ≤ g) (hm : 0 < m) (hqg : q * g ≤ m)
    (hρ : 0 < ρ) (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hqsmall : q ≤ ρ * Q / 10000) (hχsmall : χ ≤ ρ * (Q * g) / 10000)
    (hmsmall : m ≤ ρ * (Q * g) / 10000)
    (b : Fin 6 → ℝ) (c : Fin 5 → ℝ) (offset : Fin 3 → ℝ)
    (hc : |c 4| ≤ K) (hb : |b 3| ≤ K)
    (hslope : |b 4 - c 3 - c 4 * b 3| ≤ K * g) :
    ∀ z ∈ Metric.ball (0 : EuclideanSpace ℂ (Fin 3)) 4,
      (WithLp.toLp 2 (fun i =>
        (((parentMatrix K Q g c).mulVec (physicalOffset q χ m (code q χ g m b t)) + offset) i : ℂ) +
          ∑ j, (parentFromCommonMatrix K Q q χ g m c (code q χ g m b t) i j : ℂ) * z j) :
            EuclideanSpace ℂ (Fin 3)) ∈
      Metric.ball
        (Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison.emb
          (WithLp.toLp 2 (Submission.Lib.K4AffineMeshCaps.affineBase (parentMatrix K Q g c) offset (point b t)))) ρ := by
  exact common_sheet_ball_containment (parentMatrix K Q g c) offset hq hχ hm hρ
    (code q χ g m b t) (point b t) (coords_norm_le hq hχ hg hm hqg b ht)
    (actual_parent_matrix_rows_small hK hQ hq hχ hχ1 hg hg1 hχg hm hρ hqsmall hχsmall hmsmall b c hc hb hslope)

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.CommonDomain
