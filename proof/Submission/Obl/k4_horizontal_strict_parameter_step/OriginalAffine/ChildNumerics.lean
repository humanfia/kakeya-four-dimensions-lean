/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/OriginalAffine/ChildNumerics.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.OriginalAffine.MeshChoice
import Mathlib.Tactic.GCongr

namespace Submission.Obl.k4_horizontal_strict_parameter_step

/-- The normalized cell cap divided by the original child witness floor is
polynomial in the unchanged slack.  In particular the child volume cancels. -/
lemma original_child_cap_ratio {K q g A : ℝ} (hK : 1 ≤ K) (hq : 0 < q)
    (hg : 0 < g) (hA : 0 < A) (hgq : g ≤ K * q) :
    512 * (2 * K + 7) * (K * A) * (q / 2) * (K * q) * (K * q * g) ≤
      2304 * K ^ 8 * (q ^ 4 * A / K ^ 3) := by
  have hK0 : 0 < K := by linarith
  calc
    _ = 256 * (2 * K + 7) * K ^ 3 * A * q ^ 3 * g := by ring
    _ ≤ 256 * (9 * K) * K ^ 3 * A * q ^ 3 * (K * q) := by
      gcongr
      linarith
    _ = _ := by field_simp; ring

lemma original_child_comparison_error {K m C a₀ : ℝ} (hK : 1 ≤ K)
    (hm : 0 < m) (ha₀ : 0 ≤ a₀) (hC : 0 ≤ C)
    (hratio : C ≤ 2304 * K ^ 8 * m) :
    2 * K * a₀ + 48 * C * (2 * K * a₀) / m ≤ 262144 * K ^ 9 * a₀ := by
  have hK0 : 0 < K := by linarith
  have hK8 : 1 ≤ K ^ 8 := one_le_pow₀ hK
  have hlo : 2 * K * a₀ ≤ 2 * K ^ 9 * a₀ := by
    have hh := mul_le_mul_of_nonneg_right hK8 (by positivity : 0 ≤ 2 * K * a₀)
    convert hh using 1 <;> ring
  calc
    _ ≤ 2 * K * a₀ + 48 * (2304 * K ^ 8 * m) * (2 * K * a₀) / m := by
      gcongr
    _ = 2 * K * a₀ + 221184 * K ^ 9 * a₀ := by field_simp; ring
    _ ≤ 262144 * K ^ 9 * a₀ := by nlinarith [hlo, mul_nonneg (pow_nonneg hK0.le 9) ha₀]

/-- The native horizontal jet and its normal component control both ordinary
spatial slopes, uniformly over unit times. -/
lemma spatial_slopes_of_native_jet {A B K q E t : ℝ}
    (hK : 1 ≤ K) (hq : 0 < q) (hq1 : q ≤ 1) (hE : 0 ≤ E) (ht : |t| ≤ 1)
    (hnormal : |B| ≤ E / q ^ 2) (hrow : |A + t * B| ≤ 8 * K * E / q) :
    |A| ≤ 9 * K * E / q ^ 2 ∧ |B| ≤ 9 * K * E / q ^ 2 := by
  have hK0 : 0 ≤ K := by linarith
  have hquot : 0 ≤ E / q ^ 2 := div_nonneg hE (sq_nonneg _)
  have hA : |A| ≤ 8 * K * E / q + E / q ^ 2 := by
    calc
      _ = |(A + t * B) - t * B| := by congr 1; ring
      _ ≤ |A + t * B| + |t * B| := abs_sub _ _
      _ ≤ 8 * K * E / q + E / q ^ 2 := by
        apply add_le_add hrow
        rw [abs_mul]
        exact (mul_le_mul ht hnormal (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  constructor
  · apply (le_div_iff₀ (sq_pos_of_pos hq)).mpr
    calc
      _ ≤ (8 * K * E / q + E / q ^ 2) * q ^ 2 :=
        mul_le_mul_of_nonneg_right hA (sq_nonneg _)
      _ = 8 * K * E * q + E := by field_simp <;> ring
      _ ≤ 9 * K * E := by
        have hh := mul_le_mul_of_nonneg_left hq1 (by positivity : 0 ≤ 8 * K * E)
        nlinarith [hh, mul_le_mul_of_nonneg_right hK hE]
  · exact hnormal.trans (by
      have h := mul_le_mul_of_nonneg_right hK hquot
      rw [show 9 * K * E / q ^ 2 = 9 * (K * (E / q ^ 2)) by ring]
      nlinarith)

end Submission.Obl.k4_horizontal_strict_parameter_step
