import Submission.Lib.K4FinitePlankAtlases.Basic

/-!
Adapted from: here:o049

Original finite-atlas proofs developed by session x0147, through commit e50df50.
The weighted plank input is a parameter; no obligation module is imported.
-/

namespace Submission.Lib.K4FinitePlankAtlases

private theorem plane_inner_coordinates (x y : Plane) :
    inner ℝ x y = x 0 * y 0 + x 1 * y 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, mul_comm]

/-- The columns of a spatial plank frame are its two scaled orthonormal axes. -/
noncomputable def plankFrame (a b : ℝ) (e₁ e₂ : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a * e₁ 0, b * e₂ 0; a * e₁ 1, b * e₂ 1]

noncomputable def plankFrameInverse (a b : ℝ) (e₁ e₂ : Plane) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![e₁ 0 / a, e₁ 1 / a; e₂ 0 / b, e₂ 1 / b]

private theorem axis_identities {e₁ e₂ : Plane} (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1)
    (ho : inner ℝ e₁ e₂ = 0) :
    e₁ 0 ^ 2 + e₁ 1 ^ 2 = 1 ∧ e₂ 0 ^ 2 + e₂ 1 ^ 2 = 1 ∧
      e₁ 0 * e₂ 0 + e₁ 1 * e₂ 1 = 0 := by
  have hx₁ := plane_inner_coordinates e₁ e₁
  have hx₂ := plane_inner_coordinates e₂ e₂
  rw [real_inner_self_eq_norm_sq, h₁] at hx₁
  rw [real_inner_self_eq_norm_sq, h₂] at hx₂
  rw [plane_inner_coordinates] at ho
  exact ⟨by nlinarith, by nlinarith, ho⟩

/-- A normalized plank has exactly the product of its physical widths as Jacobian. -/
theorem plankFrame_abs_det {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {e₁ e₂ : Plane}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0) :
    |Matrix.det (plankFrame a b e₁ e₂)| = a * b := by
  obtain ⟨hs₁, hs₂, hd⟩ := axis_identities h₁ h₂ ho
  let d := e₁ 0 * e₂ 1 - e₁ 1 * e₂ 0
  have hdsq : d ^ 2 = 1 := by
    calc
      _ = (e₁ 0 ^ 2 + e₁ 1 ^ 2) * (e₂ 0 ^ 2 + e₂ 1 ^ 2) -
          (e₁ 0 * e₂ 0 + e₁ 1 * e₂ 1) ^ 2 := by dsimp [d]; ring
      _ = 1 := by rw [hs₁, hs₂, hd]; norm_num
  have hda : |d| = 1 := by nlinarith [sq_abs d, abs_nonneg d]
  have hdet : Matrix.det (plankFrame a b e₁ e₂) = a * b * d := by
    simp only [plankFrame, Matrix.det_fin_two]
    dsimp [d]
    ring
  rw [hdet, abs_mul, abs_mul, abs_of_pos ha, abs_of_pos hb, hda, mul_one]

/-- The inverse frame records the two orthogonal components divided by their widths. -/
theorem plankFrame_inverse {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {e₁ e₂ : Plane}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0) :
    (plankFrame a b e₁ e₂)⁻¹ = plankFrameInverse a b e₁ e₂ := by
  obtain ⟨hs₁, hs₂, hd⟩ := axis_identities h₁ h₂ ho
  have hmul : plankFrameInverse a b e₁ e₂ * plankFrame a b e₁ e₂ =
      !![e₁ 0 ^ 2 + e₁ 1 ^ 2, (b / a) * (e₁ 0 * e₂ 0 + e₁ 1 * e₂ 1);
        (a / b) * (e₁ 0 * e₂ 0 + e₁ 1 * e₂ 1), e₂ 0 ^ 2 + e₂ 1 ^ 2] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [plankFrameInverse, plankFrame, Matrix.mul_apply, Fin.sum_univ_two] <;>
      field_simp
  apply Matrix.inv_eq_left_inv
  rw [hmul, hs₁, hs₂, hd]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem plankFrame_inverse_action {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) {e₁ e₂ : Plane}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0) (z : Plane) :
    Matrix.toEuclideanLin ((plankFrame a b e₁ e₂)⁻¹) z =
      WithLp.toLp 2 ![inner ℝ z e₁ / a, inner ℝ z e₂ / b] := by
  rw [plankFrame_inverse ha hb h₁ h₂ ho]
  ext i
  fin_cases i <;>
    simp [plankFrameInverse, Matrix.toEuclideanLin, Matrix.toLpLin_apply, plane_inner_coordinates, Matrix.vecHead, Matrix.vecTail] <;> ring

/-- Whole-time orthogonal rectangle containment is a whole-time Euclidean chart fit. -/
theorem plankFrame_fit {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {e₁ e₂ z : Plane}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0)
    (hz₁ : |inner ℝ z e₁| ≤ a) (hz₂ : |inner ℝ z e₂| ≤ b) :
    ‖Matrix.toEuclideanLin ((plankFrame a b e₁ e₂)⁻¹) z‖ ≤ 2 := by
  have h0 : |inner ℝ z e₁ / a| ≤ 1 := by
    rw [abs_div, abs_of_pos ha]
    exact (div_le_one ha).mpr hz₁
  have h1 : |inner ℝ z e₂ / b| ≤ 1 := by
    rw [abs_div, abs_of_pos hb]
    exact (div_le_one hb).mpr hz₂
  rw [plankFrame_inverse_action ha.ne' hb.ne' h₁ h₂ ho]
  have hn := EuclideanSpace.real_norm_sq_eq
    (WithLp.toLp 2 ![inner ℝ z e₁ / a, inner ℝ z e₂ / b])
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hn
  have hs0 : (inner ℝ z e₁ / a) ^ 2 ≤ 1 := by
    nlinarith [sq_abs (inner ℝ z e₁ / a), abs_nonneg (inner ℝ z e₁ / a)]
  have hs1 : (inner ℝ z e₂ / b) ^ 2 ≤ 1 := by
    nlinarith [sq_abs (inner ℝ z e₂ / b), abs_nonneg (inner ℝ z e₂ / b)]
  nlinarith [norm_nonneg (WithLp.toLp 2 ![inner ℝ z e₁ / a, inner ℝ z e₂ / b])]

/-- The frame-entry budget is controlled by the physical side lengths. -/
theorem plankFrame_entries {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {e₁ e₂ : Plane}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) :
    (∑ i : Fin 2, ∑ j : Fin 2, |plankFrame a b e₁ e₂ i j|) ≤ 2 * (a + b) := by
  have hc₁ (i : Fin 2) : |e₁ i| ≤ 1 := by simpa only [h₁, Real.norm_eq_abs] using PiLp.norm_apply_le e₁ i
  have hc₂ (i : Fin 2) : |e₂ i| ≤ 1 := by simpa only [h₂, Real.norm_eq_abs] using PiLp.norm_apply_le e₂ i
  simp [Fin.sum_univ_two, plankFrame, abs_mul, abs_of_pos ha, abs_of_pos hb]
  have h0 := mul_le_mul_of_nonneg_left (hc₁ 0) ha.le
  have h1 := mul_le_mul_of_nonneg_left (hc₁ 1) ha.le
  have h2 := mul_le_mul_of_nonneg_left (hc₂ 0) hb.le
  have h3 := mul_le_mul_of_nonneg_left (hc₂ 1) hb.le
  linarith

/-- Reciprocal side lengths likewise control every inverse-frame coefficient. -/
theorem plankFrame_inverse_entries {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {e₁ e₂ : Plane}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0) :
    (∑ i : Fin 2, ∑ j : Fin 2, |(plankFrame a b e₁ e₂)⁻¹ i j|) ≤
      2 * (a⁻¹ + b⁻¹) := by
  have hc₁ (i : Fin 2) : |e₁ i| ≤ 1 := by simpa only [h₁, Real.norm_eq_abs] using PiLp.norm_apply_le e₁ i
  have hc₂ (i : Fin 2) : |e₂ i| ≤ 1 := by simpa only [h₂, Real.norm_eq_abs] using PiLp.norm_apply_le e₂ i
  rw [plankFrame_inverse ha.ne' hb.ne' h₁ h₂ ho]
  simp [Fin.sum_univ_two, plankFrameInverse, abs_div, abs_of_pos ha, abs_of_pos hb]
  have h0 := div_le_div_of_nonneg_right (hc₁ 0) ha.le
  have h1 := div_le_div_of_nonneg_right (hc₁ 1) ha.le
  have h2 := div_le_div_of_nonneg_right (hc₂ 0) hb.le
  have h3 := div_le_div_of_nonneg_right (hc₂ 1) hb.le
  simp only [one_div] at h0 h1 h2 h3
  linarith

/-- This is the exact entry/inverse-entry sum used in the terminal statement. -/
theorem plankFrame_entry_budget {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {e₁ e₂ : Plane}
    (h₁ : ‖e₁‖ = 1) (h₂ : ‖e₂‖ = 1) (ho : inner ℝ e₁ e₂ = 0) :
    (∑ i : Fin 2, ∑ j : Fin 2,
      (|plankFrame a b e₁ e₂ i j| + |(plankFrame a b e₁ e₂)⁻¹ i j|)) ≤
      2 * (a + b + a⁻¹ + b⁻¹) := by
  simp only [Finset.sum_add_distrib]
  have h := add_le_add (plankFrame_entries ha hb h₁ h₂)
    (plankFrame_inverse_entries ha hb h₁ h₂ ho)
  linarith

end Submission.Lib.K4FinitePlankAtlases
