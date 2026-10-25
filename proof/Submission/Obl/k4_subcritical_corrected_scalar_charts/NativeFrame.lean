/- Adapted from this LOT tree, o249, session x0876, commit b1a68828d72d39f6f06511039c5be605a582a5dc,
   `Submission/Obl/k4_horizontal_endpoint_three_projections/NativeFrame.lean`. Original attributions are retained below. -/
/- Adapted from this LOT tree, o218, session x0760, commit ce93c8df6e603b8044f968da8a9087dc728f3bb6,
   `Submission/Obl/k4_horizontal_endpoint_wide_return/NativeFrame.lean`. -/
import Mathlib

namespace Submission.Obl.k4_subcritical_corrected_scalar_charts

open Set MeasureTheory MvPolynomial

noncomputable section

/-- Unit coordinates for a horizontal native box. The transverse scale is h². -/
def nativeFrame (h t₀ p r v w τ : ℝ) (z : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![(z 0 - t₀) / h, (z 1 - (p + z 0 * v)) / h,
    (z 2 - (r - z 0 * w) - τ * (z 1 - (p + z 0 * v))) / h ^ 2]

theorem measurable_nativeFrame (h t₀ p r v w τ : ℝ) :
    Measurable (nativeFrame h t₀ p r v w τ) := by
  apply Measurable.of_eval
  intro i
  fin_cases i <;> simp only [nativeFrame, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] <;> fun_prop

def nativeUnframe (h t₀ p r v w τ : ℝ) (u : Fin 3 → ℝ) : Fin 3 → ℝ :=
  ![t₀ + h * u 0, p + (t₀ + h * u 0) * v + h * u 1,
    r - (t₀ + h * u 0) * w + τ * (h * u 1) + h ^ 2 * u 2]

theorem nativeUnframe_frame {h : ℝ} (hh : h ≠ 0)
    (t₀ p r v w τ : ℝ) (z : Fin 3 → ℝ) :
    nativeUnframe h t₀ p r v w τ (nativeFrame h t₀ p r v w τ z) = z := by
  ext i
  fin_cases i <;> simp [nativeFrame, nativeUnframe] <;> field_simp <;> ring

theorem nativeFrame_unframe {h : ℝ} (hh : h ≠ 0)
    (t₀ p r v w τ : ℝ) (u : Fin 3 → ℝ) :
    nativeFrame h t₀ p r v w τ (nativeUnframe h t₀ p r v w τ u) = u := by
  ext i
  fin_cases i <;> simp [nativeFrame, nativeUnframe] <;> field_simp <;> ring

/-- The ordinary grid in normalized coordinates becomes a sheared physical box.
Its volume factor is h⁴ times the normalized mesh volume. -/
theorem nativeFrame_cell_box {h σ : ℝ} (hh : 0 < h) (hσ : 0 < σ)
    (t₀ p r v w τ : ℝ) (z : Fin 3 → ℝ) (q : Fin 3 → ℤ)
    (hq : (fun i => ⌊nativeFrame h t₀ p r v w τ z i / σ⌋) = q) :
    |z 0 - (t₀ + h * σ * (q 0 : ℝ))| ≤ h * σ ∧
    |z 1 - (p + h * σ * (q 1 : ℝ) + z 0 * v)| ≤ h * σ ∧
    |z 2 - (r + h ^ 2 * σ * (q 2 : ℝ) + τ * (h * σ * (q 1 : ℝ)) - z 0 * w) -
      τ * (z 1 - (p + h * σ * (q 1 : ℝ) + z 0 * v))| ≤ h ^ 2 * σ := by
  have hcell (i : Fin 3) :
      |nativeFrame h t₀ p r v w τ z i - σ * (q i : ℝ)| ≤ σ := by
    have hlo := (le_div_iff₀ hσ).mp (Int.floor_le (nativeFrame h t₀ p r v w τ z i / σ))
    have hhi := (div_lt_iff₀ hσ).mp (Int.lt_floor_add_one (nativeFrame h t₀ p r v w τ z i / σ))
    have hi := congrFun hq i
    rw [hi] at hlo hhi
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hs0 : |h * (nativeFrame h t₀ p r v w τ z 0 - σ * (q 0 : ℝ))| ≤ h * σ := by
    simpa only [abs_mul, abs_of_pos hh] using
      mul_le_mul_of_nonneg_left (hcell 0) hh.le
  have hs1 : |h * (nativeFrame h t₀ p r v w τ z 1 - σ * (q 1 : ℝ))| ≤ h * σ := by
    simpa only [abs_mul, abs_of_pos hh] using
      mul_le_mul_of_nonneg_left (hcell 1) hh.le
  have hs2 : |h ^ 2 * (nativeFrame h t₀ p r v w τ z 2 - σ * (q 2 : ℝ))| ≤ h ^ 2 * σ := by
    simpa only [abs_mul, abs_of_nonneg (sq_nonneg h)] using
      mul_le_mul_of_nonneg_left (hcell 2) (sq_nonneg h)
  simp only [nativeFrame, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at hs0 hs1 hs2
  constructor
  · convert hs0 using 1 <;> congr 1 <;> field_simp [hh.ne'] <;> ring
  constructor
  · convert hs1 using 1 <;> congr 1 <;> field_simp [hh.ne'] <;> ring
  · convert hs2 using 1 <;> congr 1 <;> field_simp [hh.ne'] <;> ring

/-- An affine native field expressed in the normalized box. -/
def nativeAffinePolynomial (L : Fin 4 → ℝ) (h t₀ p r v w τ : ℝ) :
    MvPolynomial (Fin 3) ℝ :=
  C (L 0 + L 1 * t₀ + L 2 * (p + t₀ * v) + L 3 * (r - t₀ * w)) +
    C (h * (L 1 + v * L 2 - w * L 3)) * X 0 +
    C (h * (L 2 + τ * L 3)) * X 1 + C (h ^ 2 * L 3) * X 2

theorem nativeAffinePolynomial_degree (L : Fin 4 → ℝ) (h t₀ p r v w τ : ℝ) :
    (nativeAffinePolynomial L h t₀ p r v w τ).totalDegree ≤ 1 := by
  have hCX (a : ℝ) (i : Fin 3) : (C a * X i : MvPolynomial (Fin 3) ℝ).totalDegree ≤ 1 := by
    exact (totalDegree_mul _ _).trans (by simp only [totalDegree_C, totalDegree_X]; omega)
  have hadd (P Q : MvPolynomial (Fin 3) ℝ) (hP : P.totalDegree ≤ 1) (hQ : Q.totalDegree ≤ 1) :
      (P + Q).totalDegree ≤ 1 := (totalDegree_add _ _).trans (max_le hP hQ)
  unfold nativeAffinePolynomial
  exact hadd _ _ (hadd _ _ (hadd _ _ (by rw [totalDegree_C]; omega) (hCX _ _)) (hCX _ _)) (hCX _ _)

theorem eval_nativeAffinePolynomial (L : Fin 4 → ℝ) (h t₀ p r v w τ : ℝ)
    (u : Fin 3 → ℝ) :
    eval u (nativeAffinePolynomial L h t₀ p r v w τ) =
      L 0 + L 1 * nativeUnframe h t₀ p r v w τ u 0 +
        L 2 * nativeUnframe h t₀ p r v w τ u 1 +
          L 3 * nativeUnframe h t₀ p r v w τ u 2 := by
  simp only [nativeAffinePolynomial, eval_add, eval_mul, eval_C, eval_X, nativeUnframe,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

theorem eval_nativeAffinePolynomial_frame (L : Fin 4 → ℝ) {h : ℝ} (hh : h ≠ 0)
    (t₀ p r v w τ : ℝ) (z : Fin 3 → ℝ) :
    eval (nativeFrame h t₀ p r v w τ z) (nativeAffinePolynomial L h t₀ p r v w τ) =
      L 0 + L 1 * z 0 + L 2 * z 1 + L 3 * z 2 := by
  rw [eval_nativeAffinePolynomial, nativeUnframe_frame hh]

end

end Submission.Obl.k4_subcritical_corrected_scalar_charts
