import Submission.Obl.k4_pair_anchor_jet_bins.Interface

namespace Submission.Obl.k4_pair_anchor_jet_bins

open MvPolynomial Submission.Lib.K4QuadraticSheets

/-- The discriminant identity controls the hidden derivative even off the root sheet. -/
theorem hidden_derivative_bound {R : MvPolynomial (Fin 4) ℂ} (hR : R.totalDegree ≤ 2)
    {δ B D : ℝ} (hδ : 0 < δ) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hc : ‖qc R‖ ≤ δ⁻¹) (z : Fin 3 → ℂ) (w : ℂ)
    (hd : ‖qdisc R z‖ ≤ D) (hv : ‖eval (Fin.snoc z w) R‖ ≤ δ * B) :
    ‖eval (Fin.snoc z w) (pderiv (Fin.last 3) R)‖ ≤ D + 2 * B + 1 := by
  have hsq : ‖eval (Fin.snoc z w) (pderiv (Fin.last 3) R)‖ ^ 2 ≤ D + 2 * B := by
    calc
      _ = ‖eval (Fin.snoc z w) (pderiv (Fin.last 3) R) ^ 2‖ := (norm_pow _ _).symm
      _ = ‖qdisc R z + 2 * qc R * eval (Fin.snoc z w) R‖ := by
        rw [pderiv_sq_eq_qdisc_add R hR]
      _ ≤ ‖qdisc R z‖ + ‖2 * qc R * eval (Fin.snoc z w) R‖ := norm_add_le _ _
      _ ≤ D + 2 * δ⁻¹ * (δ * B) := by
        rw [norm_mul, norm_mul, Complex.norm_ofNat]
        gcongr
      _ = D + 2 * B := by field_simp
  have hn := norm_nonneg (eval (Fin.snoc z w) (pderiv (Fin.last 3) R))
  nlinarith [sq_nonneg (‖eval (Fin.snoc z w) (pderiv (Fin.last 3) R)‖ - 1)]

/-- Move a value estimate from a sheet to a nearby hidden trajectory value. -/
theorem transfer_hidden_value {R : MvPolynomial (Fin 4) ℂ} (hR : R.totalDegree ≤ 2)
    {δ A B D : ℝ} (hδ : 0 < δ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hc : ‖qc R‖ ≤ δ⁻¹) (z : Fin 3 → ℂ) (w f : ℂ)
    (hd : ‖qdisc R z‖ ≤ D) (hv : ‖eval (Fin.snoc z f) R‖ ≤ δ * B)
    (hw : ‖w - f‖ ≤ δ * A) :
    ‖eval (Fin.snoc z w) R‖ ≤ δ * (B + A * (D + 2 * B + 1 + A)) ∧
    ‖eval (Fin.snoc z w) (pderiv (Fin.last 3) R)‖ ≤ D + 2 * B + 1 + A := by
  have hdf := hidden_derivative_bound hR hδ hB hD hc z f hd hv
  have hprod : ‖qc R‖ * ‖w - f‖ ≤ A := by
    calc
      _ ≤ δ⁻¹ * (δ * A) := mul_le_mul hc hw (norm_nonneg _) (by positivity)
      _ = A := by field_simp
  have hprod2 : ‖qc R / 2 * (w - f)‖ ≤ A := by
    rw [norm_mul, norm_div, Complex.norm_ofNat]
    nlinarith [mul_nonneg (norm_nonneg (qc R)) (norm_nonneg (w - f))]
  have heq : eval (Fin.snoc z w) R = eval (Fin.snoc z f) R +
      (w - f) * (eval (Fin.snoc z f) (pderiv (Fin.last 3) R) + qc R / 2 * (w - f)) := by
    have := eval_snoc_sub_eval_snoc hR z w f
    linear_combination this
  have hdeq : eval (Fin.snoc z w) (pderiv (Fin.last 3) R) =
      eval (Fin.snoc z f) (pderiv (Fin.last 3) R) + qc R * (w - f) := by
    rw [eval_snoc_pderiv R hR, eval_snoc_pderiv R hR]
    ring
  constructor
  · rw [heq]
    calc
      _ ≤ ‖eval (Fin.snoc z f) R‖ + ‖(w - f) *
          (eval (Fin.snoc z f) (pderiv (Fin.last 3) R) + qc R / 2 * (w - f))‖ :=
        norm_add_le _ _
      _ ≤ δ * B + (δ * A) * (D + 2 * B + 1 + A) := by
        rw [norm_mul]
        apply add_le_add hv
        exact mul_le_mul hw ((norm_add_le _ _).trans (add_le_add hdf hprod2))
          (norm_nonneg _) (mul_nonneg hδ.le hA)
      _ = δ * (B + A * (D + 2 * B + 1 + A)) := by ring
  · rw [hdeq]
    exact (norm_add_le _ _).trans (by rw [norm_mul]; exact add_le_add hdf hprod)

end Submission.Obl.k4_pair_anchor_jet_bins
