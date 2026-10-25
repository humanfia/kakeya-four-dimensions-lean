-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/RawRestoration/RestoredBounds.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
-- Adapted from this LOT tree o143/x0542, commit f027eb90,
-- Submission/Obl/k4_isotropic_discovery_of_local_restoration/RestoredBounds.lean.
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.TransportBounds
import Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration.LocalRestoration

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration

noncomputable section

open MvPolynomial

/-- Split the three base coordinates from the hidden coordinate. -/
def pointOfCoordinates (x : Fin 4 → ℝ) : Base × ℝ :=
  (WithLp.toLp 2 (fun i : Fin 3 => x i.castSucc), x 3)

lemma coordinates_pointOfCoordinates (x : Fin 4 → ℝ) :
    ![(pointOfCoordinates x).1 0, (pointOfCoordinates x).1 1,
      (pointOfCoordinates x).1 2, (pointOfCoordinates x).2] = x := by
  funext i
  fin_cases i <;> rfl

/-- Restored value, derivative, and curvature bounds in the original units. -/
theorem restored_bounds_in_original_coordinates {C : ℕ} (D : LocalBranchData C)
    (Q : Poly) (hQ : D.restored Q) (c : Fin 3 → ℝ)
    (M : Matrix (Fin 3) (Fin 3) ℝ) {B K : ℝ} (hB : 0 < B)
    (hbudget : D.A ^ C ≤ K) (x : Fin 4 → ℝ)
    (hx : pointOfCoordinates (coordinateMap c M B x) ∈ D.region) :
    |eval x (transportPolynomial c M B Q)| ≤ K * D.b ∧
      B / K ≤ |eval x (pderiv 3 (transportPolynomial c M B Q))| ∧
      |eval x (pderiv 3 (transportPolynomial c M B Q))| ≤ K * B ∧
      |eval x (pderiv 3 (pderiv 3 (transportPolynomial c M B Q)))| ≤
        K * B ^ 2 / D.b := by
  have hA : 0 < D.A := lt_of_lt_of_le (by norm_num) D.two_le_A
  have hAC : 0 < D.A ^ C := pow_pos hA C
  have h := hQ.2.2 _ hx
  rw [coordinates_pointOfCoordinates] at h
  obtain ⟨hval, hlo, hhi, hcurv⟩ := h
  obtain ⟨hd, hdd⟩ := eval_transport_hidden_derivatives c M B Q x
  have hdinv : K⁻¹ ≤ D.A ^ (-(C : ℤ)) := by
    rw [zpow_neg, zpow_natCast]
    exact inv_anti₀ hAC hbudget
  rw [eval_transportPolynomial, hd, hdd, abs_mul, abs_mul,
    abs_of_pos hB, abs_of_nonneg (sq_nonneg B)]
  refine ⟨hval.trans (mul_le_mul_of_nonneg_right hbudget D.b_pos.le), ?_, ?_, ?_⟩
  · calc
      B / K = B * K⁻¹ := div_eq_mul_inv _ _
      _ ≤ B * D.A ^ (-(C : ℤ)) := mul_le_mul_of_nonneg_left hdinv hB.le
      _ ≤ B * |eval (coordinateMap c M B x) (pderiv 3 Q)| :=
        mul_le_mul_of_nonneg_left hlo hB.le
  · exact (mul_le_mul_of_nonneg_left hhi hB.le).trans_eq (mul_comm _ _)
      |>.trans (mul_le_mul_of_nonneg_right hbudget hB.le)
  · calc
      B ^ 2 * |eval (coordinateMap c M B x) (pderiv 3 (pderiv 3 Q))|
          ≤ B ^ 2 * (D.A ^ C / D.b) :=
        mul_le_mul_of_nonneg_left hcurv (sq_nonneg _)
      _ ≤ B ^ 2 * (K / D.b) := by
        gcongr
        exact D.b_pos.le
      _ = K * B ^ 2 / D.b := by ring

end

end Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration
