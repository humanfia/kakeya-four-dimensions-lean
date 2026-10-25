/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file NormalStrips.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.OriginalRows
import Submission.Lib.K4QuadraticSublevel

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

noncomputable section

def normalCoordinate (row : Fin 2 → ℝ) (z : Fin 3 → ℝ) : ℝ :=
  z 2 - row 0 * z 0 - row 1 * z 1

def normalPolynomial (row : Fin 2 → ℝ) (l : ScalarLine) : Polynomial ℝ :=
  Polynomial.C (l.2 2 - row 1 * l.2 0) +
    Polynomial.C (l.2 3 - row 0 - row 1 * l.2 1) * Polynomial.X +
    Polynomial.C (l.2 4) * Polynomial.X ^ 2

theorem normalPolynomial_degree (row : Fin 2 → ℝ) (l : ScalarLine) :
    (normalPolynomial row l).natDegree ≤ 2 := by
  dsimp only [normalPolynomial]
  compute_degree

theorem normalPolynomial_eval (row : Fin 2 → ℝ) (l : ScalarLine) (t : ℝ) :
    (normalPolynomial row l).eval t = normalCoordinate row (scalarPosition (l, t)) := by
  simp [normalPolynomial, normalCoordinate, scalarPosition, scalarX, scalarY]
  ring

theorem normalPolynomial_derivative_eval (row : Fin 2 → ℝ) (l : ScalarLine) (t : ℝ) :
    (normalPolynomial row l).derivative.eval t = l.2 3 + 2 * t * l.2 4 - row 0 - row 1 * l.2 1 := by
  simp [normalPolynomial, Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_pow]
  ring

/-- Endpoint bounds on the affine derivative suffice for the variation
between two labeled times; no label interval is assumed. -/
theorem quadratic_variation_of_endpoint_bounds (P : Polynomial ℝ) (hP : P.natDegree ≤ 2)
    {t u D : ℝ} (ht : |P.derivative.eval t| ≤ D) (hu : |P.derivative.eval u| ≤ D) :
    |P.eval t - P.eval u| ≤ D * |t - u| := by
  have hid := Submission.Lib.K4QuadraticSublevel.quadratic_eval_sub P hP t u
  have habs : 2 * |P.eval u - P.eval t| =
      |u - t| * |P.derivative.eval t + P.derivative.eval u| := by
    simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] using congrArg abs hid
  have hsum : |P.derivative.eval t + P.derivative.eval u| ≤ 2 * D :=
    (abs_add_le _ _).trans (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hsum (abs_nonneg (u - t))
  have hfinal : |P.eval u - P.eval t| ≤ D * |u - t| := by rw [← habs] at hmul; nlinarith
  simpa only [abs_sub_comm] using hfinal

/-- The graph error and nearby chosen row control the normal derivative
on each original active occurrence. -/
theorem normal_derivative_bound (row G : Fin 2 → ℝ) (l : ScalarLine) (t : ℝ)
    {H ε δ : ℝ} (hv : |l.2 1| ≤ H)
    (hgraph : |l.2 3 + 2 * t * l.2 4 - G 0 - G 1 * l.2 1| ≤ ε)
    (hrow : ∀ e, |G e - row e| ≤ δ) :
    |(normalPolynomial row l).derivative.eval t| ≤ ε + δ * (1 + H) := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hrow 0)
  have hid : (normalPolynomial row l).derivative.eval t =
      (l.2 3 + 2 * t * l.2 4 - G 0 - G 1 * l.2 1) +
        (G 0 - row 0) + (G 1 - row 1) * l.2 1 := by
    rw [normalPolynomial_derivative_eval]
    ring
  rw [hid]
  calc
    _ ≤ |l.2 3 + 2 * t * l.2 4 - G 0 - G 1 * l.2 1| +
        |G 0 - row 0| + |(G 1 - row 1) * l.2 1| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ε + δ + δ * H := by
      rw [abs_mul]
      exact add_le_add (add_le_add hgraph (hrow 0))
        (mul_le_mul (hrow 1) hv (abs_nonneg _) hδ)
    _ = _ := by ring

theorem normalCoordinate_sub_le (row : Fin 2 → ℝ) (z z' : Fin 3 → ℝ) :
    |normalCoordinate row z - normalCoordinate row z'| ≤
      (1 + |row 0| + |row 1|) * ‖z - z'‖ := by
  have hid : normalCoordinate row z - normalCoordinate row z' =
      (z 2 - z' 2) + (-(row 0 * (z 0 - z' 0))) + (-(row 1 * (z 1 - z' 1))) := by
    dsimp only [normalCoordinate]
    ring
  rw [hid]
  calc
    _ ≤ |z 2 - z' 2| + |-(row 0 * (z 0 - z' 0))| + |-(row 1 * (z 1 - z' 1))| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ ‖z - z'‖ + |row 0| * ‖z - z'‖ + |row 1| * ‖z - z'‖ := by
      simp only [abs_neg, abs_mul]
      gcongr
      · exact norm_le_pi_norm (z - z') 2
      · exact norm_le_pi_norm (z - z') 0
      · exact norm_le_pi_norm (z - z') 1
    _ = _ := by ring

/-- The fine-state center approximates the normal coordinate uniformly. -/
theorem normalCoordinate_center_error {b : ℝ} (hb : 0 < b)
    (row : Fin 2 → ℝ) (z : Fin 3 → ℝ) :
    |normalCoordinate row z - normalCoordinate row (leftCorner b (cell b z))| ≤
      (1 + |row 0| + |row 1|) * b :=
  (normalCoordinate_sub_le row z _).trans
    (mul_le_mul_of_nonneg_left (norm_sub_leftCorner_le hb z) (by positivity))

/-- Points assigned by fine-state centers to one coarse physical cell stay
within its width plus the two fine discretization errors. -/
theorem same_assigned_cell_distance {b ρ : ℝ} (hb : 0 < b) (hρ : 0 < ρ)
    (z z' : Fin 3 → ℝ)
    (hcell : cell ρ (leftCorner b (cell b z)) = cell ρ (leftCorner b (cell b z'))) :
    ‖z - z'‖ ≤ ρ + 2 * b := by
  have hc := (norm_sub_lt_of_cell_eq hρ hcell).le
  calc
    _ ≤ ‖z - leftCorner b (cell b z)‖ + ‖leftCorner b (cell b z) - z'‖ := by
      simpa only [dist_eq_norm] using dist_triangle z (leftCorner b (cell b z)) z'
    _ ≤ ‖z - leftCorner b (cell b z)‖ +
        (‖leftCorner b (cell b z) - leftCorner b (cell b z')‖ + ‖leftCorner b (cell b z') - z'‖) := by
      gcongr
      simpa only [dist_eq_norm] using dist_triangle (leftCorner b (cell b z))
        (leftCorner b (cell b z')) z'
    _ ≤ b + (ρ + b) := by
      gcongr
      · exact norm_sub_leftCorner_le hb z
      · simpa only [norm_sub_rev] using norm_sub_leftCorner_le hb z'
    _ = _ := by ring

end

end Submission.Obl.k4_scalar_graph_residual_discovery
