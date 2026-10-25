-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/QuadraticVariation.lean
import Submission.Obl.k4_stable_quadratic_hidden_sheets.Variation
import Submission.Obl.k4_stable_native_signal_oscillation.BasePolynomials

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization

/-- Real-valued form of the accepted explicit quadratic variation estimate. -/
theorem quadratic_base_variation (P : MvPolynomial (Fin 3) ℝ)
    (hP : P.totalDegree ≤ 2) (A : ℝ) (hA : ∀ e, |P.coeff e| ≤ A)
    {R δ : ℝ} (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (x y : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ R) (hxy : ∀ i, |y i - x i| ≤ δ) :
    |eval y P - eval x P| ≤ 216 * A * R ^ 2 * δ := by
  have heval (z : Fin 3 → ℝ) :
      eval₂ (algebraMap ℝ ℂ) (fun i => (z i : ℂ)) P = (eval z P : ℂ) := by
    change eval₂ (algebraMap ℝ ℂ) ((algebraMap ℝ ℂ) ∘ z) P =
      (algebraMap ℝ ℂ) (eval₂ (RingHom.id ℝ) z P)
    exact (eval₂_comp_left (algebraMap ℝ ℂ) (RingHom.id ℝ) z P).symm
  have h := Submission.Obl.k4_stable_quadratic_hidden_sheets.eval₂_sub_le P hP A hA R δ
    hR hδ hδ1 (fun i => (x i : ℂ)) (fun i => (y i : ℂ))
    (fun i => by simpa using hx i)
    (fun i => by
      simpa only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] using hxy i)
  rw [heval, heval, ← Complex.ofReal_sub] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

theorem eval_hidden_derivative (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (z : Fin 3 → ℝ) (w : ℝ) :
    eval (Fin.snoc z w) (pderiv (3 : Fin 4) P) =
      eval z (restrictBase (pderiv (3 : Fin 4) P)) + curvature P 3 * w := by
  have h := quadratic_coordinate_derivative P hP (Fin.snoc z 0) (Fin.last 3) w
  rw [Fin.snoc_last, zero_add, update_snoc_hidden, ← eval_restrictBase] at h
  simpa only [show (Fin.last 3 : Fin 4) = 3 by decide] using h

/-- Base freezing is controlled only by the two calibrated base polynomials;
the hidden quadratic coefficient cancels from their difference. -/
theorem quadratic_freezing_variation (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) {A R δ H : ℝ}
    (hA : 0 ≤ A) (hR : 1 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (_hH : 0 ≤ H)
    (hγ : ∀ e, |(restrictBase P).coeff e| ≤ A)
    (hβ : ∀ e, |(restrictBase (pderiv (3 : Fin 4) P)).coeff e| ≤ A)
    (x y : Fin 3 → ℝ) (hx : ∀ i, |x i| ≤ R) (hxy : ∀ i, |y i - x i| ≤ δ)
    (w : ℝ) (hw : |w| ≤ H) :
    |eval (Fin.snoc y w) P - eval (Fin.snoc x w) P| ≤
        216 * A * R ^ 2 * (1 + H) * δ ∧
      |eval (Fin.snoc y w) (pderiv (3 : Fin 4) P) -
        eval (Fin.snoc x w) (pderiv (3 : Fin 4) P)| ≤ 216 * A * R ^ 2 * δ := by
  have hγdeg : (restrictBase P).totalDegree ≤ 2 := (totalDegree_restrictBase _).trans hP
  have hβdeg : (restrictBase (pderiv (3 : Fin 4) P)).totalDegree ≤ 2 :=
    (totalDegree_restrictBase _).trans
      ((Submission.Obl.k4_quadratic_slope_volume.totalDegree_pderiv_le P 3).trans (by omega))
  have hγ' := quadratic_base_variation _ hγdeg A hγ hR hδ hδ1 x y hx hxy
  have hβ' := quadratic_base_variation _ hβdeg A hβ hR hδ hδ1 x y hx hxy
  constructor
  · have heq : eval (Fin.snoc y w) P - eval (Fin.snoc x w) P =
        (eval y (restrictBase P) - eval x (restrictBase P)) +
          (eval y (restrictBase (pderiv 3 P)) - eval x (restrictBase (pderiv 3 P))) * w := by
      rw [eval_snoc_quadratic P hP, eval_snoc_quadratic P hP]
      rw [show (Fin.last 3 : Fin 4) = 3 by decide]
      ring
    rw [heq]
    calc
      _ ≤ |eval y (restrictBase P) - eval x (restrictBase P)| +
          |eval y (restrictBase (pderiv 3 P)) - eval x (restrictBase (pderiv 3 P))| * |w| := by
        simpa only [abs_mul] using abs_add_le
          (eval y (restrictBase P) - eval x (restrictBase P))
          ((eval y (restrictBase (pderiv 3 P)) - eval x (restrictBase (pderiv 3 P))) * w)
      _ ≤ 216 * A * R ^ 2 * δ + (216 * A * R ^ 2 * δ) * H :=
        add_le_add hγ' (mul_le_mul hβ' hw (abs_nonneg _) (by positivity))
      _ = _ := by ring
  · rw [eval_hidden_derivative P hP, eval_hidden_derivative P hP]
    simpa only [add_sub_add_right_eq_sub] using hβ'

/-- Within one residual hidden bin, native variation uses the ACTUAL native
derivative at the observed point. Large calibrated coefficients only govern
the fine base mesh, and do not enter the scalar-bin multiplicity. -/
theorem native_oscillation_of_base_control (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (x y : Fin 3 → ℝ) (w w' : ℝ) {K a : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hfirst : |eval (Fin.snoc x w) (pderiv (3 : Fin 4) P)| ≤ K)
    (hsecond : |curvature P 3| ≤ K) (hhidden : |w' - w| ≤ a)
    (hbase : |eval (Fin.snoc y w') P - eval (Fin.snoc x w') P| ≤ a) :
    dist (eval (Fin.snoc y w') P) (eval (Fin.snoc x w) P) ≤ (1 + 2 * K) * a := by
  have h := signal_error_scale P hP (Fin.snoc x w) (Fin.last 3)
    hK (show (0 : ℝ) ≤ 1 by norm_num) ha ha1 hfirst hsecond
    (show |w' - w| ≤ 1 * a by simpa only [one_mul] using hhidden)
  simp only [Fin.snoc_last, update_snoc_hidden, one_pow, one_add_one_eq_two] at h
  rw [show w + (w' - w) = w' by ring] at h
  rw [Real.dist_eq]
  exact (abs_sub_le _ (eval (Fin.snoc x w') P) _).trans
    ((add_le_add hbase h).trans_eq (by ring))

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
