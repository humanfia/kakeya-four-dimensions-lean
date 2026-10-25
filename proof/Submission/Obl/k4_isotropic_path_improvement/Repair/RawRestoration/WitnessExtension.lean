-- Part of an offer for o106 assembled by x0678 (o064). Adapted from this LOT tree, o064's
-- repository, origin/x0447 at f61522e4 (x0447's file Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/RawRestoration/WitnessExtension.lean);
-- only the namespace changed. See that file for the sources it in turn adapts.
-- Adapted from this LOT tree o143/x0542, commit f027eb90,
-- Submission/Obl/k4_isotropic_discovery_of_local_restoration/WitnessExtension.lean.
import Mathlib
import Submission.Lib.K4PolynomialRemez
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices
import Submission.Obl.k4_polynomial_variation_tube.LineVariation

/-! Extend restored tests from long witness sets to their original time block. -/

namespace Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration

noncomputable section

open MvPolynomial MeasureTheory

/-- Restrict a polynomial to an affine trajectory in normalized block time. -/
def affineTimePolynomial {n : ℕ} (a v : Fin n → ℝ) (P : MvPolynomial (Fin n) ℝ) :
    Polynomial ℝ :=
  k4_polynomial_variation_tube.lineRestrict P (WithLp.toLp 2 a) (WithLp.toLp 2 v)

lemma affineTimePolynomial_degree {n : ℕ} (a v : Fin n → ℝ)
    (P : MvPolynomial (Fin n) ℝ) :
    (affineTimePolynomial a v P).natDegree ≤ P.totalDegree := by
  exact k4_polynomial_variation_tube.natDegree_lineRestrict_le _ _ _

lemma eval_affineTimePolynomial {n : ℕ} (a v : Fin n → ℝ)
    (P : MvPolynomial (Fin n) ℝ) (t : ℝ) :
    (affineTimePolynomial a v P).eval t = eval (fun i => a i + t * v i) P := by
  simpa [affineTimePolynomial] using k4_polynomial_variation_tube.eval_lineRestrict
    P (WithLp.toLp 2 a) (WithLp.toLp 2 v) t

/-- Remez in normalized time has no inverse power of the physical block length. -/
theorem affine_trajectory_witness_extension {n d : ℕ} (a v : Fin n → ℝ)
    (P : MvPolynomial (Fin n) ℝ) (hdeg : P.totalDegree ≤ d)
    (S : Set ℝ) {η E : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Set.Icc (0 : ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ t ∈ S, |eval (fun i => a i + t * v i) P| ≤ E) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |eval (fun i => a i + t * v i) P| ≤ (8 * ((d : ℝ) + 1) / η) ^ d * E := by
  have h := Submission.Lib.K4PolynomialRemez.polynomial_remez_unit
    (affineTimePolynomial a v P) d ((affineTimePolynomial_degree a v P).trans hdeg)
    S hη hη1 hE hS hmass (by simpa only [eval_affineTimePolynomial] using hbound)
  simpa only [eval_affineTimePolynomial] using h

/-- A quadratic's hidden derivative needs only the first power of the Remez loss. -/
theorem quadratic_hidden_derivative_witness_extension (a v : Fin 4 → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (hdeg : P.totalDegree ≤ 2)
    (S : Set ℝ) {η E : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Set.Icc (0 : ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ t ∈ S, |eval (fun i => a i + t * v i) (pderiv 3 P)| ≤ E) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |eval (fun i => a i + t * v i) (pderiv 3 P)| ≤ (16 / η) * E := by
  have hderiv : (pderiv (3 : Fin 4) P).totalDegree ≤ 1 :=
    (k4_quadratic_slope_volume.totalDegree_pderiv_le P 3).trans (by omega)
  convert affine_trajectory_witness_extension a v (pderiv 3 P) hderiv S
    hη hη1 hE hS hmass hbound
    using 1 <;> norm_num

/-- A quadratic's hidden curvature is constant, so extending it costs no loss. -/
theorem quadratic_hidden_curvature_witness_extension (a v : Fin 4 → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (hdeg : P.totalDegree ≤ 2)
    (S : Set ℝ) {η E : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Set.Icc (0 : ℝ) 1) (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ t ∈ S, |eval (fun i => a i + t * v i) (pderiv 3 (pderiv 3 P))| ≤ E) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1,
      |eval (fun i => a i + t * v i) (pderiv 3 (pderiv 3 P))| ≤ E := by
  have hfirst := k4_quadratic_slope_volume.totalDegree_pderiv_le P 3
  have hsecond := k4_quadratic_slope_volume.totalDegree_pderiv_le (pderiv 3 P) 3
  have hcurv : (pderiv (3 : Fin 4) (pderiv 3 P)).totalDegree ≤ 0 := by omega
  simpa using affine_trajectory_witness_extension a v (pderiv 3 (pderiv 3 P))
    hcurv S hη hη1 hE hS hmass hbound

end

end Submission.Obl.k4_isotropic_path_improvement.Repair.RawRestoration
