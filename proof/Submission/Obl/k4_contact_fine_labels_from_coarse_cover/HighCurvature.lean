-- Adapted from this LOT tree, o241, session x0834, branch x0834 at 511ef044.
-- Original file: Submission/Obl/k4_contact_equal_rate_affine_palettes/HighCurvature.lean
import Submission.Obl.k4_stable_native_signal_oscillation.BasePolynomials

namespace Submission.Obl.k4_contact_fine_labels_from_coarse_cover

open MvPolynomial
open Submission.Obl.k4_stable_native_signal_oscillation
open Submission.Obl.k4_quadratic_atlas_normalization

/-- Display a polynomial of degree at most one in the coefficient format
required by the frozen palette conclusion. -/
theorem exists_affine_coefficients (P : MvPolynomial (Fin 3) ℝ)
    (hP : P.totalDegree ≤ 1) :
    ∃ L : Fin 4 → ℝ, ∀ z : Fin 3 → ℝ,
      eval z P = L 0 + L 1 * z 0 + L 2 * z 1 + L 3 * z 2 := by
  classical
  let L : Fin 4 → ℝ := ![P.coeff 0, P.coeff (Finsupp.single 0 1),
    P.coeff (Finsupp.single 1 1), P.coeff (Finsupp.single 2 1)]
  have hsupport (m : Fin 3 →₀ ℕ) (hm : m ∈ P.support) :
      m = 0 ∨ ∃ i, m = Finsupp.single i 1 := by
    have hle := (le_totalDegree hm).trans hP
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle with h | h
    · exact Or.inl ((Finsupp.degree_eq_zero_iff m).mp h)
    · exact Or.inr ((Finsupp.sum_eq_one_iff m).mp h)
  have heq : P = C (L 0) + C (L 1) * X 0 + C (L 2) * X 1 + C (L 3) * X 2 := by
    ext m
    by_cases hm0 : m = 0
    · subst m
      simp [L]
    by_cases hm1 : ∃ i, m = Finsupp.single i 1
    · obtain ⟨i, rfl⟩ := hm1
      have hzero (j : Fin 3) : (0 : Fin 3 →₀ ℕ) ≠ Finsupp.single j 1 := by
        exact Ne.symm (Finsupp.single_ne_zero.mpr (by norm_num))
      fin_cases i <;>
        norm_num [L, coeff_C, C_mul_X_eq_monomial, coeff_monomial,
          Finsupp.single_eq_single_iff, Finsupp.single_eq_zero, hzero]
    · have hcoeff : P.coeff m = 0 := by
        by_contra h
        rcases hsupport m (mem_support_iff.mpr h) with h | h
        · exact hm0 h
        · exact hm1 h
      have h0 : m ≠ Finsupp.single 0 1 := fun h => hm1 ⟨0, h⟩
      have h1 : m ≠ Finsupp.single 1 1 := fun h => hm1 ⟨1, h⟩
      have h2 : m ≠ Finsupp.single 2 1 := fun h => hm1 ⟨2, h⟩
      simp [hcoeff, coeff_C, C_mul_X_eq_monomial, coeff_monomial,
        Ne.symm hm0, Ne.symm h0, Ne.symm h1, Ne.symm h2]
  refine ⟨L, fun z => ?_⟩
  rw [heq]
  simp

/-- The large-curvature alternative uses one affine entry, uniformly over
all admissible points; its coefficients can be arbitrarily large. -/
theorem high_curvature_affine_entry (F : MvPolynomial (Fin 4) ℝ)
    (hF : F.totalDegree ≤ 2) {K a : ℝ} (hK : 0 < K) (ha : 0 < a)
    (hlarge : (K ^ 5 * a)⁻¹ ≤ |curvature F 3|) :
    ∃ L : Fin 4 → ℝ, ∀ v : Fin 4 → ℝ,
      |eval v (pderiv 3 F)| ≤ K →
      |v 3 - (L 0 + L 1 * v 0 + L 2 * v 1 + L 3 * v 2)| ≤ K ^ 6 * a := by
  obtain ⟨L, hL⟩ := exists_affine_coefficients (centerPoly F) (centerPoly_degree F hF)
  refine ⟨L, fun v hv => ?_⟩
  have hcurv : curvature F 3 ≠ 0 := by
    exact abs_pos.mp ((by positivity : 0 < (K ^ 5 * a)⁻¹).trans_le hlarge)
  have hc := eval_centerPoly F hF hcurv (Fin.init v) (v (Fin.last 3))
  rw [Fin.snoc_init_self] at hc
  change eval (Fin.init v) (centerPoly F) = hiddenCenter F v 3 at hc
  have hcenter := hiddenCenter_distance F v 3 hK ha hlarge hv
  rw [← hc, hL] at hcenter
  simpa [Fin.init_def, Fin.castSucc, abs_sub_comm] using hcenter

end Submission.Obl.k4_contact_fine_labels_from_coarse_cover
