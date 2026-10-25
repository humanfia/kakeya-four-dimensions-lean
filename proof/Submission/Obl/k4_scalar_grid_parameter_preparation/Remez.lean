/- Adapted from this LOT tree, o092, session x0317, commit 9697971769c3.
   Original file: Submission/Obl/k4_scalar_tangent_isotropic_improvement/Remez.lean -/
import Submission.Lib.K4PolynomialRemez
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices

/-! Polynomial wrappers for the accepted general Remez comparison library. -/

namespace Submission.Obl.k4_scalar_grid_parameter_preparation

open Set MeasureTheory

export Submission.Lib.K4PolynomialRemez
  (exists_away_from_finset norm_eval_le_of_root_comparison polynomial_remez_unit probability_large_fibers)

private theorem update_binary_zero (x y t : ℝ) :
    Function.update (![x, y] : Fin 2 → ℝ) 0 t = ![t, y] := by
  ext i
  fin_cases i <;> simp

private theorem update_binary_one (x y t : ℝ) :
    Function.update (![x, y] : Fin 2 → ℝ) 1 t = ![x, t] := by
  ext i
  fin_cases i <;> simp

private theorem coordinate_polynomial_data (p : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hp : p.totalDegree ≤ D) (v : Fin 2 → ℝ) (i : Fin 2) :
    ∃ q : Polynomial ℝ, q.natDegree ≤ D ∧
      ∀ t, q.eval t = MvPolynomial.eval (Function.update v i t) p := by
  refine ⟨Submission.Obl.k4_quadratic_slope_volume.coordinatePolynomialHom v i p, ?_, ?_⟩
  · apply (Submission.Obl.k4_quadratic_slope_volume.natDegree_eval₂_affine_le p _ ?_).trans hp
    intro j
    split_ifs <;> simp
  · exact Submission.Obl.k4_quadratic_slope_volume.eval_coordinatePolynomialHom p v i

private theorem binary_separate_polynomial (p : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hp : p.totalDegree ≤ D) :
    (∀ x : ℝ, ∃ q : Polynomial ℝ, q.natDegree ≤ D ∧ ∀ y, q.eval y = MvPolynomial.eval ![x, y] p) ∧
    (∀ y : ℝ, ∃ q : Polynomial ℝ, q.natDegree ≤ D ∧ ∀ x, q.eval x = MvPolynomial.eval ![x, y] p) := by
  constructor
  · intro x
    obtain ⟨q, hq, heval⟩ := coordinate_polynomial_data p D hp ![x, 0] 1
    exact ⟨q, hq, fun y => by simpa only [update_binary_one] using heval y⟩
  · intro y
    obtain ⟨q, hq, heval⟩ := coordinate_polynomial_data p D hp ![0, y] 0
    exact ⟨q, hq, fun x => by simpa only [update_binary_zero] using heval x⟩

/-- Remez on an arbitrary coordinate slice. -/
theorem polynomial_remez_coordinate (p : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hp : p.totalDegree ≤ D) (v : Fin 2 → ℝ) (i : Fin 2) (S : Set ℝ) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E) (hS : S ⊆ Set.Icc (0 : ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ t ∈ S, |MvPolynomial.eval (Function.update v i t) p| ≤ E) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      |MvPolynomial.eval (Function.update v i x) p| ≤ (8 * ((D : ℝ) + 1) / η) ^ D * E := by
  obtain ⟨q, hq, heval⟩ := coordinate_polynomial_data p D hp v i
  simpa only [heval] using polynomial_remez_unit q D hq S hη hη1 hE hS hmass
    (by simpa only [heval] using hbound)

/-- Bivariate Remez on a measurable subset of the unit square. -/
theorem polynomial_remez_square (p : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hp : p.totalDegree ≤ D) (S : Set (ℝ × ℝ)) (hSmeas : MeasurableSet S) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ z ∈ S, |MvPolynomial.eval ![z.1, z.2] p| ≤ E) :
    ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      |MvPolynomial.eval ![z.1, z.2] p| ≤ (16 * ((D : ℝ) + 1) / η) ^ (2 * D) * E := by
  obtain ⟨hrow, hcol⟩ := binary_separate_polynomial p D hp
  exact Submission.Lib.K4PolynomialRemez.separately_polynomial_remez_square _ D
    hrow hcol S hSmeas hη hη1 hE hS hmass hbound

/-- The square comparison requires only outer mass for a polynomial witness set. -/
theorem polynomial_remez_square_of_outer_measure (p : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hp : p.totalDegree ≤ D) (S : Set (ℝ × ℝ)) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S)
    (hbound : ∀ z ∈ S, |MvPolynomial.eval ![z.1, z.2] p| ≤ E) :
    ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1,
      |MvPolynomial.eval ![z.1, z.2] p| ≤ (16 * ((D : ℝ) + 1) / η) ^ (2 * D) * E := by
  obtain ⟨hrow, hcol⟩ := binary_separate_polynomial p D hp
  have hcont : Continuous (fun z : ℝ × ℝ => MvPolynomial.eval ![z.1, z.2] p) :=
    (MvPolynomial.continuous_eval p).comp (by apply continuous_pi; intro i; fin_cases i <;> fun_prop)
  exact Submission.Lib.K4PolynomialRemez.separately_polynomial_remez_square_of_outer_measure _
    hcont D hrow hcol S hη hη1 hE hS hmass hbound

/-- Outer-measure Remez in the coordinates of scalar packet fields and potentials. -/
theorem polynomial_remez_box (p : MvPolynomial (Fin 2) ℝ) (D : ℕ)
    (hp : p.totalDegree ≤ D) (S : Set (Fin 2 → ℝ)) {η E : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hE : 0 ≤ E)
    (hS : S ⊆ Set.Icc (0 : Fin 2 → ℝ) 1)
    (hmass : ENNReal.ofReal η ≤ volume S) (hbound : ∀ z ∈ S, |MvPolynomial.eval z p| ≤ E) :
    ∀ z ∈ Set.Icc (0 : Fin 2 → ℝ) 1,
      |MvPolynomial.eval z p| ≤ (16 * ((D : ℝ) + 1) / η) ^ (2 * D) * E := by
  obtain ⟨hrow, hcol⟩ := binary_separate_polynomial p D hp
  exact Submission.Lib.K4PolynomialRemez.separately_polynomial_remez_box _
    (MvPolynomial.continuous_eval p) D hrow hcol S hη hη1 hE hS hmass hbound

end Submission.Obl.k4_scalar_grid_parameter_preparation
