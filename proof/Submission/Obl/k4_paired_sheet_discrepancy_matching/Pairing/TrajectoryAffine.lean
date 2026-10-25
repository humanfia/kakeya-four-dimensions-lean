/- Adapted from this LOT tree, o114/x0680 commit133cc8c, Submission/Obl/k4_terminal_representative_atlas/Pairing/TrajectoryAffine.lean.
Existing attribution to o156/x0531,x0524,x0575 and accepted imports is retained below. -/

/- Adapted from this LOT tree, o156/x0524, c7cfd90, Submission/Obl/k4_terminal_local_sheet_pairing/TrajectoryAffine.lean; namespace and imports adjusted for o114. -/
import Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing.Interface
import Submission.Obl.k4_quadratic_selector_sweep.Quadratic

namespace Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing

open MvPolynomial

/-- The frozen normalized base is affine in the original trajectory time. -/
theorem exists_base_affine (T : ℕ) (j κ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (l : ℕ × (Fin 6 → ℝ)) :
    ∃ z₀ v₀ : EuclideanSpace ℝ (Fin 3), ∀ t : ℝ,
      base T j κ c u Q l t = z₀ + t • v₀ := by
  let A := Matrix.toEuclideanLin Q⁻¹ (y l 0 - c)
  let V := Matrix.toEuclideanLin Q⁻¹ (v l - u)
  have hy (t : ℝ) : y l t - c - t • u = y l 0 - c + t • (v l - u) := by
    ext i
    fin_cases i <;> simp [y, x, v, smul_eq_mul] <;> ring
  have hlin (t : ℝ) : Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u) = A + t • V := by
    dsimp [A, V]
    rw [hy, map_add, map_smul]
  let z₀ : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2
    ![(-j - 1 / 2) / (100 * κ), A 0 / (100 * κ), A 1 / (100 * κ)]
  let v₀ : EuclideanSpace ℝ (Fin 3) := WithLp.toLp 2
    ![(2 : ℝ) ^ T / (100 * κ), V 0 / (100 * κ), V 1 / (100 * κ)]
  refine ⟨z₀, v₀, ?_⟩
  intro t
  ext i
  fin_cases i <;> simp [base, hlin, z₀, v₀, smul_eq_mul] <;> ring

/-- A quadratic's hidden derivative is affine along the actual normalized
base/hidden trajectory, exactly as required by the short source-sheet fit. -/
theorem source_derivative_affine (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (T : ℕ) (j κ B : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (l : ℕ × (Fin 6 → ℝ)) :
    ∃ m d : ℝ, ∀ t : ℝ,
      eval (Fin.snoc (fun i => base T j κ c u Q l t i) (B * (x l t) 3))
        (pderiv (3 : Fin 4) P) = m * t + d := by
  obtain ⟨z₀, v₀, hz⟩ := exists_base_affine T j κ c u Q l
  let a : Fin 4 → ℝ := Fin.snoc (fun i => z₀ i) (B * l.2 2)
  let b : Fin 4 → ℝ := Fin.snoc (fun i => v₀ i) (B * l.2 5)
  have hdegree : (pderiv (3 : Fin 4) P).totalDegree ≤ 1 :=
    Submission.Obl.k4_quadratic_selector_sweep.totalDegree_pderiv_le P (3 : Fin 4) hP
  obtain ⟨m, d, hd⟩ :=
    Submission.Obl.k4_quadratic_selector_sweep.eval_affine_of_totalDegree_le_one
      (pderiv (3 : Fin 4) P) hdegree a b
  refine ⟨m, d, ?_⟩
  intro t
  have hvars : Fin.snoc (fun i => base T j κ c u Q l t i) (B * (x l t) 3) =
      (fun i : Fin 4 => a i + t * b i) := by
    rw [hz]
    ext i
    fin_cases i
    · change (z₀ + t • v₀) 0 = z₀ 0 + t * v₀ 0
      rfl
    · change (z₀ + t • v₀) 1 = z₀ 1 + t * v₀ 1
      rfl
    · change (z₀ + t • v₀) 2 = z₀ 2 + t * v₀ 2
      rfl
    · change B * (l.2 2 + t * l.2 5) = B * l.2 2 + t * (B * l.2 5)
      ring
  rw [hvars]
  exact hd t

end Submission.Obl.k4_paired_sheet_discrepancy_matching.Pairing
