import Submission.Obl.k4_scalar_tangent_isotropic_improvement.PolynomialLipschitz
import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GridCells

/-! Transfer actual trajectory tests to the thickened finite base cells. -/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

noncomputable section

theorem cubicTest_le_on_gridCell (D : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (p : MvPolynomial (Fin 2) ℝ) (o z u : Fin 2 → ℝ) (ξ H r τ E v w : ℝ),
      p.totalDegree ≤ D → 0 < ξ → 1 ≤ H → (∀ b, |p.coeff b| ≤ H) →
      (baseGridCell o ξ (baseGridTag o ξ z) ⊆ Set.Icc (0 : Fin 2 → ℝ) 1) →
      (∀ i, |u i| ≤ H) → |v| ≤ H → |w| ≤ H → dist z u ≤ r → |v - w| ≤ τ →
      |cubicTest p u w| ≤ E →
      ∀ x ∈ baseGridCell o ξ (baseGridTag o ξ z),
        |cubicTest p x v| ≤ E + C * H ^ (2 * D + 4) * (ξ + r + τ) := by
  obtain ⟨C, hC, hLip⟩ := exists_cubicTest_lipschitz D
  refine ⟨C, hC, ?_⟩
  intro p o z u ξ H r τ E v w hp hξ hH hc hbox hu hv hw hz hvw htest x hx
  have hxH : ∀ i, |x i| ≤ H := by
    intro i
    have h := hbox hx
    rw [abs_of_nonneg (h.1 i)]
    exact (h.2 i).trans hH
  have hxz : dist x z ≤ ξ :=
    dist_le_of_same_baseGridCell o hξ hx ((mem_baseGridCell_iff o hξ _ _).mpr rfl)
  have hxu : dist x u ≤ ξ + r :=
    (dist_triangle x z u).trans (add_le_add hxz hz)
  calc
    |cubicTest p x v| ≤ |cubicTest p u w| + |cubicTest p x v - cubicTest p u w| := by
      have h := abs_add_le (cubicTest p u w) (cubicTest p x v - cubicTest p u w)
      rwa [show cubicTest p u w + (cubicTest p x v - cubicTest p u w) = cubicTest p x v by ring] at h
    _ ≤ E + C * H ^ (2 * D + 4) * (dist x u + |v - w|) :=
      add_le_add htest (hLip p H v w x u hp hH hc hxH hu hv hw)
    _ ≤ E + C * H ^ (2 * D + 4) * (ξ + r + τ) := by
      gcongr

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
