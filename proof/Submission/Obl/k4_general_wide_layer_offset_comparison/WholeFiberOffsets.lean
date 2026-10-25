import Submission.Obl.k4_general_wide_layer_offset_comparison.TrueFiberChart

-- Adapted from the parent obligation o254 (k4_general_parent_wide_layer_candidates), branch x0898 of this LOT tree, file k4_general_parent_wide_layer_candidates/WholeFiberOffsets.lean; namespace renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open Set MvPolynomial

noncomputable section

/-- The absolute degree-two Lipschitz constant supplied by accepted o176. -/
def offsetLipschitz : ℝ :=
  (Submission.Obl.k4_stable_native_signal_oscillation.exists_polynomial_lipschitz_of_ball_bound 2).choose

theorem offsetLipschitz_pos : 0 < offsetLipschitz :=
  (Submission.Obl.k4_stable_native_signal_oscillation.exists_polynomial_lipschitz_of_ball_bound 2).choose_spec.1

/-- Return the matching-ball Lipschitz estimate to the two original
projected polynomials at arbitrary physical points. -/
theorem native_offset_lipschitz (G₀ G₁ : MvPolynomial (Fin 2) ℝ)
    (hG₀ : G₀.totalDegree ≤ 2) (hG₁ : G₁.totalDegree ≤ 2)
    {h g b M : ℝ} (hh : 0 < h) (hb : 0 < b) (hM : 0 ≤ M) (D : ℤ × ℤ × ℤ)
    (hbound : ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 →
      |eval (fun i => y i)
        (projectedChartPolynomial G₁ (domainTime h D) (32 * h)
          (domainIntercept h g b D) (domainVelocity g D) (32 * b) -
        projectedChartPolynomial G₀ (domainTime h D) (32 * h)
          (domainIntercept h g b D) (domainVelocity g D) (32 * b))| ≤ M)
    (z z₀ : Fin 3 → ℝ)
    (hz : ‖domainMatchingPoint h g b D z‖ ≤ 1)
    (hz₀ : ‖domainMatchingPoint h g b D z₀‖ ≤ 1) :
    |(eval ![z 0, z 2] G₁ - eval ![z 0, z 2] G₀) -
      (eval ![z₀ 0, z₀ 2] G₁ - eval ![z₀ 0, z₀ 2] G₀)| ≤
      offsetLipschitz * M * ‖domainMatchingPoint h g b D z - domainMatchingPoint h g b D z₀‖ := by
  let P := projectedChartPolynomial G₁ (domainTime h D) (32 * h)
      (domainIntercept h g b D) (domainVelocity g D) (32 * b) -
    projectedChartPolynomial G₀ (domainTime h D) (32 * h)
      (domainIntercept h g b D) (domainVelocity g D) (32 * b)
  have hP : P.totalDegree ≤ 2 := (totalDegree_sub _ _).trans
    (max_le (projectedChartPolynomial_degree _ hG₁ _ _ _ _ _)
      (projectedChartPolynomial_degree _ hG₀ _ _ _ _ _))
  have hsmall (y : EuclideanSpace ℝ (Fin 3)) (hy : ‖y‖ ≤ 1 / 8) :
      |eval (fun i => y i) P| ≤ M := hbound y (by linarith)
  have hlip :=
    (Submission.Obl.k4_stable_native_signal_oscillation.exists_polynomial_lipschitz_of_ball_bound 2).choose_spec.2
      P hP M hM hsmall (domainMatchingPoint h g b D z) (domainMatchingPoint h g b D z₀) hz hz₀
  simpa only [P, offsetLipschitz, eval_sub,
    projectedChartPolynomial_domainMatchingPoint _ hh hb] using hlip

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- An actual long-domain comparison freezes to one constant depending
only on the original Q, tag, two polynomials and the chosen true-block time.
The estimate holds on the ENTIRE physical H-sized fiber. -/
theorem AtDepth.trueFiber_offset_bound {k : ℕ} {r m R H h g b M : ℝ}
    (hat : p.AtDepth k r R) (hN : 0 < p.N k) (hH : 2 ≤ H)
    (hK : 0 ≤ p.K k) (hKH : p.K k ≤ H)
    (hh : 0 < h) (hg : 0 < g) (hb : 0 < b) (hmove : h * g = b)
    (hχwidth : p.N k ^ (-m) ≤
      (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
    (hχg : p.N k ^ (-m) ≤ p.N k ^ (-p.ℓ * r))
    (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ) {ω : α × ℝ}
    (hl : ω.1 ∈ p.B k r Q) (ht : ω.2 ∈ block (p.T k r) (p.j k r Q))
    (hz : ⌊p.b k ω.1 0 / p.N k ^ (-m)⌋ = tag 1)
    (hv : ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋ = tag 0)
    (hsmall : H ^ 2 * (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r) / b +
      ((2 : ℝ) ^ (-(p.T k r : ℤ))) * g / b) ≤ 1 / 4)
    (G₀ G₁ : MvPolynomial (Fin 2) ℝ) (hG₀ : G₀.totalDegree ≤ 2) (hG₁ : G₁.totalDegree ≤ 2)
    (hM : 0 ≤ M)
    (hbound : ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ ≤ 1 / 2 →
      let D := p.domainCode k h g b ω
      |eval (fun i => y i)
        (projectedChartPolynomial G₁ (domainTime h D) (32 * h)
          (domainIntercept h g b D) (domainVelocity g D) (32 * b) -
        projectedChartPolynomial G₀ (domainTime h D) (32 * h)
          (domainIntercept h g b D) (domainVelocity g D) (32 * b))| ≤ M)
    {t₀ : ℝ} (ht₀ : t₀ ∈ block (p.T k r) (p.j k r Q)) :
    let z₀ := p.trueFiberPoint k r m Q tag t₀
    let offset := eval ![z₀ 0, z₀ 2] G₁ - eval ![z₀ 0, z₀ 2] G₀
    ∀ z ∈ p.trueFiberBox k r m H Q tag,
      |eval ![z 0, z 2] G₁ - eval ![z 0, z 2] G₀ - offset| ≤
        offsetLipschitz * M *
          (H ^ 2 * (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r) / b +
            ((2 : ℝ) ^ (-(p.T k r : ℤ))) * g / b)) := by
  dsimp only
  let D := p.domainCode k h g b ω
  let z₀ := p.trueFiberPoint k r m Q tag t₀
  have hz₀ := p.trueFiberPoint_mem (m := m) hN (by linarith : 0 ≤ H) Q tag ht₀
  have hbounds := AtDepth.trueFiber_matching_bounds p hat hN hH hK hKH hh hg hb hmove
    hχwidth hχg Q tag hl ht hz hv hsmall
  intro z hz
  exact (native_offset_lipschitz G₀ G₁ hG₀ hG₁ hh hb hM D hbound z z₀
    ((hbounds.1 z hz).trans (by norm_num)) ((hbounds.1 z₀ hz₀).trans (by norm_num))).trans
    (mul_le_mul_of_nonneg_left (hbounds.2 z hz z₀ hz₀)
      (mul_nonneg offsetLipschitz_pos.le hM))

end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
