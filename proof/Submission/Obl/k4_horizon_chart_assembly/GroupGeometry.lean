import Submission.Obl.k4_horizon_chart_assembly.Groups

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory MvPolynomial
open scoped BigOperators ENNReal

noncomputable section

theorem nativeEligible_planar_norm {P : MvPolynomial (Fin 4) ℝ} {B K H : ℝ}
    {l : Trajectory} (hl : nativeEligible P B K H l) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : ‖planarPoint l t‖ ≤ K := by
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, planarPoint] using (hl.2.2 t ht).1

/-- The global base fit bounds planar speed by the endpoint difference. -/
theorem nativeEligible_velocity_norm {P : MvPolynomial (Fin 4) ℝ} {B K H : ℝ}
    {l : Trajectory} (hl : nativeEligible P B K H l) : ‖planarVelocity l‖ ≤ 2 * K := by
  have hv : planarVelocity l = planarPoint l 1 - planarPoint l 0 := by
    ext e
    fin_cases e <;> simp [planarVelocity, planarPoint]
  rw [hv]
  have h0 : ‖planarPoint l 0‖ ≤ K := nativeEligible_planar_norm hl (by norm_num)
  have h1 : ‖planarPoint l 1‖ ≤ K := nativeEligible_planar_norm hl (by norm_num)
  exact (norm_sub_le _ _).trans (by linarith)


/-- The a.e. native hypotheses imply the formatted pointwise eligibility wherever
the original event provides its tempered coefficient box. -/
theorem nativeEligible_of_native_bounds (P : MvPolynomial (Fin 4) ℝ) (B K H : ℝ)
    (l : Trajectory) (hi : (l.1 : ℝ) ≤ H) (hc : ∀ e, |l.2 e| ≤ H)
    (h : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖yl l t‖ + ‖vl l‖ ≤ K ∧ |eval (xl l t) P| ≤ K ∧
      |eval (xl l t) (pderiv (3 : Fin 4) P)| ≤ K * B ∧
      |eval (xl l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤ K * B ^ 2) :
    nativeEligible P B K H l := by
  refine ⟨hi, hc, fun t ht => ?_⟩
  have hh := h t ht
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hy : ‖yl l t‖ ≤ K := by linarith [norm_nonneg (vl l)]
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, yl,
      Submission.Obl.k4_quadratic_atlas_normalization.y,
      Submission.Obl.k4_quadratic_atlas_normalization.x, planarPoint] using hy
  · simpa only [graphPoint, xl, Submission.Obl.k4_quadratic_atlas_normalization.x, mul_one] using hh.2.1
  · exact hh.2.2.1
  · simpa only [graphPoint, xl, Submission.Obl.k4_quadratic_atlas_normalization.x, div_one] using hh.2.2.2

/-- An integer radius larger than twice the old base bound normalizes every
eligible midpoint group to the unit trace chart. -/
theorem nativeGroup_normalized_bounds (P : MvPolynomial (Fin 4) ℝ)
    (B H s mid : ℝ) {K q a R : ℝ} (hq : 0 < q) (hK : 0 ≤ K)
    (hR : 2 * K + 2 ≤ R) (hnear : |s - mid| ≤ q)
    (Γ : (Fin 2 → ℤ) × ℤ) {l : Trajectory}
    (hl : l ∈ nativeGroup P B K H mid q a Γ) :
    ‖groupIntercept q a s (R * q) Γ l‖ ≤ 1 ∧ ‖groupVelocity q (R * q) l‖ ≤ 1 := by
  have hK' : 0 ≤ R - 2 := by linarith
  have hv : ‖planarVelocity (0, l.2)‖ ≤ R - 2 :=
    (nativeEligible_velocity_norm hl.1).trans (by linarith)
  have h := midpoint_group_normalized_bounds P mid s a hq hK' l.2 Γ hl.2 hv hnear
  have heq : (R - 2 + 2) * q = R * q := by ring
  simpa only [heq, groupIntercept, groupVelocity, planarPoint, planarVelocity] using h

/-- Enlarging one common positive slack preserves a whole-block fit. -/
theorem wholeBlockFit_mono {P : MvPolynomial (Fin 4) ℝ}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {c u : Plane} {K K' B a s t : ℝ}
    (hKK' : K ≤ K') (hB : 0 ≤ B) (ha : 0 < a)
    {x : Fin 6 → ℝ} (h : WholeBlockFit P Q c u K B a s t x) :
    WholeBlockFit P Q c u K' B a s t x := by
  intro z hz
  have hh := h z hz
  exact ⟨hh.1.trans hKK', hh.2.1.trans (mul_le_mul_of_nonneg_right hKK' ha.le),
    hh.2.2.1.trans (mul_le_mul_of_nonneg_right hKK' hB),
    hh.2.2.2.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKK' (sq_nonneg B)) ha.le)⟩

/-- Each selected normalized matrix chart lifts to every original whole-block
fit with one slack proportional to the integer grouping radius. -/
theorem nativeGroup_wholeBlockFit (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (B H s mid : ℝ) {K q a R : ℝ} (hK : 0 ≤ K) (hq : 0 < q)
    (ha : 0 < a) (ha1 : a ≤ 1) (hqa : q ≤ a) (hB : 0 < B)
    (hR : 2 * K + 2 ≤ R) (hmid : mid ∈ Icc (0 : ℝ) 1)
    (hblock : Icc s (s + q) ⊆ Icc (0 : ℝ) 1)
    (hnear : ∀ t ∈ Icc s (s + q), |t - mid| ≤ q)
    (Γ : (Fin 2 → ℤ) × ℤ) {l : Trajectory}
    (hl : l ∈ nativeGroup P B K H mid q a Γ)
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hQ : Q.det ≠ 0) (c w : Plane)
    (hfit : ∀ τ ∈ Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin Q⁻¹
        (groupIntercept q a s (R * q) Γ l + τ • groupVelocity q (R * q) l - c - τ • w)‖ ≤ 2) :
    WholeBlockFit (shiftedTest P (a * (Γ.2 : ℝ))) ((R * q) • Q)
      (liftedBlockCenter (midpointGroupCenter q Γ) c w s q (R * q))
      (liftedBlockSpeed w q (R * q)) (64 * R) B a s (s + q) l.2 := by
  have hK' : 0 ≤ R - 2 := by linarith
  have hKR : K ≤ R - 2 := by linarith
  have hvalue : ∀ t ∈ Icc (0 : ℝ) 1, |eval (graphPoint (0, l.2) t) P| ≤ R - 2 := by
    intro t ht
    have hh : |eval (graphPoint (0, l.2) t) P| ≤ K := by
      simpa only [mul_one] using (hl.1.2.2 t ht).2.1
    exact hh.trans hKR
  have hfirst : ∀ t ∈ Icc (0 : ℝ) 1,
      |eval (graphPoint (0, l.2) t) (pderiv (3 : Fin 4) P)| ≤ (R - 2) * B := by
    intro t ht
    exact (hl.1.2.2 t ht).2.2.1 |>.trans (mul_le_mul_of_nonneg_right hKR hB.le)
  have hsecond : ∀ t ∈ Icc (0 : ℝ) 1,
      |eval (graphPoint (0, l.2) t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P))| ≤
        (R - 2) * B ^ 2 := by
    intro t ht
    have hh := (hl.1.2.2 t ht).2.2.2
    simp only [div_one] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hKR (sq_nonneg B))
  have heq : (R - 2 + 2) * q = R * q := by ring
  have hfit' : ∀ τ ∈ Icc (0 : ℝ) 1,
      ‖Matrix.toEuclideanLin Q⁻¹
        (normalizedBlockIntercept (planarPoint (0, l.2) 0) (planarVelocity (0, l.2))
          (midpointGroupCenter q Γ) s ((R - 2 + 2) * q) +
          τ • normalizedBlockVelocity (planarVelocity (0, l.2)) q ((R - 2 + 2) * q) - c - τ • w)‖ ≤ 2 := by
    simpa only [heq, groupIntercept, groupVelocity, planarPoint, planarVelocity] using hfit
  have h := initial_group_wholeBlockFit P hP Q hQ c w s mid hq ha ha1 hqa hB hK'
    hmid hblock hnear l.2 Γ hl.2 hvalue hfirst hsecond hfit'
  rw [heq] at h
  exact wholeBlockFit_mono (by linarith) hB.le ha h

end
end Submission.Obl.k4_horizon_chart_assembly
