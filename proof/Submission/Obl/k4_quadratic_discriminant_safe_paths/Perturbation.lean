import Mathlib

namespace Submission.Obl.k4_quadratic_discriminant_safe_paths

open Set Metric

/-- The coefficient bound gives a uniform Lipschitz bound for quadratics on
the complex unit ball. Only the existence of an absolute constant is needed. -/
theorem exists_quadratic_lipschitz : ∃ L : ℝ, 0 < L ∧
    ∀ (A : ℝ) (P : MvPolynomial (Fin 3) ℝ), 0 ≤ A → P.totalDegree ≤ 2 →
      (∀ d, |P.coeff d| ≤ A) →
    ∀ z w : EuclideanSpace ℂ (Fin 3), ‖z‖ ≤ 1 → ‖w‖ ≤ 1 →
      ‖MvPolynomial.eval (fun i => z i) (P.map (algebraMap ℝ ℂ)) -
        MvPolynomial.eval (fun i => w i) (P.map (algebraMap ℝ ℂ))‖ ≤
      L * A * dist z w := by
  classical
  let M : Finset (Fin 3 →₀ ℕ) := Finset.univ.image
    (fun d : Fin 3 → Fin 3 => Finsupp.equivFunOnFinite.symm (fun i => (d i : ℕ)))
  let m (d : Fin 3 →₀ ℕ) (z : EuclideanSpace ℂ (Fin 3)) : ℂ :=
    ∏ i, z i ^ d i
  have hK : ∀ d, ∃ K : NNReal, LipschitzOnWith K (m d)
      (closedBall (0 : EuclideanSpace ℂ (Fin 3)) 1) := by
    intro d
    have hdiff : ContDiff ℝ 1 (m d) := by dsimp [m]; fun_prop
    exact hdiff.contDiffOn.exists_lipschitzOnWith (by norm_num)
      (convex_closedBall _ _) (isCompact_closedBall _ _)
  choose K hK using hK
  let L : ℝ := (∑ d ∈ M, (K d : ℝ)) + 1
  have hsum : 0 ≤ ∑ d ∈ M, (K d : ℝ) :=
    Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)
  refine ⟨L, by dsimp [L]; linarith, ?_⟩
  intro A P hA hdeg hcoeff z w hz hw
  have hsupport : P.support ⊆ M := by
    intro d hd
    have hdle (i : Fin 3) : d i < 3 := by
      have := (MvPolynomial.le_degreeOf_of_mem_support i hd).trans
        ((MvPolynomial.degreeOf_le_totalDegree P i).trans hdeg)
      omega
    apply Finset.mem_image.mpr
    refine ⟨fun i => ⟨d i, hdle i⟩, Finset.mem_univ _, ?_⟩
    ext i
    simp
  have heval (u : EuclideanSpace ℂ (Fin 3)) :
      MvPolynomial.eval (fun i => u i) (P.map (algebraMap ℝ ℂ)) =
      ∑ d ∈ P.support, (P.coeff d : ℂ) * m d u := by
    rw [← MvPolynomial.eval₂_eq_eval_map, MvPolynomial.eval₂_eq']
    rfl
  rw [heval, heval, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ P.support, ‖(P.coeff d : ℂ) * m d z -
        (P.coeff d : ℂ) * m d w‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ P.support, A * (K d : ℝ) * dist z w := by
      apply Finset.sum_le_sum
      intro d hd
      rw [← mul_sub, norm_mul]
      have hcoeff' : ‖(P.coeff d : ℂ)‖ ≤ A := by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using hcoeff d
      have hm : ‖m d z - m d w‖ ≤ (K d : ℝ) * dist z w := by
        simpa only [dist_eq_norm] using (hK d).dist_le_mul z
          (by simpa using hz) w (by simpa using hw)
      exact (mul_le_mul hcoeff' hm (norm_nonneg _) hA).trans_eq (by ring)
    _ ≤ ∑ d ∈ M, A * (K d : ℝ) * dist z w :=
      Finset.sum_le_sum_of_subset_of_nonneg hsupport (by intros; positivity)
    _ = (∑ d ∈ M, (K d : ℝ)) * A * dist z w := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      ring
    _ ≤ L * A * dist z w := by
      apply mul_le_mul_of_nonneg_right _ (dist_nonneg : 0 ≤ dist z w)
      apply mul_le_mul_of_nonneg_right _ hA
      dsimp [L]
      linarith

end Submission.Obl.k4_quadratic_discriminant_safe_paths
