import Submission.Obl.k4_quadratic_discriminant_safe_paths.Measurability
import Submission.Obl.k4_quadratic_slope_volume.PolynomialSlices
import Submission.Obl.k4_algebraic_sheet_bound.LineGeometry

namespace Submission.Obl.k4_quadratic_discriminant_safe_paths

open Set Metric

noncomputable def linePolynomial (P : MvPolynomial (Fin 3) ℝ) (a x : RealSpace) :
    Polynomial ℂ :=
  (MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.C (x i - a i) * Polynomial.X) P).map
      (algebraMap ℝ ℂ)

theorem linePolynomial_degree (P : MvPolynomial (Fin 3) ℝ) (a x : RealSpace)
    (hP : P.totalDegree ≤ 2) : (linePolynomial P a x).natDegree ≤ 2 := by
  rw [linePolynomial, Polynomial.natDegree_map]
  apply (Submission.Obl.k4_quadratic_slope_volume.natDegree_eval₂_affine_le P _ ?_).trans hP
  intro i
  apply Polynomial.natDegree_add_le_of_degree_le
  · simp
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)

theorem linePolynomial_eval (P : MvPolynomial (Fin 3) ℝ) (a x : RealSpace) (s : ℂ) :
    (linePolynomial P a x).eval s =
      MvPolynomial.eval (fun i => (emb a + s • (emb x - emb a)) i)
        (P.map (algebraMap ℝ ℂ)) := by
  rw [← MvPolynomial.eval₂_eq_eval_map]
  induction P using MvPolynomial.induction_on with
  | C r => simp [linePolynomial]
  | add P Q hP hQ =>
    simpa only [linePolynomial, MvPolynomial.eval₂_add, Polynomial.map_add,
      Polynomial.eval_add] using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP =>
    simp only [linePolynomial, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X,
      Polynomial.map_mul, Polynomial.eval_mul] at *
    rw [hP]
    congr 1
    simp [emb, Polynomial.eval_map, mul_comm]

theorem linePolynomial_zero (P : MvPolynomial (Fin 3) ℝ) (a x : RealSpace) :
    ‖(linePolynomial P a x).eval 0‖ = |MvPolynomial.eval (fun i => a i) P| := by
  rw [linePolynomial_eval]
  simp only [zero_smul, add_zero, ← MvPolynomial.eval₂_eq_eval_map]
  change ‖MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun i => (a i : ℂ)) P‖ = _
  have h := MvPolynomial.eval₂_comp_left (algebraMap ℝ ℂ) (RingHom.id ℝ)
    (fun i => a i) P
  simp only [RingHom.comp_id, Function.comp_def, Complex.coe_algebraMap] at h
  rw [← h]
  exact Complex.norm_real _

theorem linePolynomial_one (P : MvPolynomial (Fin 3) ℝ) (a x : RealSpace) :
    ‖(linePolynomial P a x).eval 1‖ = |MvPolynomial.eval (fun i => x i) P| := by
  rw [linePolynomial_eval]
  simp only [one_smul, add_sub_cancel, ← MvPolynomial.eval₂_eq_eval_map]
  change ‖MvPolynomial.eval₂ (algebraMap ℝ ℂ) (fun i => (x i : ℂ)) P‖ = _
  have h := MvPolynomial.eval₂_comp_left (algebraMap ℝ ℂ) (RingHom.id ℝ)
    (fun i => x i) P
  simp only [RingHom.comp_id, Function.comp_def, Complex.coe_algebraMap] at h
  rw [← h]
  exact Complex.norm_real _

noncomputable def complexLineAffine (a x : ComplexSpace) : ℂ →ᵃ[ℝ] ComplexSpace :=
  ((LinearMap.toSpanSingleton ℂ ComplexSpace (x - a)).restrictScalars ℝ).toAffineMap +
    AffineMap.const ℝ ℂ a

theorem complexLineAffine_apply (a x : ComplexSpace) (s : ℂ) :
    complexLineAffine a x s = a + s • (x - a) := by
  simp [complexLineAffine, add_comm]

theorem brokenPath_image (a x : RealSpace) (τ : ℂ) :
    brokenPath a x τ = complexLineAffine (emb a) (emb x) ''
      (segment ℝ (0 : ℂ) τ ∪ segment ℝ τ 1) := by
  rw [image_union, image_segment, image_segment]
  simp [complexLineAffine_apply, brokenPath]

theorem brokenPath_norm_le {a x : RealSpace} {τ : ℂ}
    (ha : ‖a‖ ≤ (1 : ℝ) / 8) (hx : ‖x‖ ≤ (1 : ℝ) / 8) (hτ : ‖τ‖ ≤ 1)
    {w : ComplexSpace} (hw : w ∈ brokenPath a x τ) : ‖w‖ ≤ 1 / 2 := by
  have hna : ‖emb a‖ ≤ (1 : ℝ) / 8 := by
    simpa only [emb, Submission.Obl.k4_algebraic_sheet_bound.norm_complexify] using ha
  have hnx : ‖emb x‖ ≤ (1 : ℝ) / 8 := by
    simpa only [emb, Submission.Obl.k4_algebraic_sheet_bound.norm_complexify] using hx
  have hnb : ‖emb a + τ • (emb x - emb a)‖ ≤ (1 : ℝ) / 2 := by
    calc
      _ ≤ ‖emb a‖ + ‖τ‖ * ‖emb x - emb a‖ := by
        simpa only [norm_smul] using norm_add_le (emb a) (τ • (emb x - emb a))
      _ ≤ ‖emb a‖ + 1 * (‖emb x‖ + ‖emb a‖) := by
        gcongr
        exact norm_sub_le _ _
      _ ≤ 1 / 2 := by linarith
  have ha' : emb a ∈ closedBall (0 : ComplexSpace) (1 / 2) := by
    rw [mem_closedBall_zero_iff]
    linarith
  have hx' : emb x ∈ closedBall (0 : ComplexSpace) (1 / 2) := by
    rw [mem_closedBall_zero_iff]
    linarith
  have hb' : emb a + τ • (emb x - emb a) ∈ closedBall (0 : ComplexSpace) (1 / 2) :=
    mem_closedBall_zero_iff.mpr hnb
  apply mem_closedBall_zero_iff.mp
  rcases hw with hw | hw
  · exact (convex_closedBall (0 : ComplexSpace) (1 / 2)).segment_subset ha' hb' hw
  · exact (convex_closedBall (0 : ComplexSpace) (1 / 2)).segment_subset hb' hx' hw

end Submission.Obl.k4_quadratic_discriminant_safe_paths
