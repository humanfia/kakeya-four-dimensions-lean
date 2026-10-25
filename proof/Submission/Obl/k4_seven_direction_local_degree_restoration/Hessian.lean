import Submission.Obl.k4_seven_direction_local_degree_restoration.GraphTaylor
import Submission.Obl.k4_real_conic_restoration.Basic

/-! The normalized Hessian is a quantitatively nonzero conic in the large case. -/

namespace Submission.Obl.k4_seven_direction_local_degree_restoration

open Submission.Obl.k4_real_conic_restoration (quad coeff coeff_nonneg coeff_le abs_sum_le)

noncomputable def normalizedHessian (f : Base → ℝ) (s : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => iteratedFDeriv ℝ 2 f 0
    ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j] / (2 * s)

lemma normalizedHessian_quad (f : Base → ℝ) (s : ℝ) (u : Base) :
    quad (normalizedHessian f s) (fun i => u i) =
      iteratedFDeriv ℝ 2 f 0 (fun _ => u) / (2 * s) := by
  unfold quad normalizedHessian
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3, u i *
      (iteratedFDeriv ℝ 2 f 0
        ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j] / (2 * s)) * u j) =
      (∑ i : Fin 3, ∑ j : Fin 3,
        iteratedFDeriv ℝ 2 f 0
          ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j] * u i * u j) / (2 * s) := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
    congr 1
    funext i
    congr 1
    funext j
    ring
  rw [hsum, bilinear_coordinates]
  congr 2
  funext i
  fin_cases i <;> rfl

lemma normalizedHessian_isSymm {f : Base → ℝ} (s : ℝ)
    (hf : ContDiffOn ℝ 3 f (Metric.ball (0 : Base) 3)) :
    (normalizedHessian f s).IsSymm := by
  have hs : IsSymmSndFDerivAt ℝ f 0 :=
    (hf.contDiffAt (Metric.isOpen_ball.mem_nhds (by simp))).isSymmSndFDerivAt (by norm_num)
  apply Matrix.ext
  intro i j
  change iteratedFDeriv ℝ 2 f 0
      ![EuclideanSpace.basisFun (Fin 3) ℝ j, EuclideanSpace.basisFun (Fin 3) ℝ i] / (2 * s) = _
  rw [IsSymmSndFDerivAt.iteratedFDeriv_cons (hf := hs)]
  rfl

lemma normalizedHessian_entry_le {f : Base → ℝ} {s A : ℝ} (hs : 0 < s)
    (h2 : ‖iteratedFDeriv ℝ 2 f 0‖ ≤ A * s) (i j : Fin 3) :
    |normalizedHessian f s i j| ≤ A / 2 := by
  have h := (iteratedFDeriv ℝ 2 f 0).le_opNorm
    ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j]
  have h' : |iteratedFDeriv ℝ 2 f 0
      ![EuclideanSpace.basisFun (Fin 3) ℝ i, EuclideanSpace.basisFun (Fin 3) ℝ j]| ≤ A * s := by
    simpa [Fin.prod_univ_two, EuclideanSpace.basisFun_apply, Real.norm_eq_abs] using h.trans
      (mul_le_mul_of_nonneg_right h2 (by positivity))
  unfold normalizedHessian
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * s)]
  refine (div_le_div_of_nonneg_right h' (by positivity : 0 ≤ 2 * s)).trans_eq ?_
  field_simp

lemma normalizedHessian_coeff_le {f : Base → ℝ} {s A : ℝ} (hs : 0 < s)
    (h2 : ‖iteratedFDeriv ℝ 2 f 0‖ ≤ A * s) :
    coeff (normalizedHessian f s) ≤ 9 * A / 2 := by
  exact (coeff_le (normalizedHessian_entry_le hs h2)).trans_eq (by ring)

lemma abs_quad_le_coeff {Q : Matrix (Fin 3) (Fin 3) ℝ} {u : Base} (hu : ‖u‖ ≤ 1) :
    |quad Q (fun i => u i)| ≤ coeff Q := by
  have hc (i : Fin 3) : |u i| ≤ 1 := by
    have hi : |u i| ≤ ‖u‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
    exact hi.trans hu
  refine (abs_sum_le _).trans ?_
  refine (Finset.sum_le_sum fun i hi => (abs_sum_le _).trans ?_)
  refine Finset.sum_le_sum fun j hj => ?_
  rw [abs_mul, abs_mul]
  calc |u i| * |Q i j| * |u j| ≤ 1 * |Q i j| * 1 := by gcongr <;> exact hc _
       _ = |Q i j| := by ring

/-- Relative non-affineness forces the normalized Hessian away from zero once the quadratic
Taylor remainder is at most half the non-affineness scale. -/
lemma normalizedHessian_coeff_lower {f : Base → ℝ} {s B : ℝ} (hs : 0 < s)
    (hf : ContDiffOn ℝ 3 f (Metric.ball (0 : Base) 3))
    (hnon : ∀ (c : ℝ) (L : Base →L[ℝ] ℝ),
      ∃ u ∈ Metric.closedBall (0 : Base) 1, s ≤ |f u - c - L u|)
    (hB : ∀ u ∈ Metric.closedBall (0 : Base) 1, ‖iteratedFDeriv ℝ 3 f u‖ ≤ B)
    (hsmall : B / 6 ≤ s / 2) :
    1 / 2 ≤ coeff (normalizedHessian f s) := by
  obtain ⟨u, hu, hna⟩ := hnon (f 0) (fderiv ℝ f 0)
  have ht := abs_sub_quadratic_taylor_le hf hB hu
  have hq := abs_quad_le_coeff (Q := normalizedHessian f s) (by simpa using hu)
  have heval : iteratedFDeriv ℝ 2 f 0 (fun _ => u) / 2 =
      s * quad (normalizedHessian f s) (fun i => u i) := by
    rw [normalizedHessian_quad]
    field_simp
  have hscaled : |iteratedFDeriv ℝ 2 f 0 (fun _ => u) / 2| ≤
      s * coeff (normalizedHessian f s) := by
    rw [heval, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left hq hs.le
  have hsplit : |f u - f 0 - fderiv ℝ f 0 u| ≤
      |f u - (f 0 + fderiv ℝ f 0 u + iteratedFDeriv ℝ 2 f 0 (fun _ => u) / 2)| +
        |iteratedFDeriv ℝ 2 f 0 (fun _ => u) / 2| := by
    convert abs_add_le
      (f u - (f 0 + fderiv ℝ f 0 u + iteratedFDeriv ℝ 2 f 0 (fun _ => u) / 2))
      (iteratedFDeriv ℝ 2 f 0 (fun _ => u) / 2) using 1
    congr 1
    ring
  nlinarith

/-- A power enlargement puts the coefficient norm in the interval required by conic restoration. -/
lemma normalizedHessian_coeff_bounds_power {f : Base → ℝ} {s A : ℝ} (hA : 2 ≤ A)
    (hlower : 1 / 2 ≤ coeff (normalizedHessian f s))
    (hupper : coeff (normalizedHessian f s) ≤ 9 * A / 2) :
    (A ^ 4)⁻¹ ≤ coeff (normalizedHessian f s) ∧ coeff (normalizedHessian f s) ≤ A ^ 4 := by
  have hA0 : 0 < A := by linarith
  have hpow3 : (8 : ℝ) ≤ A ^ 3 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
         _ ≤ A ^ 3 := pow_le_pow_left₀ (by norm_num) hA 3
  have hpow4 : (16 : ℝ) ≤ A ^ 4 := by
    calc (16 : ℝ) = 2 ^ 4 := by norm_num
         _ ≤ A ^ 4 := pow_le_pow_left₀ (by norm_num) hA 4
  constructor
  · refine le_trans ((inv_le_iff_one_le_mul₀ (pow_pos hA0 4)).2 ?_) hlower
    nlinarith
  · refine hupper.trans ?_
    calc 9 * A / 2 ≤ 8 * A := by linarith
         _ ≤ A ^ 3 * A := mul_le_mul_of_nonneg_right hpow3 hA0.le
         _ = A ^ 4 := by ring

/-- The analytic data needed before restoring the seven approximate conic zeros. -/
theorem large_normalizedHessian (K : ℕ) {f : Base → ℝ} {A b s h : ℝ}
    (hA : 2 ≤ A) (hb : 0 < b) (hh : 0 < h) (hlarge : b < s * h)
    (hscale : A ^ K * h ≤ 1)
    (hf : ContDiffOn ℝ 3 f (Metric.ball (0 : Base) 3))
    (hnon : ∀ (c : ℝ) (L : Base →L[ℝ] ℝ),
      ∃ u ∈ Metric.closedBall (0 : Base) 1, s ≤ |f u - c - L u|)
    (h2 : ‖iteratedFDeriv ℝ 2 f 0‖ ≤ A * s)
    (hthird : ∀ u ∈ Metric.closedBall (0 : Base) 1,
      ‖iteratedFDeriv ℝ 3 f u‖ ≤ A ^ K * (b + s * h))
    (p : Fin 7 → Base)
    (hsecond : ∀ i : Fin 7, |iteratedFDeriv ℝ 2 f 0 (fun _ => p i)| ≤ A * (b + s * h)) :
    0 < s ∧ (normalizedHessian f s).IsSymm ∧
      (A ^ 4)⁻¹ ≤ coeff (normalizedHessian f s) ∧
      coeff (normalizedHessian f s) ≤ A ^ 4 ∧
      (∀ i : Fin 7, |quad (normalizedHessian f s) (fun j => p i j)| ≤ A * h) ∧
      ∀ u ∈ Metric.closedBall (0 : Base) 1,
        |(f u - f 0 - fderiv ℝ f 0 u) / s -
          quad (normalizedHessian f s) (fun i => u i)| ≤ A ^ K * h := by
  have hs : 0 < s := by nlinarith
  have hA0 : 0 ≤ A := by linarith
  have hAK : 0 ≤ A ^ K := pow_nonneg hA0 K
  have hB : ∀ u ∈ Metric.closedBall (0 : Base) 1,
      ‖iteratedFDeriv ℝ 3 f u‖ ≤ 2 * A ^ K * s * h := by
    intro u hu
    refine (hthird u hu).trans ?_
    calc A ^ K * (b + s * h) ≤ A ^ K * (2 * (s * h)) :=
           mul_le_mul_of_nonneg_left (by linarith) hAK
         _ = 2 * A ^ K * s * h := by ring
  have hBs : (2 * A ^ K * s * h) / 6 ≤ s / 2 := by
    have := mul_le_mul_of_nonneg_right hscale hs.le
    nlinarith
  have hlo := normalizedHessian_coeff_lower hs hf hnon hB hBs
  have hup := normalizedHessian_coeff_le hs h2
  have hpow := normalizedHessian_coeff_bounds_power hA hlo hup
  refine ⟨hs, normalizedHessian_isSymm s hf, hpow.1, hpow.2, ?_, ?_⟩
  · intro i
    rw [normalizedHessian_quad, abs_div, abs_of_pos (by positivity : 0 < 2 * s)]
    apply (div_le_iff₀ (by positivity : 0 < 2 * s)).2
    calc |iteratedFDeriv ℝ 2 f 0 (fun _ => p i)| ≤ A * (b + s * h) := hsecond i
         _ ≤ A * (2 * (s * h)) := mul_le_mul_of_nonneg_left (by linarith) hA0
         _ = A * h * (2 * s) := by ring
  · intro u hu
    have he : (f u - f 0 - fderiv ℝ f 0 u) / s -
        quad (normalizedHessian f s) (fun i => u i) =
        (f u - (f 0 + fderiv ℝ f 0 u + iteratedFDeriv ℝ 2 f 0 (fun _ => u) / 2)) / s := by
      rw [normalizedHessian_quad]
      field_simp
      ring
    rw [he, abs_div, abs_of_pos hs]
    refine (div_le_div_of_nonneg_right (abs_sub_quadratic_taylor_le hf hB hu) hs.le).trans ?_
    apply (div_le_iff₀ hs).2
    nlinarith [mul_nonneg (mul_nonneg hAK hs.le) hh.le]

end Submission.Obl.k4_seven_direction_local_degree_restoration
