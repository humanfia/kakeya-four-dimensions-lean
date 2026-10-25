/- Adapted within this LOT tree from o190/x0633, b469254f8a8d614d595658e7ceb1bb13f4234bd2,
Submission/Obl/k4_pair_bin_atlas_assembly/Rescale.lean. Existing provenance comments are retained below. -/
import Submission.Obl.k4_matched_pair_representative_realization.Selection.Instance
import Submission.Lib.K4QuadraticSheets.QuadTest
import Submission.Obl.k4_native_finite_terminal_atlas_lift.PolynomialBounds
import Submission.Obl.k4_eligibility_sign_description.Families

-- The substitution `frameSub` and the shapes of the statements below follow the plan of this
-- LOT tree, o158, session x0532, branch x0532,
-- Submission/Obl/k4_matched_pair_representative_realization/Rescale.lean (statements only).

/-!
# A normalized-frame test in model coordinates

`phys T j κ c u Q B P` is the test `P` of the normalized frame (base coordinates and the
scaled hidden coordinate `B w`) written in the model coordinates `(t, y₁, y₂, w)` of `x`:
`eval (x l t) (phys … P) = eval (framePt … l t) P`.  The substitution is affine, so the
total degree does not grow, the hidden derivatives scale by `B` and `B ^ 2`, and the hidden
discriminant becomes `B ^ 2` times the frozen `disc` at the base point.
-/

namespace Submission.Obl.k4_matched_pair_representative_realization.Selection

open Submission.Obl.k4_quadratic_atlas_normalization MvPolynomial
open Submission.Obl.k4_native_finite_terminal_atlas_lift (coefficientMass)

/-- The substitution taking model coordinates `(t, y₁, y₂, w)` to `(base, B w)`. -/
noncomputable def frameSub (T : ℕ) (j κ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![C ((2 : ℝ) ^ T / (100 * κ)) * X 0 - C ((j + 1 / 2) / (100 * κ)),
    C (Q⁻¹ 0 0 / (100 * κ)) * (X 1 - C (c 0) - C (u 0) * X 0) +
      C (Q⁻¹ 0 1 / (100 * κ)) * (X 2 - C (c 1) - C (u 1) * X 0),
    C (Q⁻¹ 1 0 / (100 * κ)) * (X 1 - C (c 0) - C (u 0) * X 0) +
      C (Q⁻¹ 1 1 / (100 * κ)) * (X 2 - C (c 1) - C (u 1) * X 0),
    C B * X 3]

/-- The test `P` of the normalized frame, in model coordinates. -/
noncomputable def phys (T : ℕ) (j κ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (P : MvPolynomial (Fin 4) ℝ) :
    MvPolynomial (Fin 4) ℝ :=
  aeval (frameSub T j κ c u Q B) P

/-- The frame point of a trajectory at time `t`: base coordinates and scaled hidden value. -/
noncomputable def framePt (T : ℕ) (j κ : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (l : Traj) (t : ℝ) : Fin 4 → ℝ :=
  Fin.snoc (fun i : Fin 3 => base T j κ c u Q l t i) (B * x l t 3)

variable {T : ℕ} {j κ : ℝ} {c u : EuclideanSpace ℝ (Fin 2)} {Q : Matrix (Fin 2) (Fin 2) ℝ}
  {B : ℝ}

theorem framePt_zero (l : Traj) (t : ℝ) :
    framePt T j κ c u Q B l t 0 = ((2 : ℝ) ^ T * t - j - 1 / 2) / (100 * κ) := by
  simp [framePt, base, Fin.snoc]

theorem framePt_one (l : Traj) (t : ℝ) :
    framePt T j κ c u Q B l t 1 = (Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)) 0 / (100 * κ) := by
  simp [framePt, base, Fin.snoc]

theorem framePt_two (l : Traj) (t : ℝ) :
    framePt T j κ c u Q B l t 2 = (Matrix.toEuclideanLin Q⁻¹ (y l t - c - t • u)) 1 / (100 * κ) := by
  have : (2 : Fin 4) = Fin.castSucc (2 : Fin 3) := rfl
  rw [this, framePt, Fin.snoc_castSucc]
  simp [base]

theorem framePt_three (l : Traj) (t : ℝ) : framePt T j κ c u Q B l t 3 = B * x l t 3 :=
  Fin.snoc_last (α := fun _ => ℝ) (B * x l t 3) (fun i : Fin 3 => base T j κ c u Q l t i)

theorem eval_frameSub (l : Traj) (t : ℝ) :
    (fun i => eval (x l t) (frameSub T j κ c u Q B i)) = framePt T j κ c u Q B l t := by
  funext i
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · simp only [framePt_zero]; simp [frameSub, x]; ring
  · simp only [framePt_one]
    simp [frameSub, x, y, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp only [framePt_two]
    simp [frameSub, x, y, Matrix.toEuclideanLin, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    ring
  · simp only [framePt_three]; simp [frameSub, x]

theorem eval_phys (P : MvPolynomial (Fin 4) ℝ) (l : Traj) (t : ℝ) :
    eval (x l t) (phys T j κ c u Q B P) = eval (framePt T j κ c u Q B l t) P := by
  rw [phys, Submission.Obl.k4_eligibility_sign_description.eval_aeval_real, eval_frameSub]

theorem totalDegree_frameSub_le (i : Fin 4) : (frameSub T j κ c u Q B i).totalDegree ≤ 1 := by
  have hX : ∀ k : Fin 4, (X k : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 :=
    fun k => (totalDegree_X k).le
  have hCX : ∀ (a : ℝ) (k : Fin 4), (C a * X k : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := by
    intro a k
    exact (totalDegree_mul _ _).trans (by simp)
  have hlin : ∀ (a b : ℝ) (k : Fin 4),
      (X k - C a - C b * X 0 : MvPolynomial (Fin 4) ℝ).totalDegree ≤ 1 := by
    intro a b k
    exact (totalDegree_sub _ _).trans
      (max_le ((totalDegree_sub _ _).trans (max_le (hX k) (by simp))) (hCX b 0))
  have hmul : ∀ (a : ℝ) (p : MvPolynomial (Fin 4) ℝ), p.totalDegree ≤ 1 →
      (C a * p).totalDegree ≤ 1 := by
    intro a p hp
    exact (totalDegree_mul _ _).trans (by simpa using hp)
  fin_cases i <;> simp only [frameSub, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · exact (totalDegree_sub _ _).trans (max_le (hCX _ _) (by simp))
  · exact (totalDegree_add _ _).trans (max_le (hmul _ _ (hlin _ _ 1)) (hmul _ _ (hlin _ _ 2)))
  · exact (totalDegree_add _ _).trans (max_le (hmul _ _ (hlin _ _ 1)) (hmul _ _ (hlin _ _ 2)))
  · exact hCX _ _

theorem totalDegree_phys_le (P : MvPolynomial (Fin 4) ℝ) :
    (phys T j κ c u Q B P).totalDegree ≤ P.totalDegree :=
  Submission.Obl.k4_eligibility_sign_description.degree_aeval_le P _ totalDegree_frameSub_le

theorem pderiv_frameSub (i : Fin 4) :
    pderiv (3 : Fin 4) (frameSub T j κ c u Q B i) = if i = 3 then C B else 0 := by
  fin_cases i <;> simp [frameSub, pderiv_X]

theorem pderiv_phys (P : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (phys T j κ c u Q B P) =
      C B * phys T j κ c u Q B (pderiv (3 : Fin 4) P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [phys]
  | add p q hp hq => simp only [phys, map_add] at hp hq ⊢; rw [hp, hq]; ring
  | mul_X p i ih =>
    simp only [phys] at ih ⊢
    have h1 : pderiv (3 : Fin 4) (p * X i) = pderiv 3 p * X i + p * pderiv 3 (X i) := by
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
    rw [map_mul, aeval_X, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ih, h1, map_add,
      map_mul, map_mul, aeval_X, pderiv_X, pderiv_frameSub]
    by_cases hi : i = 3
    · subst hi; simp; ring
    · simp [hi]; ring

theorem pderiv_pderiv_phys (P : MvPolynomial (Fin 4) ℝ) :
    pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (phys T j κ c u Q B P)) =
      C (B ^ 2) * phys T j κ c u Q B (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) := by
  rw [pderiv_phys, pderiv_C_mul, pderiv_phys, ← mul_assoc, ← C_mul, sq]

theorem eval_pderiv_phys (P : MvPolynomial (Fin 4) ℝ) (l : Traj) (t : ℝ) :
    eval (x l t) (pderiv (3 : Fin 4) (phys T j κ c u Q B P)) =
      B * eval (framePt T j κ c u Q B l t) (pderiv (3 : Fin 4) P) := by
  rw [pderiv_phys, eval_mul, eval_C, eval_phys]

theorem eval_pderiv_pderiv_phys (P : MvPolynomial (Fin 4) ℝ) (l : Traj) (t : ℝ) :
    eval (x l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (phys T j κ c u Q B P))) =
      B ^ 2 * eval (framePt T j κ c u Q B l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) := by
  rw [pderiv_pderiv_phys, eval_mul, eval_C, eval_phys]

/-- The frozen `disc` is the hidden discriminant expression at hidden value zero. -/
theorem eval_disc (P : MvPolynomial (Fin 4) ℝ) (z : Fin 3 → ℝ) :
    eval z (disc P) =
      (eval (Fin.snoc z 0 : Fin 4 → ℝ) (pderiv (3 : Fin 4) P)) ^ 2 -
        2 * eval (Fin.snoc z 0 : Fin 4 → ℝ) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) *
          eval (Fin.snoc z 0 : Fin 4 → ℝ) P := by
  have hsub : (eval z ∘ fun i => Fin.lastCases (0 : MvPolynomial (Fin 3) ℝ) X i) =
      (Fin.snoc z 0 : Fin 4 → ℝ) := by
    funext i
    refine Fin.lastCases ?_ (fun k => ?_) i
    · show eval z (Fin.lastCases (0 : MvPolynomial (Fin 3) ℝ) X (Fin.last 3)) =
        (Fin.snoc z 0 : Fin 4 → ℝ) (Fin.last 3)
      simp only [Fin.lastCases_last, Fin.snoc_last, map_zero]
    · simp
  change eval z (eval₂ C (fun i => Fin.lastCases (0 : MvPolynomial (Fin 3) ℝ) X i) _) = _
  rw [← eval_assoc, hsub]
  simp only [map_sub, map_mul, map_pow, eval_ofNat]

/-- For a test of degree at most two, the hidden discriminant expression is the
`K4QuadraticSheets` discriminant, whatever the hidden value. -/
theorem hiddenDisc_eq_qdisc (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) (w : ℝ) :
    (eval (Fin.snoc z w : Fin 4 → ℝ) (pderiv (3 : Fin 4) P)) ^ 2 -
        2 * eval (Fin.snoc z w : Fin 4 → ℝ) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) *
          eval (Fin.snoc z w : Fin 4 → ℝ) P = Submission.Lib.K4QuadraticSheets.qdisc P z := by
  have h1 := Submission.Lib.K4QuadraticSheets.pderiv_sq_eq_qdisc_add P hP z w
  have h2 := Submission.Lib.K4QuadraticSheets.eval_pderiv2_eq_qc P hP (Fin.snoc z w)
  change (eval (Fin.snoc z w : Fin 4 → ℝ) (pderiv (Fin.last 3) P)) ^ 2 -
        2 * eval (Fin.snoc z w : Fin 4 → ℝ) (pderiv (Fin.last 3) (pderiv (Fin.last 3) P)) *
          eval (Fin.snoc z w : Fin 4 → ℝ) P = _
  rw [h1, h2]
  ring

/-- The hidden discriminant of a test of degree at most two does not depend on the hidden
value, and equals the frozen `disc` at the base point. -/
theorem disc_eval_snoc (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (z : Fin 3 → ℝ)
    (w : ℝ) :
    (eval (Fin.snoc z w : Fin 4 → ℝ) (pderiv (3 : Fin 4) P)) ^ 2 -
        2 * eval (Fin.snoc z w : Fin 4 → ℝ) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) *
          eval (Fin.snoc z w : Fin 4 → ℝ) P = eval z (disc P) := by
  rw [eval_disc, hiddenDisc_eq_qdisc P hP z w, hiddenDisc_eq_qdisc P hP z 0]

/-- The physical discriminant is `B ^ 2` times the frozen `disc` at the base point. -/
theorem disc_phys (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2) (l : Traj) (t : ℝ) :
    (eval (x l t) (pderiv (3 : Fin 4) (phys T j κ c u Q B P))) ^ 2 -
        2 * eval (x l t) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) (phys T j κ c u Q B P))) *
          eval (x l t) (phys T j κ c u Q B P) =
      B ^ 2 * eval (fun i : Fin 3 => base T j κ c u Q l t i) (disc P) := by
  rw [eval_pderiv_phys, eval_pderiv_pderiv_phys, eval_phys,
    ← disc_eval_snoc P hP _ (B * x l t 3)]
  simp only [framePt]
  ring

/-- The second hidden derivative of a test of degree at most two is constant. -/
theorem eval_pderiv_pderiv_const (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (v : Fin 4 → ℝ) :
    eval v (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) =
      eval (0 : Fin 4 → ℝ) (pderiv (3 : Fin 4) (pderiv (3 : Fin 4) P)) :=
  Submission.Lib.K4QuadraticSheets.eval_pderiv2_eq_qc P hP v

/-- Coefficient sums of the frame substitution are polynomial in the frame data. -/
theorem coefficientMass_frameSub_le {Z : ℝ} (hZ : 1 ≤ Z) (hκ : 1 ≤ κ)
    (hT : (2 : ℝ) ^ T ≤ Z) (hj : |j| ≤ Z) (hQ : ∀ i k, |Q⁻¹ i k| ≤ Z)
    (hc : ∀ i, |c i| ≤ Z) (hu : ∀ i, |u i| ≤ Z) (hB : |B| ≤ Z) (i : Fin 4) :
    coefficientMass (frameSub T j κ c u Q B i) ≤ 6 * Z ^ 2 := by
  open Submission.Obl.k4_native_finite_terminal_atlas_lift in
  have h100 : (1 : ℝ) ≤ 100 * κ := by linarith
  have h100' : (0 : ℝ) < 100 * κ := by linarith
  have hdiv : ∀ a : ℝ, |a / (100 * κ)| ≤ |a| := by
    intro a
    rw [abs_div, abs_of_pos h100']
    exact div_le_self (abs_nonneg a) h100
  have hlin : ∀ (k : Fin 4) (a b : ℝ), |a| ≤ Z → |b| ≤ Z →
      coefficientMass (X k - C a - C b * X 0 : MvPolynomial (Fin 4) ℝ) ≤ 3 * Z := by
    intro k a b ha hb
    calc _ ≤ coefficientMass (X k - C a : MvPolynomial (Fin 4) ℝ) +
          coefficientMass (C b * X 0 : MvPolynomial (Fin 4) ℝ) := coefficientMass_sub _ _
      _ ≤ (coefficientMass (X k : MvPolynomial (Fin 4) ℝ) +
            coefficientMass (C a : MvPolynomial (Fin 4) ℝ)) +
          coefficientMass (C b : MvPolynomial (Fin 4) ℝ) *
            coefficientMass (X 0 : MvPolynomial (Fin 4) ℝ) :=
          add_le_add (coefficientMass_sub _ _) (coefficientMass_mul _ _)
      _ ≤ 3 * Z := by
          rw [coefficientMass_X, coefficientMass_C, coefficientMass_C, coefficientMass_X]
          linarith
  have hrow : ∀ (a₀ a₁ : ℝ), |a₀| ≤ Z → |a₁| ≤ Z →
      coefficientMass (C (a₀ / (100 * κ)) * (X 1 - C (c 0) - C (u 0) * X 0) +
        C (a₁ / (100 * κ)) * (X 2 - C (c 1) - C (u 1) * X 0) : MvPolynomial (Fin 4) ℝ) ≤
          6 * Z ^ 2 := by
    intro a₀ a₁ h₀ h₁
    calc _ ≤ coefficientMass (C (a₀ / (100 * κ)) * (X 1 - C (c 0) - C (u 0) * X 0) :
            MvPolynomial (Fin 4) ℝ) +
          coefficientMass (C (a₁ / (100 * κ)) * (X 2 - C (c 1) - C (u 1) * X 0) :
            MvPolynomial (Fin 4) ℝ) := coefficientMass_add _ _
      _ ≤ |a₀ / (100 * κ)| * (3 * Z) + |a₁ / (100 * κ)| * (3 * Z) := by
          refine add_le_add ((coefficientMass_mul _ _).trans ?_) ((coefficientMass_mul _ _).trans ?_)
          · rw [coefficientMass_C]
            exact mul_le_mul_of_nonneg_left (hlin 1 _ _ (hc 0) (hu 0)) (abs_nonneg _)
          · rw [coefficientMass_C]
            exact mul_le_mul_of_nonneg_left (hlin 2 _ _ (hc 1) (hu 1)) (abs_nonneg _)
      _ ≤ Z * (3 * Z) + Z * (3 * Z) := by
          gcongr
          · exact (hdiv a₀).trans h₀
          · exact (hdiv a₁).trans h₁
      _ = 6 * Z ^ 2 := by ring
  fin_cases i <;> simp only [frameSub, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val]
  · calc _ ≤ coefficientMass (C ((2 : ℝ) ^ T / (100 * κ)) * X 0 : MvPolynomial (Fin 4) ℝ) +
          coefficientMass (C ((j + 1 / 2) / (100 * κ)) : MvPolynomial (Fin 4) ℝ) :=
          coefficientMass_sub _ _
      _ ≤ |(2 : ℝ) ^ T / (100 * κ)| * 1 + |(j + 1 / 2) / (100 * κ)| := by
          gcongr
          · exact (coefficientMass_mul _ _).trans (by rw [coefficientMass_C, coefficientMass_X])
          · rw [coefficientMass_C]
      _ ≤ Z * 1 + 2 * Z := by
          gcongr
          · exact (hdiv _).trans (by rw [abs_of_pos (by positivity)]; exact hT)
          · exact (hdiv _).trans ((abs_add_le _ _).trans (by
              rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]; linarith))
      _ ≤ 6 * Z ^ 2 := by nlinarith
  · exact hrow _ _ (hQ 0 0) (hQ 0 1)
  · exact hrow _ _ (hQ 1 0) (hQ 1 1)
  · calc _ ≤ coefficientMass (C B : MvPolynomial (Fin 4) ℝ) *
          coefficientMass (X 3 : MvPolynomial (Fin 4) ℝ) := coefficientMass_mul _ _
      _ = |B| := by rw [coefficientMass_C, coefficientMass_X, mul_one]
      _ ≤ 6 * Z ^ 2 := by nlinarith

/-- Coefficients of the model-coordinate test are polynomially bounded. -/
theorem abs_coeff_phys_le (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    {K Z : ℝ} (hK0 : 0 ≤ K) (hK : ∀ e, |P.coeff e| ≤ K) (hZ : 1 ≤ Z) (hκ : 1 ≤ κ)
    (hT : (2 : ℝ) ^ T ≤ Z) (hj : |j| ≤ Z) (hQ : ∀ i k, |Q⁻¹ i k| ≤ Z)
    (hc : ∀ i, |c i| ≤ Z) (hu : ∀ i, |u i| ≤ Z) (hB : |B| ≤ Z) (e : Fin 4 →₀ ℕ) :
    |(phys T j κ c u Q B P).coeff e| ≤ 81 * K * (6 * Z ^ 2) ^ 2 := by
  open Submission.Obl.k4_native_finite_terminal_atlas_lift in
  have hH : (1 : ℝ) ≤ 6 * Z ^ 2 := by nlinarith
  calc _ ≤ coefficientMass (phys T j κ c u Q B P) := abs_coeff_le_coefficientMass _ e
    _ ≤ coefficientMass P * (6 * Z ^ 2) ^ 2 :=
        coefficientMass_aeval P hP _ hH
          (coefficientMass_frameSub_le hZ hκ hT hj hQ hc hu hB)
    _ ≤ (((2 + 1) ^ 4 : ℕ) * K) * (6 * Z ^ 2) ^ 2 := by
        gcongr
        exact coefficientMass_le_of_coeff_bound P hP hK0 hK
    _ = 81 * K * (6 * Z ^ 2) ^ 2 := by norm_num

end Submission.Obl.k4_matched_pair_representative_realization.Selection
