-- Adapted from this LOT tree, o156, session x0524, commit86ade225;
-- Submission/Obl/k4_terminal_local_sheet_pairing/PolynomialSheets.lean. Existing attribution comments are retained below.

import Submission.Obl.k4_paired_test_normalization.QuadraticExpansion

namespace Submission.Obl.k4_paired_test_normalization

open MvPolynomial Set

/-- Dropping the hidden variable commutes with complexification and evaluation. -/
theorem eval_complex_hidden_restriction (P : MvPolynomial (Fin 4) ℝ) (z : Fin 3 → ℂ) :
    eval z ((eval₂Hom C (Fin.lastCases (0 : MvPolynomial (Fin 3) ℝ) X) P).map
      (algebraMap ℝ ℂ)) = eval (Fin.snoc z 0) (P.map (algebraMap ℝ ℂ)) := by
  rw [eval_map, eval_map]
  let H : MvPolynomial (Fin 4) ℝ →+* ℂ :=
    (eval₂Hom (algebraMap ℝ ℂ) z).comp
      (eval₂Hom C (Fin.lastCases (0 : MvPolynomial (Fin 3) ℝ) X))
  have hh : H = eval₂Hom (algebraMap ℝ ℂ) (Fin.snoc z 0) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [H]
    · intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp [H]
        change eval₂ (algebraMap ℝ ℂ) z (0 : MvPolynomial (Fin 3) ℝ) = 0
        simp
      · simp [H]
  exact DFunLike.congr_fun hh P

/-- The frozen three-variable discriminant is the usual quadratic discriminant
of the hidden-value equation, also at complex base points. -/
theorem eval_complex_disc (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℂ) :
    eval z ((disc P).map (algebraMap ℝ ℂ)) =
      eval (Fin.snoc z 0) ((pderiv (3 : Fin 4) P).map (algebraMap ℝ ℂ)) ^ 2 -
      2 * (Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) : ℂ) *
        eval (Fin.snoc z 0) (P.map (algebraMap ℝ ℂ)) := by
  unfold disc
  rw [eval_complex_hidden_restriction]
  simp only [Submission.Obl.k4_quadratic_atlas_normalization.second_pderiv_eq_curvature P hP,
    map_sub, map_pow, map_mul, map_ofNat, map_C, eval_C, Complex.coe_algebraMap]

/-- The two coefficient functions used to construct quadratic sheets. -/
noncomputable def hiddenConstant (P : MvPolynomial (Fin 4) ℝ)
    (z : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  eval (Fin.snoc (fun i : Fin 3 => z i) 0) (P.map (algebraMap ℝ ℂ))

noncomputable def hiddenLinear (P : MvPolynomial (Fin 4) ℝ)
    (z : EuclideanSpace ℂ (Fin 3)) : ℂ :=
  hiddenConstant (pderiv (3 : Fin 4) P) z

noncomputable def halfCurvature (P : MvPolynomial (Fin 4) ℝ) : ℝ :=
  Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) / 2

/-- One of the two real quadratic sheets; a linear equation repeats its unique sheet. -/
noncomputable def simpleSheet (P : MvPolynomial (Fin 4) ℝ) (σ : ℝ) :
    EuclideanSpace ℂ (Fin 3) → ℂ :=
  if halfCurvature P = 0 then fun z => -hiddenConstant P z / hiddenLinear P z
  else quadraticBranch (hiddenConstant P) (hiddenLinear P) (halfCurvature P) σ

theorem hiddenConstant_ofReal (P : MvPolynomial (Fin 4) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    hiddenConstant P (emb x) = (eval (Fin.snoc (fun i : Fin 3 => x i) 0) P : ℂ) := by
  change eval (Fin.snoc (fun i : Fin 3 => (x i : ℂ)) 0) (P.map (algebraMap ℝ ℂ)) = _
  exact eval_complexification_snoc_zero P _

theorem hiddenLinear_ofReal (P : MvPolynomial (Fin 4) ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    hiddenLinear P (emb x) =
      (eval (Fin.snoc (fun i : Fin 3 => x i) 0) (pderiv (3 : Fin 4) P) : ℂ) :=
  hiddenConstant_ofReal _ _

theorem eval_real_disc (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (z : Fin 3 → ℝ) :
    eval z (disc P) = (eval (Fin.snoc z 0) (pderiv (3 : Fin 4) P)) ^ 2 -
      2 * Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) *
        eval (Fin.snoc z 0) P := by
  have h := eval_complex_disc P hP (fun i : Fin 3 => (z i : ℂ))
  rw [eval_complexification, eval_complexification_snoc_zero,
    eval_complexification_snoc_zero] at h
  exact_mod_cast h

/-- The sign of the derivative chooses a sheet with the nearest-root bound. -/
theorem simpleSheet_error (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (σ : ℝ) (hσ : σ ^ 2 = 1) (x : EuclideanSpace ℝ (Fin 3)) (w : ℝ)
    (hdisc : 0 ≤ eval (fun i => x i) (disc P))
    (hne : eval (Fin.snoc (fun i : Fin 3 => x i) w) (pderiv (3 : Fin 4) P) ≠ 0)
    (hsign : σ * eval (Fin.snoc (fun i : Fin 3 => x i) w) (pderiv (3 : Fin 4) P) =
      |eval (Fin.snoc (fun i : Fin 3 => x i) w) (pderiv (3 : Fin 4) P)|) :
    ‖simpleSheet P σ (emb x) - (w : ℂ)‖ ≤
      2 * |eval (Fin.snoc (fun i : Fin 3 => x i) w) P| /
        |eval (Fin.snoc (fun i : Fin 3 => x i) w) (pderiv (3 : Fin 4) P)| := by
  let a := eval (Fin.snoc (fun i : Fin 3 => x i) 0) P
  let b := eval (Fin.snoc (fun i : Fin 3 => x i) 0) (pderiv (3 : Fin 4) P)
  let c := halfCurvature P
  have hp : eval (Fin.snoc (fun i : Fin 3 => x i) w) P = a + b * w + c * w ^ 2 :=
    eval_real_hidden_quadratic P hP _ w
  have hder : eval (Fin.snoc (fun i : Fin 3 => x i) w) (pderiv (3 : Fin 4) P) =
      b + 2 * c * w := by
    rw [eval_real_hidden_derivative P hP]
    dsimp [b, c, halfCurvature]
    ring
  have hd : 0 ≤ b ^ 2 - 4 * c * a := by
    rw [eval_real_disc P hP] at hdisc
    dsimp [a, b, c, halfCurvature]
    convert hdisc using 1 <;> ring
  rw [hp, hder]
  rw [hder] at hne hsign
  by_cases hc : c = 0
  · have hb : b ≠ 0 := by simpa only [hc, mul_zero, zero_mul, add_zero] using hne
    have hfun : simpleSheet P σ (emb x) = ((-a / b : ℝ) : ℂ) := by
      unfold simpleSheet
      rw [ite_eq_left hc]
      simp only [hiddenConstant_ofReal, hiddenLinear_ofReal,
        Complex.ofReal_div, Complex.ofReal_neg]
      rfl
    rw [hfun, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    simp only [hc, mul_zero, zero_mul, add_zero]
    have hid : -a / b - w = -(a + b * w) / b := by field_simp [hb]; ring
    rw [hid, abs_div, abs_neg]
    have hnum : |a + b * w| ≤ 2 * |a + b * w| := by nlinarith [abs_nonneg (a + b * w)]
    exact div_le_div_of_nonneg_right hnum (abs_nonneg b)
  · have hfun : simpleSheet P σ (emb x) =
        (((-b + σ * Real.sqrt (b ^ 2 - 4 * c * a)) / (2 * c) : ℝ) : ℂ) := by
      unfold simpleSheet
      rw [ite_eq_right hc]
      exact quadraticBranch_ofReal (hiddenConstant_ofReal P x) (hiddenLinear_ofReal P x) hd
    rw [hfun, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact quadraticBranch_error hc hσ hd hne hsign

/-- The discriminant hypothesis alone gives simple real holomorphic sheets.
The real-input assertion is restricted only by membership in the complex domain. -/
theorem simpleSheet_spec (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (σ : ℝ) (hσ : σ ^ 2 = 1)
    (U : Set (EuclideanSpace ℂ (Fin 3)))
    (hdisc : ∀ z ∈ U, 0 < (eval (fun i => z i) ((disc P).map (algebraMap ℝ ℂ))).re) :
      DifferentiableOn ℂ (simpleSheet P σ) U ∧
      (∀ z ∈ U, eval (Fin.snoc (fun i : Fin 3 => z i) (simpleSheet P σ z))
        (P.map (algebraMap ℝ ℂ)) = 0 ∧
        eval (Fin.snoc (fun i : Fin 3 => z i) (simpleSheet P σ z))
          ((pderiv (3 : Fin 4) P).map (algebraMap ℝ ℂ)) ≠ 0) ∧
      ∀ x : EuclideanSpace ℝ (Fin 3), emb x ∈ U → (simpleSheet P σ (emb x)).im = 0 := by
  let a := hiddenConstant P
  let b := hiddenLinear P
  let c := halfCurvature P
  have ha : DifferentiableOn ℂ a U := (differentiable_hidden_zero _).differentiableOn
  have hb : DifferentiableOn ℂ b U := (differentiable_hidden_zero _).differentiableOn
  have hd (z : EuclideanSpace ℂ (Fin 3)) :
      b z ^ 2 - 4 * (c : ℂ) * a z =
        eval (fun i => z i) ((disc P).map (algebraMap ℝ ℂ)) := by
    rw [eval_complex_disc P hP]
    dsimp [a, b, c, hiddenConstant, hiddenLinear, halfCurvature]
    push_cast
    ring
  have har (x : EuclideanSpace ℝ (Fin 3)) :
      a (emb x) = (eval (Fin.snoc (fun i : Fin 3 => x i) 0) P : ℂ) := by
    change eval (Fin.snoc (fun i : Fin 3 => (x i : ℂ)) 0) (P.map (algebraMap ℝ ℂ)) = _
    have heq : Fin.snoc (fun i : Fin 3 => (x i : ℂ)) (0 : ℂ) =
        (fun i : Fin 4 => ((Fin.snoc (fun i : Fin 3 => x i) 0 : Fin 4 → ℝ) i : ℂ)) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change (0 : ℂ) = ((0 : ℝ) : ℂ)
        rfl
      · simp
    rw [heq]
    exact eval_complexification P _
  have hbr (x : EuclideanSpace ℝ (Fin 3)) :
      b (emb x) = (eval (Fin.snoc (fun i : Fin 3 => x i) 0) (pderiv (3 : Fin 4) P) : ℂ) := by
    change hiddenConstant (pderiv (3 : Fin 4) P) (emb x) = _
    change eval (Fin.snoc (fun i : Fin 3 => (x i : ℂ)) 0)
      ((pderiv (3 : Fin 4) P).map (algebraMap ℝ ℂ)) = _
    have heq : Fin.snoc (fun i : Fin 3 => (x i : ℂ)) (0 : ℂ) =
        (fun i : Fin 4 => ((Fin.snoc (fun i : Fin 3 => x i) 0 : Fin 4 → ℝ) i : ℂ)) := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · change (0 : ℂ) = ((0 : ℝ) : ℂ)
        rfl
      · simp
    rw [heq]
    exact eval_complexification _ _
  by_cases hc : c = 0
  · have hb0 (z) (hz : z ∈ U) : b z ≠ 0 := by
      have hp := hdisc z hz
      rw [← hd z, hc] at hp
      intro heq
      simp [heq] at hp
    obtain ⟨hF, hroot⟩ := linearBranch_simple ha hb hb0
    have hfun : simpleSheet P σ = (fun z => -a z / b z) := by
      unfold simpleSheet
      rw [ite_eq_left hc]
    rw [hfun]
    refine ⟨hF, ?_, ?_⟩
    · intro z hz
      have hcurv : Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) = 0 := by
        dsimp [c, halfCurvature] at hc
        linarith
      constructor
      · rw [eval_hidden_quadratic P hP]
        simp only [hcurv, Complex.ofReal_zero, zero_div, zero_mul, add_zero]
        exact (hroot z hz).1
      · rw [eval_hidden_derivative P hP]
        simp only [hcurv, Complex.ofReal_zero, zero_mul, add_zero]
        exact (hroot z hz).2
    · intro x hx
      change (-a (emb x) / b (emb x)).im = 0
      rw [har, hbr]
      simp [← Complex.ofReal_div, ← Complex.ofReal_neg]
  · obtain ⟨hF, hroot⟩ := quadraticBranch_simple hc hσ
      ha hb (fun z hz => by rw [hd]; exact hdisc z hz)
    have hfun : simpleSheet P σ = quadraticBranch a b c σ := by
      unfold simpleSheet
      rw [ite_eq_right hc]
    rw [hfun]
    refine ⟨hF, ?_, ?_⟩
    · intro z hz
      have hcurv :
          (Submission.Obl.k4_quadratic_atlas_normalization.curvature P (3 : Fin 4) : ℂ) =
          2 * (c : ℂ) := by dsimp [c, halfCurvature]; push_cast; ring
      constructor
      · rw [eval_hidden_quadratic P hP, hcurv]
        change a z + b z * quadraticBranch a b c σ z +
          (2 * (c : ℂ)) / 2 * quadraticBranch a b c σ z ^ 2 = 0
        simpa only [mul_div_cancel_left₀ _ (by norm_num : (2 : ℂ) ≠ 0)] using (hroot z hz).1
      · rw [eval_hidden_derivative P hP, hcurv]
        exact (hroot z hz).2
    · intro x hx
      have hpos := hdisc (emb x) hx
      rw [← hd, har, hbr] at hpos
      have hreal : 0 ≤
          (eval (Fin.snoc (fun i : Fin 3 => x i) 0) (pderiv (3 : Fin 4) P)) ^ 2 -
          4 * c * eval (Fin.snoc (fun i : Fin 3 => x i) 0) P := by
        simpa [pow_two, Complex.mul_re] using hpos.le
      rw [quadraticBranch_ofReal (har x) (hbr x) hreal]
      exact Complex.ofReal_im _

end Submission.Obl.k4_paired_test_normalization
