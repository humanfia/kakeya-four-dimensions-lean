import Mathlib

/-!
# The stable quadratic sheet

Helpers for `Submission.k4_stable_quadratic_hidden_sheets`: complex evaluation of real
polynomials on `EuclideanSpace ℂ (Fin 3)`, the holomorphic root branch of
`a w ^ 2 + b w + c` (through `Complex.sqrt` of the discriminant when `a ≠ 0`, and `-c / b`
when `a = 0`), and the real bounds and residual-to-graph fitting on that branch.
-/

namespace Submission.Obl.k4_stable_quadratic_hidden_sheets

open MvPolynomial

theorem eval₂_ofReal (p : MvPolynomial (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    eval₂ (algebraMap ℝ ℂ) (fun j => (x j : ℂ)) p = ((eval x p : ℝ) : ℂ) := by
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval_eq']
  push_cast
  rfl

theorem differentiable_eval₂ (p : MvPolynomial (Fin 3) ℝ) :
    Differentiable ℂ (fun z : EuclideanSpace ℂ (Fin 3) => eval₂ (algebraMap ℝ ℂ) (fun j => z j) p) := by
  intro z
  have := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (A := ℝ) (B := ℂ)
    (f := fun (z : EuclideanSpace ℂ (Fin 3)) (j : Fin 3) => z j) (z := z)
    (fun i => (EuclideanSpace.proj i : EuclideanSpace ℂ (Fin 3) →L[ℂ] ℂ).analyticAt z) p
  simpa [MvPolynomial.aeval_def] using this.differentiableAt

theorem coord_lt_of_mem_ball (u₀ : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (z : EuclideanSpace ℂ (Fin 3))
    (hz : z ∈ Metric.ball (WithLp.toLp 2 (fun j => (u₀ j : ℂ))) r) (i : Fin 3) :
    ‖z i - (u₀ i : ℂ)‖ < r := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have := PiLp.norm_apply_le (z - WithLp.toLp 2 (fun j => (u₀ j : ℂ))) i
  simp at this
  linarith

theorem coord_lt_of_norm_sub_lt (u₀ u : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (hu : ‖u - u₀‖ < r)
    (i : Fin 3) : ‖(u i : ℂ) - (u₀ i : ℂ)‖ < r := by
  have := PiLp.norm_apply_le (u - u₀) i
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simp at this
  linarith

/-- The discriminant identity for the complex evaluation. -/
theorem eval₂_disc (a : ℝ) (b c : MvPolynomial (Fin 3) ℝ) (y : Fin 3 → ℂ) :
    eval₂ (algebraMap ℝ ℂ) y (b * b - C (4 * a) * c) =
      eval₂ (algebraMap ℝ ℂ) y b * eval₂ (algebraMap ℝ ℂ) y b
        - 4 * (a : ℂ) * eval₂ (algebraMap ℝ ℂ) y c := by
  simp [eval₂_sub, eval₂_mul, eval₂_C]

theorem eval_disc (a : ℝ) (b c : MvPolynomial (Fin 3) ℝ) (x : Fin 3 → ℝ) :
    eval x (b * b - C (4 * a) * c) = eval x b * eval x b - 4 * a * eval x c := by
  simp

theorem sqrt_sq' (x : ℂ) : (Complex.sqrt x) ^ 2 = x := by
  unfold Complex.sqrt
  exact Complex.cpow_ofNat_inv_pow x 2

/-- The stable sheet: existence of the holomorphic root branch, given that the
discriminant has positive real part on the coordinate box. -/
theorem exists_sheet (a : ℝ) (b c : MvPolynomial (Fin 3) ℝ) (u₀ : EuclideanSpace ℝ (Fin 3))
    (σ r : ℝ) (hr : 0 < r) (hσ : σ ≠ 0)
    (hσ0 : a = 0 → 0 < eval (fun j => u₀ j) b * σ)
    (hDpos : ∀ y : Fin 3 → ℂ, (∀ i, ‖y i - (u₀ i : ℂ)‖ < r) →
      0 < (eval₂ (algebraMap ℝ ℂ) y (b * b - C (4 * a) * c)).re) :
    ∃ f : EuclideanSpace ℂ (Fin 3) → ℂ,
      DifferentiableOn ℂ f (Metric.ball (WithLp.toLp 2 (fun j => (u₀ j : ℂ))) r) ∧
      (∀ z ∈ Metric.ball (WithLp.toLp 2 (fun j => (u₀ j : ℂ))) r,
        (a : ℂ) * (f z) ^ 2 + eval₂ (algebraMap ℝ ℂ) (fun j => z j) b * f z
          + eval₂ (algebraMap ℝ ℂ) (fun j => z j) c = 0) ∧
      (∀ u : EuclideanSpace ℝ (Fin 3), ‖u - u₀‖ < r → ∃ φ : ℝ,
        f (WithLp.toLp 2 (fun j => (u j : ℂ))) = φ ∧
        a * φ ^ 2 + eval (fun j => u j) b * φ + eval (fun j => u j) c = 0 ∧
        0 < (2 * a * φ + eval (fun j => u j) b) * σ) := by
  -- real positivity of the discriminant on the real ball
  have hDreal : ∀ u : EuclideanSpace ℝ (Fin 3), ‖u - u₀‖ < r →
      0 < eval (fun j => u j) b * eval (fun j => u j) b - 4 * a * eval (fun j => u j) c := by
    intro u hu
    have := hDpos (fun j => (u j : ℂ)) (coord_lt_of_norm_sub_lt u₀ u r hu)
    rw [eval₂_ofReal, Complex.ofReal_re, eval_disc] at this
    exact this
  by_cases ha : a = 0
  · -- linear case: f = -c / b
    subst ha
    have hσ0 := hσ0 rfl
    refine ⟨fun z => -(eval₂ (algebraMap ℝ ℂ) (fun j => z j) c) /
      eval₂ (algebraMap ℝ ℂ) (fun j => z j) b, ?_, ?_, ?_⟩
    · intro z hz
      have hB : eval₂ (algebraMap ℝ ℂ) (fun j => z j) b ≠ 0 := by
        intro h0
        have := hDpos (fun j => z j) (coord_lt_of_mem_ball u₀ r z hz)
        rw [eval₂_disc, h0] at this
        simp at this
      have h2 : DifferentiableAt ℂ (fun z : EuclideanSpace ℂ (Fin 3) =>
          -(eval₂ (algebraMap ℝ ℂ) (fun j => z j) c) * (eval₂ (algebraMap ℝ ℂ) (fun j => z j) b)⁻¹) z :=
        ((differentiable_eval₂ c z).fun_neg).fun_mul ((differentiable_eval₂ b z).fun_inv hB)
      simpa only [div_eq_mul_inv] using h2.differentiableWithinAt
    · intro z hz
      have hB : eval₂ (algebraMap ℝ ℂ) (fun j => z j) b ≠ 0 := by
        intro h0
        have := hDpos (fun j => z j) (coord_lt_of_mem_ball u₀ r z hz)
        rw [eval₂_disc, h0] at this
        simp at this
      field_simp
      push_cast
      ring
    · intro u hu
      have hbne : ∀ v : EuclideanSpace ℝ (Fin 3), ‖v - u₀‖ < r → eval (fun j => v j) b ≠ 0 := by
        intro v hv h0
        have := hDreal v hv
        rw [h0] at this
        simp at this
      refine ⟨-(eval (fun j => u j) c) / eval (fun j => u j) b, ?_, ?_, ?_⟩
      · simp only
        rw [eval₂_ofReal, eval₂_ofReal]
        push_cast
        rfl
      · field_simp [hbne u hu]
        ring
      · -- sign via the intermediate value theorem on the ball
        have hconn : IsPreconnected (Metric.ball u₀ r) := (convex_ball u₀ r).isPreconnected
        have hcont : ContinuousOn (fun v : EuclideanSpace ℝ (Fin 3) => eval (fun j => v j) b)
            (Metric.ball u₀ r) :=
          ((MvPolynomial.continuous_eval b).comp (PiLp.continuous_ofLp 2 _)).continuousOn
        have hu' : u ∈ Metric.ball u₀ r := by rwa [Metric.mem_ball, dist_eq_norm]
        have hu₀' : u₀ ∈ Metric.ball u₀ r := Metric.mem_ball_self hr
        have hprod : 0 < eval (fun j => u j) b * eval (fun j => u₀ j) b := by
          by_contra hneg
          push Not at hneg
          rcases lt_or_gt_of_ne (hbne u₀ (by simpa using hr)) with h0 | h0
          · have hmem : (0:ℝ) ∈ Set.Icc (eval (fun j => u₀ j) b) (eval (fun j => u j) b) :=
              ⟨h0.le, by nlinarith⟩
            obtain ⟨v, hv, hv0⟩ := hconn.intermediate_value hu₀' hu' hcont hmem
            exact hbne v (by rwa [Metric.mem_ball, dist_eq_norm] at hv) hv0
          · have hmem : (0:ℝ) ∈ Set.Icc (eval (fun j => u j) b) (eval (fun j => u₀ j) b) :=
              ⟨by nlinarith, h0.le⟩
            obtain ⟨v, hv, hv0⟩ := hconn.intermediate_value hu' hu₀' hcont hmem
            exact hbne v (by rwa [Metric.mem_ball, dist_eq_norm] at hv) hv0
        have hb0 : 0 < eval (fun j => u₀ j) b ^ 2 := by
          have := hbne u₀ (by simpa using hr)
          positivity
        have : 0 < (eval (fun j => u j) b * σ) * eval (fun j => u₀ j) b ^ 2 := by
          nlinarith
        have h2 := pos_of_mul_pos_left this hb0.le
        simpa using h2
  · -- quadratic case: f = (-b + s √D) / (2a)
    obtain ⟨s, hs2, hsσ⟩ : ∃ s : ℝ, s ^ 2 = 1 ∧ 0 < s * σ := by
      rcases lt_or_gt_of_ne hσ with h | h
      · exact ⟨-1, by norm_num, by linarith⟩
      · exact ⟨1, by norm_num, by linarith⟩
    set D := b * b - C (4 * a) * c with hD
    refine ⟨fun z => (-(eval₂ (algebraMap ℝ ℂ) (fun j => z j) b) +
      (s : ℂ) * Complex.sqrt (eval₂ (algebraMap ℝ ℂ) (fun j => z j) D)) / (2 * (a : ℂ)),
      ?_, ?_, ?_⟩
    · intro z hz
      have hslit : eval₂ (algebraMap ℝ ℂ) (fun j => z j) D ∈ Complex.slitPlane :=
        Complex.mem_slitPlane_iff.2 (Or.inl (hDpos (fun j => z j) (coord_lt_of_mem_ball u₀ r z hz)))
      have h1 : DifferentiableAt ℂ
          (fun z : EuclideanSpace ℂ (Fin 3) => Complex.sqrt (eval₂ (algebraMap ℝ ℂ) (fun j => z j) D)) z :=
        DifferentiableAt.comp (g := Complex.sqrt) z (Complex.differentiableAt_sqrt hslit)
          (differentiable_eval₂ D z)
      have h2 : DifferentiableAt ℂ (fun z : EuclideanSpace ℂ (Fin 3) =>
          (-(eval₂ (algebraMap ℝ ℂ) (fun j => z j) b) +
            (s : ℂ) * Complex.sqrt (eval₂ (algebraMap ℝ ℂ) (fun j => z j) D)) * (2 * (a : ℂ))⁻¹) z :=
        (((differentiable_eval₂ b z).fun_neg).fun_add (h1.const_mul _)).mul_const _
      simpa only [div_eq_mul_inv] using h2.differentiableWithinAt
    · intro z hz
      have hsq := sqrt_sq' (eval₂ (algebraMap ℝ ℂ) (fun j => z j) D)
      have hDeq := eval₂_disc a b c (fun j => z j)
      rw [← hD] at hDeq
      have ha' : (a : ℂ) ≠ 0 := by exact_mod_cast ha
      have hs2' : (s : ℂ) ^ 2 = 1 := by exact_mod_cast hs2
      set B := eval₂ (algebraMap ℝ ℂ) (fun j => z j) b
      set Cc := eval₂ (algebraMap ℝ ℂ) (fun j => z j) c
      set S := Complex.sqrt (eval₂ (algebraMap ℝ ℂ) (fun j => z j) D)
      set F := (-B + (s : ℂ) * S) / (2 * (a : ℂ)) with hF
      have hf : 2 * (a : ℂ) * F = -B + (s : ℂ) * S := by rw [hF]; field_simp
      have h4 : (4 * (a : ℂ)) * ((a : ℂ) * F ^ 2 + B * F + Cc) = 0 := by
        linear_combination (2 * (a : ℂ) * F + B + (s : ℂ) * S) * hf + (s : ℂ) ^ 2 * hsq
          + (s : ℂ) ^ 2 * hDeq + (B * B - 4 * (a : ℂ) * Cc) * hs2'
      rcases mul_eq_zero.1 h4 with h | h
      · exact absurd h (mul_ne_zero (by norm_num) ha')
      · exact h
    · intro u hu
      have hDu := hDreal u hu
      refine ⟨(-(eval (fun j => u j) b) + s * Real.sqrt (eval (fun j => u j) D)) / (2 * a), ?_, ?_, ?_⟩
      · simp only
        rw [eval₂_ofReal, eval₂_ofReal, Complex.sqrt_of_nonneg]
        · push_cast
          rfl
        · rw [Complex.zero_le_real, hD, eval_disc]; exact hDu.le
      · have hsq : Real.sqrt (eval (fun j => u j) D) ^ 2 = eval (fun j => u j) D :=
          Real.sq_sqrt (by rw [hD, eval_disc]; exact hDu.le)
        have hDeq := eval_disc a b c (fun j => u j)
        rw [← hD] at hDeq
        set B := eval (fun j => u j) b
        set Cc := eval (fun j => u j) c
        set S := Real.sqrt (eval (fun j => u j) D)
        set F := (-B + s * S) / (2 * a) with hF
        have hf : 2 * a * F = -B + s * S := by rw [hF]; field_simp
        have h4 : (4 * a) * (a * F ^ 2 + B * F + Cc) = 0 := by
          linear_combination (2 * a * F + B + s * S) * hf + s ^ 2 * hsq + s ^ 2 * hDeq
            + (B * B - 4 * a * Cc) * hs2
        rcases mul_eq_zero.1 h4 with h | h
        · exact absurd h (mul_ne_zero (by norm_num) ha)
        · exact h
      · have hsqpos : 0 < Real.sqrt (eval (fun j => u j) D) :=
          Real.sqrt_pos.2 (by rw [hD, eval_disc]; exact hDu)
        have : 2 * a * ((-(eval (fun j => u j) b) + s * Real.sqrt (eval (fun j => u j) D)) / (2 * a))
            + eval (fun j => u j) b = s * Real.sqrt (eval (fun j => u j) D) := by
          field_simp; ring
        rw [this]
        nlinarith

theorem coord_le_of_norm_le (u₀ : EuclideanSpace ℝ (Fin 3)) (A : ℝ) (hu : ‖u₀‖ ≤ A) (i : Fin 3) :
    ‖(u₀ i : ℂ)‖ ≤ A := by
  have := PiLp.norm_apply_le u₀ i
  rw [Complex.norm_real]
  linarith

theorem real_branch_bounds (A a_fit a bu cu φ σ : ℝ) (hA : 2 ≤ A) (ha_fit : 0 < a_fit)
    (hroot : a * φ ^ 2 + bu * φ + cu = 0) (hsign : 0 < (2 * a * φ + bu) * σ)
    (hlo : 1 / (2 * A ^ 2) ≤ bu * bu - 4 * a * cu) (hhi : bu * bu - 4 * a * cu ≤ A ^ 2 + 1) :
    (A ^ 20)⁻¹ ≤ |2 * a * φ + bu| ∧ |2 * a * φ + bu| ≤ A ^ 20 ∧
    ∀ w : ℝ, |a * w ^ 2 + bu * w + cu| ≤ a_fit * A → 0 < (2 * a * w + bu) * σ →
      |w - φ| ≤ a_fit * A ^ 20 := by
  set q := 2 * a * φ + bu with hq
  have hA0 : 0 < A := by linarith
  have hq2 : q ^ 2 = bu * bu - 4 * a * cu := by rw [hq]; linear_combination 4 * a * hroot
  have hA19 : 2 ≤ A ^ 19 := by
    calc (2:ℝ) ≤ 2 ^ 19 := by norm_num
      _ ≤ A ^ 19 := pow_le_pow_left₀ (by norm_num) hA 19
  have hA20 : A ^ 20 = A * A ^ 19 := by ring
  have hA18 : 4 ≤ A ^ 18 := by
    calc (4:ℝ) ≤ 2 ^ 18 := by norm_num
      _ ≤ A ^ 18 := pow_le_pow_left₀ (by norm_num) hA 18
  -- |q| ≥ 1/(2A)
  have hqlo : 1 / (2 * A) ≤ |q| := by
    have h1 : (1 / (2 * A)) ^ 2 ≤ |q| ^ 2 := by
      rw [sq_abs, hq2]
      refine le_trans ?_ hlo
      rw [div_pow, one_pow, mul_pow]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
    exact (sq_le_sq₀ (by positivity) (abs_nonneg _)).1 h1
  have hqhi : |q| ≤ A + 1 := by
    have h1 : |q| ^ 2 ≤ (A + 1) ^ 2 := by
      rw [sq_abs, hq2]; nlinarith
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).1 h1
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ hqlo
    rw [one_div]
    apply inv_anti₀ (by positivity)
    rw [hA20]; nlinarith
  · refine le_trans hqhi ?_
    rw [hA20]; nlinarith
  · intro w hw hpw
    set p := 2 * a * w + bu with hp
    have hfac : a * w ^ 2 + bu * w + cu = (w - φ) * ((p + q) / 2) := by
      rw [hp, hq]; linear_combination hroot
    have hpq : |q| ≤ |p + q| := by
      rcases lt_or_gt_of_ne (show σ ≠ 0 by rintro rfl; simp at hsign) with hs | hs
      · have hq0 : q < 0 := by nlinarith
        have hp0 : p < 0 := by nlinarith
        rw [abs_of_neg hq0, abs_of_neg (by linarith)]; linarith
      · have hq0 : 0 < q := by nlinarith
        have hp0 : 0 < p := by nlinarith
        rw [abs_of_pos hq0, abs_of_pos (by linarith)]; linarith
    have h1 : |w - φ| * |q| ≤ 2 * (a_fit * A) := by
      calc |w - φ| * |q| ≤ |w - φ| * |p + q| := mul_le_mul_of_nonneg_left hpq (abs_nonneg _)
        _ = 2 * |a * w ^ 2 + bu * w + cu| := by
          rw [hfac, abs_mul, abs_div, abs_two]; ring
        _ ≤ 2 * (a_fit * A) := by linarith
    have h2 : 1 ≤ |q| * (2 * A) := by
      have := mul_le_mul_of_nonneg_right hqlo (show 0 ≤ 2 * A by positivity)
      rwa [one_div, inv_mul_cancel₀ (by positivity)] at this
    have hwφ : 0 ≤ |w - φ| := abs_nonneg _
    calc |w - φ| ≤ |w - φ| * (|q| * (2 * A)) := le_mul_of_one_le_right hwφ h2
      _ = (|w - φ| * |q|) * (2 * A) := by ring
      _ ≤ (2 * (a_fit * A)) * (2 * A) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = a_fit * (4 * A ^ 2) := by ring
      _ ≤ a_fit * A ^ 20 := by
        apply mul_le_mul_of_nonneg_left _ ha_fit.le
        have : A ^ 20 = A ^ 2 * A ^ 18 := by ring
        rw [this]; nlinarith

end Submission.Obl.k4_stable_quadratic_hidden_sheets
