import Submission.Obl.k4_scalar_capped_heavy_potential.Core.ConservativePotential
import Submission.Lib.K4ScalarSwitching.SwitchPath
import Submission.Lib.K4ScalarSwitching.PolynomialDegree

/-!
# Trajectory geometry for the conservativity step

Trajectories `l = (tag, l₀, …, l₄)` have base `y_l(t) = l₀ + t l₁` and hidden
coordinate `X_l(t) = l₂ + t l₃ + t² l₄`. Normalized base coordinates are
`u_l(t) = ((t, y_l(t)) - z₀)/h`. This file records the affine identities, the
shared-state switching relation, the rescaled polynomial field, and the
hidden coordinate along a leg as a polynomial in the leg parameter.
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MeasureTheory MvPolynomial

/-- The base coordinate of a trajectory. -/
def yL (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) : ℝ := l.2 0 + t * l.2 1

/-- The hidden coordinate of a trajectory. -/
def xL (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) : ℝ := l.2 2 + t * l.2 3 + t ^ 2 * l.2 4

/-- Normalized base coordinates of a trajectory at time `t`. -/
noncomputable def ubase (z₀ : Fin 2 → ℝ) (h : ℝ) (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) : Fin 2 → ℝ :=
  fun e => ((![t, yL l t] : Fin 2 → ℝ) e - z₀ e) / h

theorem ubase_zero (z₀ : Fin 2 → ℝ) (h : ℝ) (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) :
    ubase z₀ h l t 0 = (t - z₀ 0) / h := by
  simp [ubase]

theorem ubase_one (z₀ : Fin 2 → ℝ) (h : ℝ) (l : ℕ × (Fin 5 → ℝ)) (t : ℝ) :
    ubase z₀ h l t 1 = (yL l t - z₀ 1) / h := by
  simp [ubase]

/-- Normalized base coordinates move affinely in time, along `(1, l₁)`. -/
theorem ubase_affine {z₀ : Fin 2 → ℝ} {h : ℝ} (hh : h ≠ 0) (l : ℕ × (Fin 5 → ℝ)) (t t' : ℝ)
    (d : Fin 2) :
    ubase z₀ h l t' d = ubase z₀ h l t d + ((![1, l.2 1] : Fin 2 → ℝ) d) * ((t' - t) / h) := by
  fin_cases d
  · simp only [ubase, yL, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    field_simp
    ring
  · simp only [ubase, yL, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    field_simp
    ring

theorem continuous_ubase (z₀ : Fin 2 → ℝ) (h : ℝ) :
    Continuous (fun p : (ℕ × (Fin 5 → ℝ)) × ℝ => ubase z₀ h p.1 p.2) := by
  apply continuous_pi
  intro e
  fin_cases e
  · simp only [ubase, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
    fun_prop
  · simp only [ubase, yL, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
    fun_prop

theorem continuous_xL : Continuous (fun p : (ℕ × (Fin 5 → ℝ)) × ℝ => xL p.1 p.2) := by
  unfold xL
  fun_prop

theorem continuous_yL : Continuous (fun p : (ℕ × (Fin 5 → ℝ)) × ℝ => yL p.1 p.2) := by
  unfold yL
  fun_prop

/-! ### The shared-state switching relation -/

/-- Physical floor state `(t, y, X)` of an incidence at width `δs`. -/
noncomputable def physState (δs : ℝ) (p : (ℕ × (Fin 5 → ℝ)) × ℝ) : Fin 3 → ℤ :=
  fun e => ⌊(![p.2, yL p.1 p.2, xL p.1 p.2] : Fin 3 → ℝ) e / δs⌋

theorem measurable_physState (δs : ℝ) : Measurable (physState δs) := by
  apply measurable_pi_iff.mpr
  intro e
  apply Int.measurable_floor.comp
  apply Measurable.div_const
  fin_cases e
  · simpa using measurable_snd
  · simpa using continuous_yL.measurable
  · simpa using continuous_xL.measurable

/-- What a shared state certifies about the new line at the old time. -/
def switchRel (H δs : ℝ) (ω : (ℕ × (Fin 5 → ℝ)) × ℝ) (l' : ℕ × (Fin 5 → ℝ)) : Prop :=
  (∀ i, |l'.2 i| ≤ H) → |ω.2| ≤ 1 →
    |yL l' ω.2 - yL ω.1 ω.2| ≤ (H + 1) * δs ∧ |xL l' ω.2 - xL ω.1 ω.2| ≤ (4 * H + 1) * δs

theorem measurableSet_switchRel (H δs : ℝ) :
    MeasurableSet {z : ((ℕ × (Fin 5 → ℝ)) × ℝ) × (ℕ × (Fin 5 → ℝ)) | switchRel H δs z.1 z.2} := by
  have hset : {z : ((ℕ × (Fin 5 → ℝ)) × ℝ) × (ℕ × (Fin 5 → ℝ)) | switchRel H δs z.1 z.2} =
      ({z | ∀ i, |z.2.2 i| ≤ H} ∩ {z | |z.1.2| ≤ 1})ᶜ ∪
        ({z | |yL z.2 z.1.2 - yL z.1.1 z.1.2| ≤ (H + 1) * δs} ∩
          {z | |xL z.2 z.1.2 - xL z.1.1 z.1.2| ≤ (4 * H + 1) * δs}) := by
    ext z
    simp only [switchRel, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    tauto
  rw [hset]
  apply MeasurableSet.union
  · apply MeasurableSet.compl
    apply MeasurableSet.inter
    · have : {z : ((ℕ × (Fin 5 → ℝ)) × ℝ) × (ℕ × (Fin 5 → ℝ)) | ∀ i, |z.2.2 i| ≤ H} =
          ⋂ i, {z | |z.2.2 i| ≤ H} := by ext; simp
      rw [this]
      exact MeasurableSet.iInter fun i =>
        measurableSet_le (by fun_prop) measurable_const
    · exact measurableSet_le (by fun_prop) measurable_const
  · apply MeasurableSet.inter
    · exact measurableSet_le (by unfold yL; fun_prop) measurable_const
    · exact measurableSet_le (by unfold xL; fun_prop) measurable_const

theorem abs_sub_lt_of_floor_eq {a b δ : ℝ} (hδ : 0 < δ) (h : ⌊a / δ⌋ = ⌊b / δ⌋) :
    |a - b| < δ := by
  have h1 := (Int.abs_sub_lt_one_of_floor_eq_floor h)
  have hid : a / δ - b / δ = (a - b) / δ := by ring
  rw [hid, abs_div, abs_of_pos hδ, div_lt_one hδ] at h1
  exact h1

/-- A shared physical state certifies the switching relation. -/
theorem switchRel_of_state {H δs : ℝ} (hH : 0 ≤ H) (hδs : 0 < δs) (hδs1 : δs ≤ 1)
    (ω z : (ℕ × (Fin 5 → ℝ)) × ℝ) (hst : physState δs z = physState δs ω) :
    switchRel H δs ω z.1 := by
  intro hbd hω
  have h0 : ⌊z.2 / δs⌋ = ⌊ω.2 / δs⌋ := by simpa [physState] using congrFun hst 0
  have h1 : ⌊yL z.1 z.2 / δs⌋ = ⌊yL ω.1 ω.2 / δs⌋ := by simpa [physState] using congrFun hst 1
  have h2 : ⌊xL z.1 z.2 / δs⌋ = ⌊xL ω.1 ω.2 / δs⌋ := by simpa [physState] using congrFun hst 2
  have ht := abs_sub_lt_of_floor_eq hδs h0
  have hy := abs_sub_lt_of_floor_eq hδs h1
  have hx := abs_sub_lt_of_floor_eq hδs h2
  have hz2 : |z.2| ≤ 2 := by
    have := abs_sub_abs_le_abs_sub z.2 ω.2
    linarith
  have hb1 := hbd 1
  have hb3 := hbd 3
  have hb4 := hbd 4
  constructor
  · have hid : yL z.1 ω.2 - yL ω.1 ω.2 = (yL z.1 z.2 - yL ω.1 ω.2) + z.1.2 1 * (ω.2 - z.2) := by
      simp only [yL]; ring
    rw [hid]
    have hm : |z.1.2 1 * (ω.2 - z.2)| ≤ H * δs := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul hb1 ht.le (abs_nonneg _) hH
    calc
      _ ≤ |yL z.1 z.2 - yL ω.1 ω.2| + |z.1.2 1 * (ω.2 - z.2)| := abs_add_le _ _
      _ ≤ δs + H * δs := add_le_add hy.le hm
      _ = (H + 1) * δs := by ring
  · have hid : xL z.1 ω.2 - xL ω.1 ω.2 = (xL z.1 z.2 - xL ω.1 ω.2) +
        (ω.2 - z.2) * (z.1.2 3 + (ω.2 + z.2) * z.1.2 4) := by
      simp only [xL]; ring
    rw [hid]
    have hsum : |ω.2 + z.2| ≤ 3 := (abs_add_le _ _).trans (by linarith)
    have hinner : |z.1.2 3 + (ω.2 + z.2) * z.1.2 4| ≤ 4 * H := by
      calc
        _ ≤ |z.1.2 3| + |(ω.2 + z.2) * z.1.2 4| := abs_add_le _ _
        _ ≤ H + 3 * H := by
          rw [abs_mul]
          exact add_le_add hb3 (mul_le_mul hsum hb4 (abs_nonneg _) (by norm_num))
        _ = 4 * H := by ring
    have hm : |(ω.2 - z.2) * (z.1.2 3 + (ω.2 + z.2) * z.1.2 4)| ≤ δs * (4 * H) := by
      rw [abs_mul, abs_sub_comm]
      exact mul_le_mul ht.le hinner (abs_nonneg _) hδs.le
    calc
      _ ≤ |xL z.1 z.2 - xL ω.1 ω.2| + |(ω.2 - z.2) * (z.1.2 3 + (ω.2 + z.2) * z.1.2 4)| :=
        abs_add_le _ _
      _ ≤ δs + δs * (4 * H) := add_le_add hx.le hm
      _ = (4 * H + 1) * δs := by ring

/-! ### The rescaled field -/

/-- `scaleField λ P (z) = λ P(λ z)`. -/
noncomputable def scaleField (s : ℝ) (P : MvPolynomial (Fin 2) ℝ) : MvPolynomial (Fin 2) ℝ :=
  C s * aeval (fun i => C s * X i) P

theorem eval_scaleField (s : ℝ) (P : MvPolynomial (Fin 2) ℝ) (z : Fin 2 → ℝ) :
    eval z (scaleField s P) = s * eval (fun i => s * z i) P := by
  rw [scaleField, map_mul, eval_C,
    Submission.Lib.K4ScalarSwitching.Switching.eval_substitution]
  simp

theorem scaleField_degree (s : ℝ) (P : MvPolynomial (Fin 2) ℝ) {D : ℕ}
    (hP : P.totalDegree ≤ D) : (scaleField s P).totalDegree ≤ D := by
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (Submission.Lib.K4ScalarSwitching.PolynomialDegree.degree_aeval_le P _ ?_).trans hP
  intro i
  apply (totalDegree_mul _ _).trans
  simp [totalDegree_C, totalDegree_X]

/-- Evaluation on a box of radius `R ≥ 1` costs at most `R ^ D` times the
coefficient mass. -/
theorem eval_le_coefficientMass_on_box {n D : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (hP : P.totalDegree ≤ D) {R : ℝ} (hR : 1 ≤ R) (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ R) :
    |eval x P| ≤ R ^ D *
      Submission.Obl.k4_scalar_capped_heavy_potential.Core.CoefficientMass.coefficientMass P := by
  classical
  rw [MvPolynomial.eval_eq', Submission.Obl.k4_scalar_capped_heavy_potential.Core.CoefficientMass.coefficientMass,
    Finset.mul_sum]
  calc
    _ ≤ ∑ e ∈ P.support, |P.coeff e * ∏ i : Fin n, x i ^ e i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e ∈ P.support, R ^ D * |P.coeff e| := Finset.sum_le_sum fun e he => by
      rw [abs_mul, Finset.abs_prod, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      have hdeg : (e.sum fun _ k => k) ≤ D := (le_totalDegree he).trans hP
      calc
        (∏ i : Fin n, |x i ^ e i|) ≤ ∏ i : Fin n, R ^ e i := by
          refine Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) (fun i _ => ?_)
          rw [abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hx i) _
        _ = R ^ (∑ i : Fin n, e i) := Finset.prod_pow_eq_pow_sum _ _ _
        _ ≤ R ^ D := by
          apply pow_le_pow_right₀ hR
          rw [Finsupp.sum_fintype _ _ (by simp)] at hdeg
          exact hdeg

/-- Sup bound of the rescaled field on the unit box. -/
theorem scaleField_eval_le {s : ℝ} (hs : 1 ≤ s) (P : MvPolynomial (Fin 2) ℝ) {D : ℕ}
    (hP : P.totalDegree ≤ D) {H : ℝ} (hH : 0 ≤ H) (hcoeff : ∀ b, |P.coeff b| ≤ H)
    (z : Fin 2 → ℝ) (hz : z ∈ Icc (-1 : Fin 2 → ℝ) 1) :
    |eval z (scaleField s P)| ≤ s ^ (D + 1) * (((D + 1) ^ 2 : ℕ) * H) := by
  rw [eval_scaleField, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < s)]
  have hbox : ∀ i, |s * z i| ≤ s := by
    intro i
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < s)]
    have : |z i| ≤ 1 := abs_le.mpr ⟨by simpa using hz.1 i, by simpa using hz.2 i⟩
    nlinarith
  have h1 := eval_le_coefficientMass_on_box P hP hs _ hbox
  have h2 := Submission.Obl.k4_scalar_capped_heavy_potential.Core.CoefficientMass.coefficientMass_le_of_coeff_bound
    P hP hH hcoeff
  calc
    s * |eval (fun i => s * z i) P| ≤ s * (s ^ D * (((D + 1) ^ 2 : ℕ) * H)) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
    _ = s ^ (D + 1) * (((D + 1) ^ 2 : ℕ) * H) := by ring

/-! ### The hidden coordinate along a leg -/

/-- `s ↦ X_l(t + σ s) / h` as a polynomial in the leg parameter `s`. -/
noncomputable def legHeight (l : ℕ × (Fin 5 → ℝ)) (t σ h : ℝ) : Polynomial ℝ :=
  Polynomial.C h⁻¹ * (Polynomial.C (l.2 2) +
    (Polynomial.C t + Polynomial.C σ * Polynomial.X) * Polynomial.C (l.2 3) +
      (Polynomial.C t + Polynomial.C σ * Polynomial.X) ^ 2 * Polynomial.C (l.2 4))

theorem legHeight_eval (l : ℕ × (Fin 5 → ℝ)) (t σ h s : ℝ) :
    (legHeight l t σ h).eval s = xL l (t + σ * s) / h := by
  simp only [legHeight, xL, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_pow, Polynomial.eval_X]
  ring

theorem legHeight_derivative_eval (l : ℕ × (Fin 5 → ℝ)) (t σ h s : ℝ) :
    (legHeight l t σ h).derivative.eval s =
      σ * (l.2 3 + 2 * (t + σ * s) * l.2 4) / h := by
  simp [legHeight, Polynomial.derivative_pow]
  ring

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
