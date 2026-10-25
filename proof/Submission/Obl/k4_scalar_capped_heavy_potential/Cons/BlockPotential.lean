import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.Geometry
import Submission.Obl.k4_scalar_capped_heavy_potential.Cons.CellCurl
import Submission.Obl.k4_scalar_capped_heavy_potential.Core.CoefficientBounds
import Submission.Lib.K4PolynomialPotential

/-!
# The potential on one block

If the curl of the rescaled field `lam T(lam ·)` has small coefficients, the
polynomial potential of the rescaled field, scaled back to normalized base
coordinates and multiplied by `h`, is an approximate primitive of `X` along
every trajectory obeying the field relation throughout the block: the residual
`X_l(t) - P(u_l(t))` varies by at most `h (εT + (D+1)² E / lam)` on the block.
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MeasureTheory MvPolynomial
open Submission.Lib.K4PolynomialPotential

/-- `h P(u / lam)` as a polynomial in `u`. -/
noncomputable def unscalePotential (h lam : ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    MvPolynomial (Fin 2) ℝ :=
  C h * aeval (fun i => C lam⁻¹ * X i) P

theorem eval_unscalePotential (h lam : ℝ) (P : MvPolynomial (Fin 2) ℝ) (u : Fin 2 → ℝ) :
    eval u (unscalePotential h lam P) = h * eval (fun i => u i / lam) P := by
  rw [unscalePotential, map_mul, eval_C,
    Submission.Lib.K4ScalarSwitching.Switching.eval_substitution]
  congr 1
  apply congrArg (fun f : Fin 2 → ℝ => eval f P)
  funext i
  simp only [map_mul, eval_C, eval_X]
  ring

theorem unscalePotential_degree (h lam : ℝ) (P : MvPolynomial (Fin 2) ℝ) {D : ℕ}
    (hP : P.totalDegree ≤ D) : (unscalePotential h lam P).totalDegree ≤ D := by
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (Submission.Lib.K4ScalarSwitching.PolynomialDegree.degree_aeval_le P _ ?_).trans hP
  intro i
  apply (totalDegree_mul _ _).trans
  simp [totalDegree_C, totalDegree_X]

/-- **Block potential.** -/
theorem exists_block_potential_constant (D : ℕ) :
    ∃ Cc : ℝ, 0 < Cc ∧ ∀ (𝒯 : Fin 2 → MvPolynomial (Fin 2) ℝ) (z₀ : Fin 2 → ℝ)
      (t₀ h lam H εT Bc K : ℝ),
      (∀ i, (𝒯 i).totalDegree ≤ D) → (∀ i b, |(𝒯 i).coeff b| ≤ H) →
      0 < h → 1 ≤ lam → 0 ≤ H → 2 * H ≤ lam → 0 ≤ εT → 0 ≤ Bc →
      lam ^ (D + 1) * (((D + 1) ^ 2 : ℕ) * H) ≤ K →
      (∀ e : Fin 2 →₀ ℕ, |(pderiv 0 (scaleField lam (𝒯 1)) -
        pderiv 1 (scaleField lam (𝒯 0))).coeff e| ≤ Bc) →
      ∃ P : MvPolynomial (Fin 2) ℝ, P.totalDegree ≤ D + 2 ∧
        (∀ b, |P.coeff b| ≤ Cc ^ 2 * (h * (2 * K))) ∧
        (∀ u : Fin 2 → ℝ, (∀ i, |u i| ≤ lam) → |eval u P| ≤ h * (2 * K)) ∧
        ∀ l : ℕ × (Fin 5 → ℝ),
          (∀ t ∈ Icc t₀ (t₀ + h), ∀ i, |ubase z₀ h l t i| ≤ H) →
          (∀ t ∈ Icc t₀ (t₀ + h), |l.2 3 + 2 * t * l.2 4 -
            ∑ i : Fin 2, eval (ubase z₀ h l t) (𝒯 i) * (![1, l.2 1] : Fin 2 → ℝ) i| ≤ εT) →
          ∀ t ∈ Icc t₀ (t₀ + h),
            |(xL l t - eval (ubase z₀ h l t) P) - (xL l t₀ - eval (ubase z₀ h l t₀) P)| ≤
              h * (εT + (((D + 1) ^ 2 : ℕ) * Bc) / lam) := by
  obtain ⟨Cc, hCc, hcoef⟩ :=
    Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching.exists_multivariate_coefficient_constant
      (D + 2)
  refine ⟨Cc, hCc, ?_⟩
  intro 𝒯 z₀ t₀ h lam H εT Bc K h𝒯deg h𝒯coeff hh hlam1 hH hlamH hεT hBc hK hcurlc
  have hlam : 0 < lam := by linarith
  set At := scaleField lam (𝒯 0) with hAtdef
  set Bt := scaleField lam (𝒯 1) with hBtdef
  have hAtdeg : At.totalDegree ≤ D := scaleField_degree lam _ (h𝒯deg 0)
  have hBtdeg : Bt.totalDegree ≤ D := scaleField_degree lam _ (h𝒯deg 1)
  set Pt := polynomialPotential At Bt with hPtdef
  have hPtdeg : Pt.totalDegree ≤ D + 2 := polynomialPotential_totalDegree At Bt hAtdeg hBtdeg
  -- the curl is small on the unit box
  have hcurldeg : (pderiv 0 Bt - pderiv 1 At).totalDegree ≤ D := by
    apply (MvPolynomial.totalDegree_sub _ _).trans
    exact max_le ((totalDegree_pderiv_le Bt 0).trans ((Nat.sub_le _ _).trans hBtdeg))
      ((totalDegree_pderiv_le At 1).trans ((Nat.sub_le _ _).trans hAtdeg))
  have hcurl : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1,
      |eval z (pderiv 0 Bt - pderiv 1 At)| ≤ ((D + 1) ^ 2 : ℕ) * Bc := by
    intro z hz
    exact (Submission.Obl.k4_scalar_capped_heavy_potential.Core.Switching.eval_le_coefficientMass_on_unit
      _ z hz).trans
      (Submission.Obl.k4_scalar_capped_heavy_potential.Core.CoefficientMass.coefficientMass_le_of_coeff_bound
        _ hcurldeg hBc hcurlc)
  -- the rescaled field is bounded on the unit box
  have hAt : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z At| ≤ K :=
    fun z hz => (scaleField_eval_le hlam1 _ (h𝒯deg 0) hH (h𝒯coeff 0) z hz).trans hK
  have hBt : ∀ z ∈ Icc (-1 : Fin 2 → ℝ) 1, |eval z Bt| ≤ K :=
    fun z hz => (scaleField_eval_le hlam1 _ (h𝒯deg 1) hH (h𝒯coeff 1) z hz).trans hK
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hAt 0 ⟨fun _ => by simp, fun _ => by simp⟩)
  refine ⟨unscalePotential h lam Pt, unscalePotential_degree h lam Pt hPtdeg, ?_, ?_, ?_⟩
  · -- coefficients from the sup bound on the unit square
    apply hcoef 2 _ (unscalePotential_degree h lam Pt hPtdeg) (h * (2 * K)) (by positivity)
    intro u hu
    rw [eval_unscalePotential, abs_mul, abs_of_pos hh]
    apply mul_le_mul_of_nonneg_left _ hh.le
    apply polynomialPotential_eval_bound At Bt hK0 hAt hBt
    constructor <;> intro i
    · have := hu.1 i
      simp only [Pi.zero_apply] at this
      simp only [Pi.neg_apply, Pi.one_apply]
      have : 0 ≤ u i / lam := div_nonneg this hlam.le
      linarith
    · have := hu.2 i
      simp only [Pi.one_apply] at this ⊢
      rw [div_le_one hlam]
      linarith
  · intro u hu
    rw [eval_unscalePotential, abs_mul, abs_of_pos hh]
    apply mul_le_mul_of_nonneg_left _ hh.le
    apply polynomialPotential_eval_bound At Bt hK0 hAt hBt
    constructor <;> intro i
    · have := (abs_le.mp (hu i)).1
      simp only [Pi.neg_apply, Pi.one_apply]
      rw [le_div_iff₀ hlam]
      linarith
    · have := (abs_le.mp (hu i)).2
      simp only [Pi.one_apply]
      rw [div_le_iff₀ hlam]
      linarith
  · intro l hu hfield t ht
    -- the rescaled trajectory is the line `s ↦ (s, u' + s V)`
    set V := l.2 1 with hVdef
    set u' := (l.2 0 + z₀ 0 * l.2 1 - z₀ 1) / (h * lam) with hu'def
    set a := (t₀ - z₀ 0) / (h * lam) with hadef
    set q := 1 / lam with hqdef
    set S := legHeight l (z₀ 0) (h * lam) h with hSdef
    have hhlam : 0 < h * lam := mul_pos hh hlam
    -- conversion between physical time and the rescaled parameter
    have hconv (τ : ℝ) : (fun i => ubase z₀ h l τ i / lam) =
        (![(τ - z₀ 0) / (h * lam), u' + (τ - z₀ 0) / (h * lam) * V] : Fin 2 → ℝ) := by
      funext i
      fin_cases i
      · simp only [ubase, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
        field_simp
      · simp only [ubase, yL, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
          hu'def, hVdef]
        field_simp
        ring
    have htime (τ : ℝ) : z₀ 0 + h * lam * ((τ - z₀ 0) / (h * lam)) = τ := by
      field_simp
      ring
    have hsI : ∀ s ∈ Icc a (a + q), z₀ 0 + h * lam * s ∈ Icc t₀ (t₀ + h) := by
      intro s hs
      have h1 := hs.1
      have h2 := hs.2
      simp only [hadef, hqdef] at h1 h2
      constructor
      · have := mul_le_mul_of_nonneg_left h1 hhlam.le
        rw [mul_div_cancel₀ _ hhlam.ne'] at this
        linarith
      · have := mul_le_mul_of_nonneg_left h2 hhlam.le
        rw [mul_add, mul_div_cancel₀ _ hhlam.ne'] at this
        have hq' : h * lam * (1 / lam) = h := by field_simp
        linarith
    have htraj : ∀ s ∈ Icc a (a + q), (![s, u' + s * V] : Fin 2 → ℝ) ∈ Icc (-1) 1 := by
      intro s hs
      have hτ := hsI s hs
      have hc := hconv (z₀ 0 + h * lam * s)
      have hs' : (z₀ 0 + h * lam * s - z₀ 0) / (h * lam) = s := by field_simp; ring
      rw [hs'] at hc
      rw [← hc]
      have hb := hu _ hτ
      constructor <;> intro i
      · have := (abs_le.mp (hb i)).1
        simp only [Pi.neg_apply, Pi.one_apply]
        rw [le_div_iff₀ hlam]
        nlinarith
      · have := (abs_le.mp (hb i)).2
        simp only [Pi.one_apply]
        rw [div_le_iff₀ hlam]
        nlinarith
    have hrow : ∀ s ∈ Icc a (a + q),
        |S.derivative.eval s - (eval ![s, u' + s * V] At + V * eval ![s, u' + s * V] Bt)| ≤
          lam * εT := by
      intro s hs
      have hτ := hsI s hs
      have hc := hconv (z₀ 0 + h * lam * s)
      have hs' : (z₀ 0 + h * lam * s - z₀ 0) / (h * lam) = s := by field_simp; ring
      rw [hs'] at hc
      rw [← hc, hSdef, legHeight_derivative_eval, hAtdef, hBtdef, eval_scaleField, eval_scaleField]
      have hsc : (fun i => lam * (ubase z₀ h l (z₀ 0 + h * lam * s) i / lam)) =
          ubase z₀ h l (z₀ 0 + h * lam * s) := by funext i; field_simp
      rw [hsc]
      have hf := hfield _ hτ
      rw [Fin.sum_univ_two] at hf
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_one] at hf
      have hid : h * lam * (l.2 3 + 2 * (z₀ 0 + h * lam * s) * l.2 4) / h -
          (lam * eval (ubase z₀ h l (z₀ 0 + h * lam * s)) (𝒯 0) +
            V * (lam * eval (ubase z₀ h l (z₀ 0 + h * lam * s)) (𝒯 1))) =
          lam * (l.2 3 + 2 * (z₀ 0 + h * lam * s) * l.2 4 -
            (eval (ubase z₀ h l (z₀ 0 + h * lam * s)) (𝒯 0) +
              eval (ubase z₀ h l (z₀ 0 + h * lam * s)) (𝒯 1) * l.2 1)) := by
        rw [hVdef]
        field_simp
      rw [hid, abs_mul, abs_of_pos hlam]
      exact mul_le_mul_of_nonneg_left hf hlam.le
    have hfit := scalar_potential_fit_on_block At Bt S u' V a q (lam * εT)
      (((D + 1) ^ 2 : ℕ) * Bc) (by positivity) (by positivity) (by positivity) hcurl htraj hrow
    -- apply at the rescaled time of `t`
    set s := (t - z₀ 0) / (h * lam) with hsdef
    have hsmem : s ∈ Icc a (a + q) := by
      constructor
      · simp only [hsdef, hadef]
        exact div_le_div_of_nonneg_right (by linarith [ht.1]) hhlam.le
      · simp only [hsdef, hadef, hqdef]
        rw [show (t₀ - z₀ 0) / (h * lam) + 1 / lam = (t₀ + h - z₀ 0) / (h * lam) by
          field_simp; ring]
        exact div_le_div_of_nonneg_right (by linarith [ht.2]) hhlam.le
    have h1 := hfit s hsmem
    rw [hSdef, legHeight_eval, legHeight_eval, htime t, hadef, htime t₀] at h1
    rw [← hconv t, ← hconv t₀] at h1
    rw [eval_unscalePotential, eval_unscalePotential]
    have hid : xL l t - h * eval (fun i => ubase z₀ h l t i / lam) Pt -
        (xL l t₀ - h * eval (fun i => ubase z₀ h l t₀ i / lam) Pt) =
        h * (xL l t / h - eval (fun i => ubase z₀ h l t i / lam) Pt -
          (xL l t₀ / h - eval (fun i => ubase z₀ h l t₀ i / lam) Pt)) := by
      field_simp
    rw [hid, abs_mul, abs_of_pos hh]
    apply mul_le_mul_of_nonneg_left _ hh.le
    refine h1.trans (le_of_eq ?_)
    rw [hqdef]
    field_simp

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
