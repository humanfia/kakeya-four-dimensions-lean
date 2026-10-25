import Mathlib

/- Developed in this workspace by x0047 for o015 and its endpoint-volume child. -/

/-!
# The constant-control endpoint polynomial

Coordinates are ordered by increasing powers, the reverse of the usual order
of the low jets. In these coordinates the Jacobian is a scaled Vandermonde
matrix. This is the calculation `a02:endpoint-jacobian` in Lemma 3.3.
-/

namespace Submission.Obl.k4_matching_endpoint_volume

open scoped BigOperators ContDiff

/-- The internal-time Jacobian, with the low jets listed in reverse order. -/
noncomputable def endpointJacobian {m : ℕ} (w t : Fin m → ℝ) (s : ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  fun k p => -w p * (s - t p) ^ (k : ℕ) / ((k : ℕ).factorial : ℝ)

lemma det_endpointJacobian {m : ℕ} (w t : Fin m → ℝ) (s : ℝ) :
    (endpointJacobian w t s).det =
      (∏ k : Fin m, ((k : ℕ).factorial : ℝ)⁻¹) *
      (∏ p : Fin m, -w p) *
      (∏ p : Fin m, ∏ q ∈ Finset.Ioi p, ((s - t q) - (s - t p))) := by
  have hform : endpointJacobian w t s =
      Matrix.of (fun k p : Fin m => ((k : ℕ).factorial : ℝ)⁻¹ *
        (Matrix.of (fun k p : Fin m => -w p *
          (Matrix.vandermonde (fun p => s - t p)).transpose k p)) k p) := by
    ext k p
    simp only [endpointJacobian, Matrix.of_apply, Matrix.transpose_apply,
      Matrix.vandermonde_apply]
    ring
  rw [hform, Matrix.det_mul_column, Matrix.det_mul_row, Matrix.det_transpose,
    Matrix.det_vandermonde]
  ring

lemma abs_det_endpointJacobian {m : ℕ} (w t : Fin m → ℝ) (s : ℝ) :
    |(endpointJacobian w t s).det| =
      ((∏ p : Fin m, |w p|) *
        (∏ p : Fin m, ∏ q ∈ Finset.Ioi p, |t q - t p|)) /
      (∏ k : Fin m, ((k : ℕ).factorial : ℝ)) := by
  rw [det_endpointJacobian]
  simp only [abs_mul, Finset.abs_prod, abs_inv, abs_neg,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _)]
  rw [Finset.prod_inv_distrib]
  have hdiff : (∏ p : Fin m, ∏ q ∈ Finset.Ioi p, |s - t q - (s - t p)|) =
      ∏ p : Fin m, ∏ q ∈ Finset.Ioi p, |t q - t p| := by
    apply Finset.prod_congr rfl
    intro p hp
    apply Finset.prod_congr rfl
    intro q hq
    rw [show s - t q - (s - t p) = -(t q - t p) by ring, abs_neg]
  rw [hdiff]
  ring

lemma endpointJacobian_det_ne_zero {m : ℕ} (w t : Fin m → ℝ) (s : ℝ)
    (hw : ∀ p : Fin m, w p ≠ 0) (ht : Function.Injective t) :
    (endpointJacobian w t s).det ≠ 0 := by
  rw [det_endpointJacobian]
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact Finset.prod_ne_zero_iff.mpr fun k hk => inv_ne_zero
        (by exact_mod_cast Nat.factorial_ne_zero (k : ℕ))
    · exact Finset.prod_ne_zero_iff.mpr fun p hp => neg_ne_zero.mpr (hw p)
  · apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    have hpq : p < q := Finset.mem_Ioi.mp hq
    have hne : t p ≠ t q := fun h => (ne_of_lt hpq) (ht h)
    intro heq
    apply hne
    linarith

/-- The contribution of constant controls to the endpoint, in reverse jet order. -/
noncomputable def endpointLow {m : ℕ} (U : Fin (m + 1) → ℝ) (s₀ s : ℝ)
    (t : Fin m → ℝ) : Fin m → ℝ := fun k =>
  (U 0 * (s - s₀) ^ ((k : ℕ) + 1) +
    ∑ p : Fin m, (U p.succ - U p.castSucc) * (s - t p) ^ ((k : ℕ) + 1)) /
      (((k : ℕ) + 1).factorial : ℝ)

lemma contDiff_endpointLow {m : ℕ} (U : Fin (m + 1) → ℝ) (s₀ s : ℝ) :
    ContDiff ℝ ∞ (endpointLow U s₀ s) := by
  unfold endpointLow
  fun_prop

/-- The continuous linear map represented by the internal-time Jacobian. -/
noncomputable def endpointDerivative {m : ℕ} (w t : Fin m → ℝ) (s : ℝ) :
    (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    ∑ p : Fin m, endpointJacobian w t s k p • ContinuousLinearMap.proj p

lemma hasFDerivAt_endpointLow {m : ℕ} (U : Fin (m + 1) → ℝ) (s₀ s : ℝ)
    (t : Fin m → ℝ) :
    HasFDerivAt (endpointLow U s₀ s)
      (endpointDerivative (fun p => U p.succ - U p.castSucc) t s) t := by
  apply hasFDerivAt_pi.mpr
  intro k
  change HasFDerivAt (fun v : Fin m → ℝ => endpointLow U s₀ s v k)
    (∑ p : Fin m, endpointJacobian (fun p => U p.succ - U p.castSucc) t s k p •
      ContinuousLinearMap.proj p) t
  have hsum : HasFDerivAt
      (fun v : Fin m → ℝ => ∑ p : Fin m,
        (U p.succ - U p.castSucc) * (s - v p) ^ ((k : ℕ) + 1))
      (∑ p : Fin m, (U p.succ - U p.castSucc) •
        ((((k : ℕ) + 1) • (s - t p) ^ (k : ℕ)) •
          (-(ContinuousLinearMap.proj p : (Fin m → ℝ) →L[ℝ] ℝ)))) t := by
    apply HasFDerivAt.fun_sum
    intro p hp
    simpa only [Nat.add_sub_cancel] using
      (((hasFDerivAt_apply (𝕜 := ℝ) p t).const_sub s).pow ((k : ℕ) + 1)).const_mul
        (U p.succ - U p.castSucc)
  have hwhole := ((hasFDerivAt_const (U 0 * (s - s₀) ^ ((k : ℕ) + 1)) t).add hsum).mul_const
    ((((k : ℕ) + 1).factorial : ℝ)⁻¹)
  convert hwhole using 1
  · ext v
    simp only [endpointLow, div_eq_mul_inv, Pi.add_apply]
  · ext v
    simp only [endpointJacobian, sum_apply, smul_apply,
      ContinuousLinearMap.proj_apply, neg_apply, smul_eq_mul, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one, zero_add]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    have hf : ((k : ℕ).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k : ℕ)
    have hk : ((k : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp [hf, hk]

lemma endpointDerivative_toLinearMap {m : ℕ} (w t : Fin m → ℝ) (s : ℝ) :
    (endpointDerivative w t s).toLinearMap = Matrix.toLin' (endpointJacobian w t s) := by
  apply LinearMap.ext
  intro v
  funext k
  simp only [endpointDerivative, ContinuousLinearMap.coe_coe, ContinuousLinearMap.pi_apply,
    sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul,
    Matrix.toLin'_apply, Matrix.mulVec, dotProduct]

lemma det_endpointDerivative {m : ℕ} (w t : Fin m → ℝ) (s : ℝ) :
    (endpointDerivative w t s).det = (endpointJacobian w t s).det := by
  change LinearMap.det (endpointDerivative w t s).toLinearMap = _
  rw [endpointDerivative_toLinearMap, LinearMap.det_toLin']

lemma fderiv_endpointLow {m : ℕ} (U : Fin (m + 1) → ℝ) (s₀ s : ℝ)
    (t : Fin m → ℝ) :
    fderiv ℝ (endpointLow U s₀ s) t =
      endpointDerivative (fun p => U p.succ - U p.castSucc) t s :=
  (hasFDerivAt_endpointLow U s₀ s t).fderiv

lemma abs_det_fderiv_endpointLow {m : ℕ} (U : Fin (m + 1) → ℝ) (s₀ s : ℝ)
    (t : Fin m → ℝ) :
    |(fderiv ℝ (endpointLow U s₀ s) t).det| =
      ((∏ p : Fin m, |U p.succ - U p.castSucc|) *
        (∏ p : Fin m, ∏ q ∈ Finset.Ioi p, |t q - t p|)) /
      (∏ k : Fin m, ((k : ℕ).factorial : ℝ)) := by
  rw [fderiv_endpointLow, det_endpointDerivative, abs_det_endpointJacobian]

end Submission.Obl.k4_matching_endpoint_volume
