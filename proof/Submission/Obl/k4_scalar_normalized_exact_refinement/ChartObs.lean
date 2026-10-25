import Submission.Obl.k4_scalar_normalized_exact_refinement.Tails
import Submission.Obl.k4_scalar_normalized_exact_refinement.Spec
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.DensityTransport

/-!
# Observations of a normalized chart

A chart with time block `[t₀, t₀ + dt]`, affine base fit `u + t v` of width `J` and quadratic
hidden fit `P` at scale `a = N^(-r)` normalizes lines by a map `θ` with

* `y (θ l) ((t - t₀) / dt) = (y l t - u - t v) / J`,
* `x (θ l) ((t - t₀) / dt) = (x l t - P(t, y l t)) / a`,

the identities of the literal Refinement certificate. Here we only use these identities.
The normalized pure observation at depth `s` is an affine change of base coordinates of the
*shifted observation* `(t, y, ⌊(x - P(t, y)) / (a N^(-s))⌋)` of the original incidence, and the
original observation at depth `r + s` has a label which is one of two shifts of it.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis

open MeasureTheory Set
open scoped ENNReal

abbrev Line := ℕ × (Fin 5 → ℝ)
abbrev Inc := Line × ℝ
abbrev Base := (Fin 2 → ℝ) × ℤ
abbrev Joint := Base × ℤ

/-- The pure observation of the frozen statement at resolution `N` and depth `r`. -/
def obs (N r : ℝ) (z : Inc) : Base :=
  ((![z.2, Spec.y z.1 z.2] : Fin 2 → ℝ), ⌊Spec.x z.1 z.2 / N ^ (-r)⌋)

/-- The joint observation of the frozen statement at depth `r` and angular depth `u`. -/
def aug (N r u : ℝ) (z : Inc) : Joint := (obs N r z, ⌊z.1.2 1 / N ^ (-u)⌋)

def BaseRef : Measure Base := volume.prod Measure.count
def JointRef : Measure Joint := BaseRef.prod Measure.count

scoped instance baseRef_sigmaFinite : SigmaFinite BaseRef := by unfold BaseRef; infer_instance
scoped instance jointRef_sigmaFinite : SigmaFinite JointRef := by unfold JointRef; infer_instance

lemma measurable_obs (N r : ℝ) : Measurable (obs N r) := by
  unfold obs Spec.x Spec.y
  fun_prop

lemma measurable_aug (N r u : ℝ) : Measurable (aug N r u) := by
  unfold aug
  exact (measurable_obs N r).prodMk (by fun_prop)

/-- The shifted observation: the hidden bin of the residual `x - P(t, y)` at width `w`. -/
def shiftObs (w : ℝ) (P : MvPolynomial (Fin 2) ℝ) (z : Inc) : Base :=
  ((![z.2, Spec.y z.1 z.2] : Fin 2 → ℝ),
    ⌊(Spec.x z.1 z.2 - MvPolynomial.eval (![z.2, Spec.y z.1 z.2] : Fin 2 → ℝ) P) / w⌋)

lemma measurable_shiftObs (w : ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    Measurable (shiftObs w P) := by
  have hb : Measurable (fun z : Inc => (![z.2, Spec.y z.1 z.2] : Fin 2 → ℝ)) := by
    unfold Spec.y
    fun_prop
  have hP : Measurable (fun z : Inc =>
      MvPolynomial.eval (![z.2, Spec.y z.1 z.2] : Fin 2 → ℝ) P) :=
    (MvPolynomial.continuous_eval P).measurable.comp hb
  have hx : Measurable (fun z : Inc => Spec.x z.1 z.2) := by
    unfold Spec.x
    fun_prop
  unfold shiftObs
  exact hb.prodMk (((hx.sub hP).div_const w).floor)

/-! ## The base change of a chart -/

/-- Forward linear part `(τ, η) ↦ (dt τ, dt v τ + J η)`. -/
def chartMatrix (dt v J : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![dt, 0; dt * v, J]

lemma det_chartMatrix (dt v J : ℝ) : (chartMatrix dt v J).det = dt * J := by
  simp [chartMatrix, Matrix.det_fin_two]

def chartLinear (dt v J : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) :
    (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 2)) (chartMatrix dt v J)
    (isUnit_iff_ne_zero.mpr (by rw [det_chartMatrix]; exact mul_ne_zero hdt hJ))

lemma chartLinear_apply (dt v J : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (b : Fin 2 → ℝ) :
    chartLinear dt v J hdt hJ b = ![dt * b 0, dt * v * b 0 + J * b 1] := by
  ext i
  fin_cases i <;>
    simp [chartLinear, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin',
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, chartMatrix]

lemma det_chartLinear (dt v J : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) :
    LinearMap.det (chartLinear dt v J hdt hJ).toLinearMap = dt * J := by
  change LinearMap.det (Matrix.toLin (Pi.basisFun ℝ (Fin 2))
    (Pi.basisFun ℝ (Fin 2)) (chartMatrix dt v J)) = dt * J
  rw [LinearMap.det_toLin, det_chartMatrix]

/-- Normalized base coordinates to original ones: `t = t₀ + dt τ`, `y = u + t v + J η`. -/
def chartForward (t₀ dt u v J : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) :
    (Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) :=
  k4_dyadic_crop_affine_laws.Framework.affineObservationEquiv
    (chartLinear dt v J hdt hJ) ![t₀, u + t₀ * v]

lemma chartForward_apply (t₀ dt u v J : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (b : Fin 2 → ℝ) :
    chartForward t₀ dt u v J hdt hJ b =
      ![t₀ + dt * b 0, u + (t₀ + dt * b 0) * v + J * b 1] := by
  rw [chartForward, k4_dyadic_crop_affine_laws.Framework.affineObservationEquiv_apply,
    chartLinear_apply]
  ext i
  fin_cases i <;> simp <;> ring

lemma chartForward_symm_apply (t₀ dt u v J : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0)
    (b : Fin 2 → ℝ) :
    (chartForward t₀ dt u v J hdt hJ).symm b =
      ![(b 0 - t₀) / dt, (b 1 - u - b 0 * v) / J] := by
  apply (chartForward t₀ dt u v J hdt hJ).injective
  rw [MeasurableEquiv.apply_symm_apply, chartForward_apply]
  ext i
  fin_cases i <;> simp <;> field_simp <;> ring

lemma map_chartForward_symm (t₀ dt u v J : ℝ) (hdt : 0 < dt) (hJ : 0 < J) :
    (volume : Measure (Fin 2 → ℝ)).map (chartForward t₀ dt u v J hdt.ne' hJ.ne').symm =
      ENNReal.ofReal (dt * J) • volume := by
  rw [chartForward, k4_dyadic_crop_affine_laws.Framework.map_affineObservationEquiv_symm,
    det_chartLinear, abs_of_pos (mul_pos hdt hJ)]

/-- The base change of a chart on pure observations. -/
def baseEquiv (t₀ dt u v J : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) : Base ≃ᵐ Base :=
  (chartForward t₀ dt u v J hdt hJ).symm.prodCongr (MeasurableEquiv.refl ℤ)

lemma baseEquiv_apply (t₀ dt u v J : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (o : Base) :
    baseEquiv t₀ dt u v J hdt hJ o =
      (![(o.1 0 - t₀) / dt, (o.1 1 - u - o.1 0 * v) / J], o.2) := by
  change ((chartForward t₀ dt u v J hdt hJ).symm o.1, o.2) = _
  rw [chartForward_symm_apply]

lemma map_baseEquiv (t₀ dt u v J : ℝ) (hdt : 0 < dt) (hJ : 0 < J) :
    BaseRef.map (baseEquiv t₀ dt u v J hdt.ne' hJ.ne') = ENNReal.ofReal (dt * J) • BaseRef :=
  k4_dyadic_crop_affine_laws.Framework.map_prod_count_equiv _ _ _ _
    (map_chartForward_symm t₀ dt u v J hdt hJ)

/-- The base change of a chart on joint observations. -/
def jointEquiv (t₀ dt u v J : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) : Joint ≃ᵐ Joint :=
  (baseEquiv t₀ dt u v J hdt hJ).prodCongr (MeasurableEquiv.refl ℤ)

lemma jointEquiv_apply (t₀ dt u v J : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) (o : Joint) :
    jointEquiv t₀ dt u v J hdt hJ o = (baseEquiv t₀ dt u v J hdt hJ o.1, o.2) := rfl

lemma map_jointEquiv (t₀ dt u v J : ℝ) (hdt : 0 < dt) (hJ : 0 < J) :
    JointRef.map (jointEquiv t₀ dt u v J hdt.ne' hJ.ne') = ENNReal.ofReal (dt * J) • JointRef :=
  k4_dyadic_crop_affine_laws.Framework.map_prod_count_equiv _ _ _ _
    (map_baseEquiv t₀ dt u v J hdt hJ)

/-! ## Observations through the normalization identities -/

section Identities

variable {N r t₀ dt u v J : ℝ} {P : MvPolynomial (Fin 2) ℝ} {θ : Line → Line}

/-- The normalized incidence map. -/
def normInc (t₀ dt : ℝ) (θ : Line → Line) (z : Inc) : Inc := (θ z.1, (z.2 - t₀) / dt)

lemma measurable_normInc (t₀ dt : ℝ) {θ : Line → Line} (hθ : Measurable θ) :
    Measurable (normInc t₀ dt θ) := by
  unfold normInc
  exact (hθ.comp measurable_fst).prodMk ((measurable_snd.sub_const t₀).div_const dt)

lemma obs_normInc (hN : 0 < N) (hdt : 0 < dt) (hJ : 0 < J)
    (hy : ∀ l t, Spec.y (θ l) ((t - t₀) / dt) = (Spec.y l t - u - t * v) / J)
    (hx : ∀ l t, Spec.x (θ l) ((t - t₀) / dt) =
      (Spec.x l t - MvPolynomial.eval ![t, Spec.y l t] P) / N ^ (-r))
    (s : ℝ) (z : Inc) :
    obs N s (normInc t₀ dt θ z) =
      baseEquiv t₀ dt u v J hdt.ne' hJ.ne' (shiftObs (N ^ (-(r + s))) P z) := by
  rw [baseEquiv_apply]
  unfold obs shiftObs normInc
  simp only
  rw [hy, hx]
  have hw : N ^ (-r) * N ^ (-s) = N ^ (-(r + s)) := by
    rw [← Real.rpow_add hN]
    ring_nf
  apply Prod.ext
  · ext i
    fin_cases i <;> simp
  · simp only
    congr 1
    rw [div_div, hw]

/-- The normalized velocity of a line. -/
lemma velocity_normInc (hdt : 0 < dt) (hJ : 0 < J)
    (hy : ∀ l t, Spec.y (θ l) ((t - t₀) / dt) = (Spec.y l t - u - t * v) / J)
    (l : Line) : (θ l).2 1 = dt * (l.2 1 - v) / J := by
  have h0 := hy l t₀
  have h1 := hy l (t₀ + dt)
  simp only [Spec.y, sub_self, zero_div, zero_mul, add_zero] at h0 h1
  have hd : (t₀ + dt - t₀) / dt = 1 := by field_simp; ring
  rw [hd, one_mul] at h1
  have : (θ l).2 1 = (l.2 0 + (t₀ + dt) * l.2 1 - u - (t₀ + dt) * v) / J -
      (l.2 0 + t₀ * l.2 1 - u - t₀ * v) / J := by linarith
  rw [this]
  field_simp
  ring

lemma aug_normInc (hN : 0 < N) (hdt : 0 < dt) (hJ : 0 < J)
    (hy : ∀ l t, Spec.y (θ l) ((t - t₀) / dt) = (Spec.y l t - u - t * v) / J)
    (hx : ∀ l t, Spec.x (θ l) ((t - t₀) / dt) =
      (Spec.x l t - MvPolynomial.eval ![t, Spec.y l t] P) / N ^ (-r))
    (s w : ℝ) (z : Inc) :
    aug N s w (normInc t₀ dt θ z) =
      jointEquiv t₀ dt u v J hdt.ne' hJ.ne'
        (shiftObs (N ^ (-(r + s))) P z, ⌊(dt * (z.1.2 1 - v) / J) / N ^ (-w)⌋) := by
  rw [jointEquiv_apply]
  unfold aug
  rw [obs_normInc hN hdt hJ hy hx s z]
  congr 2
  unfold normInc
  simp only
  rw [velocity_normInc hdt hJ hy]

end Identities

/-! ## Two shifts of the hidden bin -/

/-- Floor of a shifted real is one of two shifts of the floor. -/
lemma floor_add_cases (a b : ℝ) : ⌊a + b⌋ = ⌊a⌋ + ⌊b⌋ ∨ ⌊a + b⌋ = ⌊a⌋ + ⌊b⌋ + 1 := by
  have h1 : (⌊a⌋ : ℝ) + ⌊b⌋ ≤ a + b := add_le_add (Int.floor_le a) (Int.floor_le b)
  have h2 : a + b < (⌊a⌋ : ℝ) + ⌊b⌋ + 2 := by
    have := Int.lt_floor_add_one a
    have := Int.lt_floor_add_one b
    linarith
  have hlo : ⌊a⌋ + ⌊b⌋ ≤ ⌊a + b⌋ := Int.le_floor.mpr (by push_cast; exact h1)
  have hhi : ⌊a + b⌋ < ⌊a⌋ + ⌊b⌋ + 2 := Int.floor_lt.mpr (by push_cast; exact h2)
  omega

/-- The label map recovering an original hidden bin from a shifted one. -/
def unshift (w : ℝ) (P : MvPolynomial (Fin 2) ℝ) (j : Fin 2) (o : Base) : Base :=
  (o.1, o.2 - ⌊-MvPolynomial.eval o.1 P / w⌋ - (j : ℤ))

lemma measurable_unshift (w : ℝ) (P : MvPolynomial (Fin 2) ℝ) (j : Fin 2) :
    Measurable (unshift w P j) := by
  unfold unshift
  refine measurable_fst.prodMk ?_
  have hP : Measurable (fun o : Base => MvPolynomial.eval o.1 P) :=
    (MvPolynomial.continuous_eval P).measurable.comp measurable_fst
  exact (measurable_snd.sub ((hP.neg.div_const w).floor)).sub_const _

/-- The original observation at the depth of the shift is an unshift of the shifted one. -/
lemma obs_eq_unshift {N σ : ℝ} (P : MvPolynomial (Fin 2) ℝ) (z : Inc) :
    ∃ j : Fin 2, obs N σ z = unshift (N ^ (-σ)) P j (shiftObs (N ^ (-σ)) P z) := by
  set w := N ^ (-σ)
  set X := Spec.x z.1 z.2
  set Q := MvPolynomial.eval (![z.2, Spec.y z.1 z.2] : Fin 2 → ℝ) P
  have hsplit : (X - Q) / w = X / w + (-Q / w) := by ring
  rcases floor_add_cases (X / w) (-Q / w) with h | h
  · refine ⟨0, Prod.ext rfl ?_⟩
    show ⌊X / w⌋ = ⌊(X - Q) / w⌋ - ⌊-Q / w⌋ - (((0 : Fin 2) : ℕ) : ℤ)
    rw [hsplit, h]
    simp
  · refine ⟨1, Prod.ext rfl ?_⟩
    show ⌊X / w⌋ = ⌊(X - Q) / w⌋ - ⌊-Q / w⌋ - (((1 : Fin 2) : ℕ) : ℤ)
    rw [hsplit, h]
    simp only [Fin.isValue, Fin.val_one, Nat.cast_one]
    ring

end Submission.Obl.k4_scalar_normalized_exact_refinement.Analysis
