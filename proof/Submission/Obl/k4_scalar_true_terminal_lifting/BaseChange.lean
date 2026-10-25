import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.DensityTransport
import Submission.Obl.k4_crop_base_finite_tail.BaseTransport
import Submission.Obl.k4_scalar_crop_profile_transport.Angular

noncomputable section

namespace Submission.Obl.k4_scalar_true_terminal_lifting

open MeasureTheory Set
open scoped ENNReal

abbrev Line := ℕ × (Fin 5 → ℝ)
abbrev State := Line × ℝ
abbrev Observation := (Fin 2 → ℝ) × ℤ

abbrev reference : Measure Observation := volume.prod Measure.count

/-- The forward scalar change sends normalized time and position to the original
ones. Its determinant is the product of the time and position widths. -/
def normalizationMatrix (dt J v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![dt, 0; dt * v, J]

theorem normalizationMatrix_det (dt J v : ℝ) :
    (normalizationMatrix dt J v).det = dt * J := by
  simp [normalizationMatrix, Matrix.det_fin_two]

def normalizationLinear (dt J v : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) :
    (Fin 2 → ℝ) ≃ₗ[ℝ] (Fin 2 → ℝ) :=
  Matrix.toLinearEquiv (Pi.basisFun ℝ (Fin 2)) (normalizationMatrix dt J v)
    (isUnit_iff_ne_zero.mpr (by rw [normalizationMatrix_det]; exact mul_ne_zero hdt hJ))

theorem normalizationLinear_apply (dt J v : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0)
    (s : Fin 2 → ℝ) :
    normalizationLinear dt J v hdt hJ s = ![dt * s 0, dt * v * s 0 + J * s 1] := by
  ext e
  fin_cases e <;>
    simp [normalizationLinear, Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin',
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      normalizationMatrix]

theorem normalizationLinear_det (dt J v : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) :
    LinearMap.det (normalizationLinear dt J v hdt hJ).toLinearMap = dt * J := by
  change LinearMap.det (Matrix.toLin (Pi.basisFun ℝ (Fin 2))
    (Pi.basisFun ℝ (Fin 2)) (normalizationMatrix dt J v)) = _
  rw [LinearMap.det_toLin, normalizationMatrix_det]

def baseForward (dt J u v t₀ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) :
    (Fin 2 → ℝ) ≃ᵐ (Fin 2 → ℝ) :=
  k4_dyadic_crop_affine_laws.Framework.affineObservationEquiv
    (normalizationLinear dt J v hdt hJ) ![t₀, u + t₀ * v]

theorem baseForward_apply (dt J u v t₀ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0)
    (s : Fin 2 → ℝ) :
    baseForward dt J u v t₀ hdt hJ s =
      ![dt * s 0 + t₀, u + (dt * s 0 + t₀) * v + J * s 1] := by
  rw [baseForward, k4_dyadic_crop_affine_laws.Framework.affineObservationEquiv_apply,
    normalizationLinear_apply]
  ext e
  fin_cases e <;> simp
  ring

theorem baseForward_symm_apply (dt J u v t₀ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0)
    (s : Fin 2 → ℝ) :
    (baseForward dt J u v t₀ hdt hJ).symm s =
      ![(s 0 - t₀) / dt, (s 1 - u - s 0 * v) / J] := by
  apply (baseForward dt J u v t₀ hdt hJ).injective
  rw [MeasurableEquiv.apply_symm_apply, baseForward_apply]
  ext e
  fin_cases e <;> simp
  · field_simp
    ring
  · field_simp
    ring

def observationEquiv (dt J u v t₀ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0) :
    Observation ≃ᵐ Observation :=
  (baseForward dt J u v t₀ hdt hJ).symm.prodCongr (MeasurableEquiv.refl ℤ)

theorem observationEquiv_apply (dt J u v t₀ : ℝ) (hdt : dt ≠ 0) (hJ : J ≠ 0)
    (s : Observation) :
    observationEquiv dt J u v t₀ hdt hJ s =
      (![(s.1 0 - t₀) / dt, (s.1 1 - u - s.1 0 * v) / J], s.2) := by
  change ((baseForward dt J u v t₀ hdt hJ).symm s.1, s.2) = _
  rw [baseForward_symm_apply]

theorem map_observationEquiv_reference (dt J u v t₀ : ℝ) (hdt : 0 < dt) (hJ : 0 < J) :
    reference.map (observationEquiv dt J u v t₀ hdt.ne' hJ.ne') =
      ENNReal.ofReal (dt * J) • reference := by
  apply k4_dyadic_crop_affine_laws.Framework.map_prod_count_equiv
  change (volume : Measure (Fin 2 → ℝ)).map (baseForward dt J u v t₀ hdt.ne' hJ.ne').symm = _
  rw [baseForward, k4_dyadic_crop_affine_laws.Framework.map_affineObservationEquiv_symm,
    normalizationLinear_det, abs_of_pos (mul_pos hdt hJ)]

/-- Pull a terminal observation density back through an exact selected-law
transport. The time width cancels, leaving the full assigned prior divided by
the scalar position width. -/
theorem raw_terminal_density_law
    (dt J u v t₀ : ℝ) (hdt : 0 < dt) (hJ : 0 < J)
    (a : ℝ≥0∞) (ha : a ≠ 0) (hat : a ≠ ∞)
    (source target : Measure State) (θ : State → State) (hθ : Measurable θ)
    (oldObs newObs : State → Observation) (hold : Measurable oldObs)
    (hnew : Measurable newObs)
    (hcommute : newObs ∘ θ = observationEquiv dt J u v t₀ hdt.ne' hJ.ne' ∘ oldObs)
    (htransport : target = (ENNReal.ofReal dt * a)⁻¹ • source.map θ)
    (G : Observation → ℝ≥0∞) (hG : Measurable G)
    (hlaw : target.map newObs = reference.withDensity G) :
    source.map oldObs = reference.withDensity (fun z =>
      (a / ENNReal.ofReal J) * G (observationEquiv dt J u v t₀ hdt.ne' hJ.ne' z)) := by
  let e := observationEquiv dt J u v t₀ hdt.ne' hJ.ne'
  have ht : ENNReal.ofReal dt ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hdt
  have hbase : reference.map e = ENNReal.ofReal (dt * J) • reference :=
    map_observationEquiv_reference dt J u v t₀ hdt hJ
  have hnormal : (ENNReal.ofReal dt * a)⁻¹ • (source.map oldObs).map e =
      reference.withDensity G := by
    rw [htransport, Measure.map_smul _ hnew.aemeasurable,
      Measure.map_map hnew hθ, hcommute, ← Measure.map_map e.measurable hold] at hlaw
    exact hlaw
  have h := k4_crop_base_finite_tail.BaseTransport.pullback_density_law e reference reference
    (ENNReal.ofReal (dt * J)) (ENNReal.ofReal dt * a)
    (ENNReal.ofReal_ne_zero_iff.mpr (mul_pos hdt hJ)) ENNReal.ofReal_ne_top
    (mul_ne_zero ht ha) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hat)
    hbase (source.map oldObs) G hG hnormal
  simpa only [ENNReal.ofReal_mul hdt.le,
    k4_dyadic_crop_affine_laws.Framework.block_density_normalization
      (ENNReal.ofReal dt) a (ENNReal.ofReal J) ht ENNReal.ofReal_ne_top] using h

def normalizeState (θ : Line → Line) (dt t₀ : ℝ) (s : State) : State :=
  (θ s.1, (s.2 - t₀) / dt)

theorem measurable_normalizeState {θ : Line → Line} (hθ : Measurable θ) (dt t₀ : ℝ) :
    Measurable (normalizeState θ dt t₀) := by
  exact (hθ.comp measurable_fst).prodMk ((measurable_snd.sub_const t₀).div_const dt)

/-- Terminal observations in the original continuous coordinates, with the
polynomial subtracted before recording the hidden bin. -/
def residualObservation (N L : ℝ) (P : MvPolynomial (Fin 2) ℝ) (s : State) : Observation :=
  (![s.2, k4_scalar_crop_profile_transport.y s.1 s.2],
    ⌊(k4_scalar_crop_profile_transport.x s.1 s.2 -
      MvPolynomial.eval ![s.2, k4_scalar_crop_profile_transport.y s.1 s.2] P) / N ^ (-L)⌋)

theorem measurable_residualObservation (N L : ℝ) (P : MvPolynomial (Fin 2) ℝ) :
    Measurable (residualObservation N L P) := by
  have hb : Measurable (fun s : State => ![s.2, k4_scalar_crop_profile_transport.y s.1 s.2]) := by
    apply Measurable.of_eval
    intro e
    fin_cases e <;> simp [k4_scalar_crop_profile_transport.y] <;> fun_prop
  have hx : Measurable (fun s : State => k4_scalar_crop_profile_transport.x s.1 s.2) := by
    unfold k4_scalar_crop_profile_transport.x
    fun_prop
  have he := P.continuous_eval.measurable.comp hb
  exact hb.prodMk (Int.measurable_floor.comp ((hx.sub he).div_const _))

theorem residual_hidden_bin_cases (N L : ℝ) (P : MvPolynomial (Fin 2) ℝ) (s : State) :
    (residualObservation N L P s).2 = (k4_scalar_crop_profile_transport.Obs N L s).2 +
        ⌊-MvPolynomial.eval (k4_scalar_crop_profile_transport.Obs N L s).1 P / N ^ (-L)⌋ ∨
      (residualObservation N L P s).2 = (k4_scalar_crop_profile_transport.Obs N L s).2 +
        ⌊-MvPolynomial.eval (k4_scalar_crop_profile_transport.Obs N L s).1 P / N ^ (-L)⌋ + 1 := by
  simpa only [residualObservation, k4_scalar_crop_profile_transport.Obs, sub_div, neg_div,
    add_assoc] using k4_scalar_crop_profile_transport.floor_sub_cases
      (k4_scalar_crop_profile_transport.x s.1 s.2 / N ^ (-L))
      (MvPolynomial.eval ![s.2, k4_scalar_crop_profile_transport.y s.1 s.2] P / N ^ (-L))

theorem terminal_observation_commutes
    {N : ℝ} (hN : 0 < N) (L r dt J u v t₀ : ℝ) (hdt : 0 < dt) (hJ : 0 < J)
    (P : MvPolynomial (Fin 2) ℝ) (θ : Line → Line)
    (hy : ∀ l t, k4_scalar_crop_profile_transport.y (θ l) ((t - t₀) / dt) =
      (k4_scalar_crop_profile_transport.y l t - u - t * v) / J)
    (hx : ∀ l t, k4_scalar_crop_profile_transport.x (θ l) ((t - t₀) / dt) =
      (k4_scalar_crop_profile_transport.x l t -
        MvPolynomial.eval ![t, k4_scalar_crop_profile_transport.y l t] P) / N ^ (-r)) :
    k4_scalar_crop_profile_transport.Obs N (L - r) ∘ normalizeState θ dt t₀ =
      observationEquiv dt J u v t₀ hdt.ne' hJ.ne' ∘ residualObservation N L P := by
  funext s
  rw [Function.comp_apply, Function.comp_apply, observationEquiv_apply]
  apply Prod.ext
  · ext e
    fin_cases e <;> simp [normalizeState, k4_scalar_crop_profile_transport.Obs,
      residualObservation, hy]
  · change ⌊k4_scalar_crop_profile_transport.x (θ s.1) ((s.2 - t₀) / dt) / N ^ (-(L - r))⌋ =
      ⌊(k4_scalar_crop_profile_transport.x s.1 s.2 -
        MvPolynomial.eval ![s.2, k4_scalar_crop_profile_transport.y s.1 s.2] P) / N ^ (-L)⌋
    rw [hx, div_div, ← Real.rpow_add hN, show -r + -(L - r) = -L by ring]

end Submission.Obl.k4_scalar_true_terminal_lifting
