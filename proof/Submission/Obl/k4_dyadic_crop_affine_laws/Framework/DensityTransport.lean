/- Adapted from this LOT tree, obligation o077, x0250, commit 6b0e9a0.
Interface originally from o077 session x0266; other original provenance follows. -/

/-
Adapted from this LOT tree, obligation o006, session x0006, branch x0006,
Submission/Obl/k4_core/Framework/DensityTransport.lean.
Original code and any earlier attribution are retained below.
-/

import Mathlib

/-!
# Exact transport and conditioning of observation densities

Transported bins are retained as labels. The normalization factor is the base
Jacobian divided by the original product-prior budget.
-/

namespace Submission.Obl.k4_dyadic_crop_affine_laws.Framework

open MeasureTheory Set
open scoped ENNReal

/-- An observation density transports by composing with the inverse coordinate
map. This formula is valid before any conditioning or renormalization. -/
theorem map_withDensity_measurableEquiv {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y) (μ : Measure X)
    (ρ : X → ENNReal) (hρ : Measurable ρ) :
    (μ.withDensity ρ).map e = (μ.map e).withDensity (fun y => ρ (e.symm y)) := by
  ext S hS
  rw [Measure.map_apply e.measurable hS, withDensity_apply _ (e.measurable hS),
    withDensity_apply _ hS]
  simpa only [e.symm_apply_apply] using
    (setLIntegral_map (μ := μ) (f := fun y => ρ (e.symm y)) (g := e) hS
      (hρ.comp e.symm.measurable) e.measurable).symm

/-- Exact density transport with a constant base Jacobian and an independent
normalization of the selected incidence law. -/
theorem normalized_density_transport {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (ν : Measure Y) (J budget : ENNReal)
    (hbase : μ.map e = J • ν) (ρ : X → ENNReal) (hρ : Measurable ρ) :
    (budget⁻¹ • μ.withDensity ρ).map e =
      ν.withDensity (fun y => (J / budget) * ρ (e.symm y)) := by
  rw [Measure.map_smul _ e.measurable.aemeasurable, map_withDensity_measurableEquiv e μ ρ hρ,
    hbase, withDensity_smul_measure, smul_smul]
  have hm : Measurable (fun y => ρ (e.symm y)) := hρ.comp e.symm.measurable
  rw [← withDensity_smul _ hm]
  congr 1
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
  ring

/-- A time-block base Jacobian `q*J` divided by the unchanged product-prior
budget `q*prior` leaves exactly `J/prior`. -/
theorem block_density_normalization (q J prior : ENNReal) (hq : q ≠ 0) (hqtop : q ≠ ∞) :
    (q * J) / (q * prior) = J / prior := by
  rw [ENNReal.mul_div_mul_left _ _ hq hqtop]

/-- Exact normalization for a retained time block. Its density factor contains
only the spatial Jacobian and the unchanged assigned prior mass. -/
theorem normalized_block_density_transport {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (μ : Measure X) (ν : Measure Y) (q J prior : ENNReal)
    (hq : q ≠ 0) (hqtop : q ≠ ∞) (hbase : μ.map e = (q * J) • ν)
    (ρ : X → ENNReal) (hρ : Measurable ρ) :
    ((q * prior)⁻¹ • μ.withDensity ρ).map e =
      ν.withDensity (fun y => (J / prior) * ρ (e.symm y)) := by
  simpa only [block_density_normalization q J prior hq hqtop] using
    normalized_density_transport e μ ν (q * J) (q * prior) hbase ρ hρ

section Affine

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The affine map from normalized to original continuous observation coordinates. -/
noncomputable def affineObservationEquiv (L : E ≃ₗ[ℝ] E) (b : E) : E ≃ᵐ E :=
  L.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.addRight b)

theorem affineObservationEquiv_apply (L : E ≃ₗ[ℝ] E) (b x : E) :
    affineObservationEquiv L b x = L x + b := rfl

theorem affineObservationEquiv_symm_apply (L : E ≃ₗ[ℝ] E) (b x : E) :
    (affineObservationEquiv L b).symm x = L.symm (x - b) := by
  simp [affineObservationEquiv, sub_eq_add_neg]

/-- The inverse coordinate map carries original base Haar measure to the
normalized base measure multiplied by the forward affine Jacobian. -/
theorem map_affineObservationEquiv_symm (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : E ≃ₗ[ℝ] E) (b : E) :
    μ.map (affineObservationEquiv L b).symm =
      ENNReal.ofReal |LinearMap.det (L : E →ₗ[ℝ] E)| • μ := by
  have hsub : Measurable (fun x : E => x - b) := measurable_id.sub_const b
  have hL : Measurable (L.symm : E → E) := L.symm.toContinuousLinearEquiv.continuous.measurable
  have hcomp : (fun x : E => L.symm (x - b)) = L.symm ∘ (fun x => x - b) := rfl
  rw [show ((affineObservationEquiv L b).symm : E → E) =
    (fun x : E => L.symm (x - b)) from funext (affineObservationEquiv_symm_apply L b)]
  rw [hcomp, ← Measure.map_map hL hsub, (measurePreserving_sub_right μ b).map_eq]
  change μ.map ((L.symm : E →ₗ[ℝ] E) : E → E) = _
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar μ L.symm.isUnit_det'.ne_zero,
    LinearEquiv.det_coe_symm, inv_inv]

end Affine

/-- Matrix of the forward time and planar-space change of coordinates. -/
def chartBaseMatrix (q : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![q, 0, 0;
    q * u 0, Q 0 0, Q 0 1;
    q * u 1, Q 1 0, Q 1 1]

theorem det_chartBaseMatrix (q : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    (chartBaseMatrix q u Q).det = q * Q.det := by
  simp [chartBaseMatrix, Matrix.det_fin_three, Matrix.det_fin_two]
  ring

/-- The linear part of the chart's forward base-coordinate transformation. -/
noncomputable def chartBaseLinearEquiv (q : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hq : q ≠ 0) (hQ : Q.det ≠ 0) :
    EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  Matrix.toLinearEquiv (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (chartBaseMatrix q u Q) (isUnit_iff_ne_zero.mpr (by
      rw [det_chartBaseMatrix]
      exact mul_ne_zero hq hQ))

theorem det_chartBaseLinearEquiv (q : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hq : q ≠ 0) (hQ : Q.det ≠ 0) :
    LinearMap.det (chartBaseLinearEquiv q u Q hq hQ).toLinearMap = q * Q.det := by
  change LinearMap.det (Matrix.toLin (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (chartBaseMatrix q u Q)) = _
  rw [LinearMap.det_toLin, det_chartBaseMatrix]

theorem chartBaseLinearEquiv_apply (q : ℝ) (u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hq : q ≠ 0) (hQ : Q.det ≠ 0)
    (x : EuclideanSpace ℝ (Fin 3)) :
    chartBaseLinearEquiv q u Q hq hQ x = Matrix.toEuclideanLin (chartBaseMatrix q u Q) x := rfl

/-- The chart maps normalized time and position to
`t=t0+q*tau`, `y=c+t*u+Q*z`. -/
noncomputable def chartBaseEquiv (t0 q : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hq : q ≠ 0) (hQ : Q.det ≠ 0) :
    EuclideanSpace ℝ (Fin 3) ≃ᵐ EuclideanSpace ℝ (Fin 3) :=
  affineObservationEquiv (chartBaseLinearEquiv q u Q hq hQ)
    (WithLp.toLp 2 ![t0, c 0 + t0 * u 0, c 1 + t0 * u 1])

theorem chartBaseEquiv_apply (t0 q : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hq : q ≠ 0) (hQ : Q.det ≠ 0)
    (x : EuclideanSpace ℝ (Fin 3)) :
    chartBaseEquiv t0 q c u Q hq hQ x = WithLp.toLp 2
      ![t0 + q * x 0,
        c 0 + (t0 + q * x 0) * u 0 + Q 0 0 * x 1 + Q 0 1 * x 2,
        c 1 + (t0 + q * x 0) * u 1 + Q 1 0 * x 1 + Q 1 1 * x 2] := by
  rw [chartBaseEquiv, affineObservationEquiv_apply, chartBaseLinearEquiv_apply]
  ext i
  fin_cases i <;>
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, chartBaseMatrix,
      dotProduct, Fin.sum_univ_succ] <;> ring

/-- The chart normalization has exactly the forward base Jacobian `q*abs(det Q)`. -/
theorem map_chartBaseEquiv_symm (t0 q : ℝ) (c u : EuclideanSpace ℝ (Fin 2))
    (Q : Matrix (Fin 2) (Fin 2) ℝ) (hq : 0 < q) (hQ : Q.det ≠ 0) :
    (volume : Measure (EuclideanSpace ℝ (Fin 3))).map
      (chartBaseEquiv t0 q c u Q hq.ne' hQ).symm =
      ENNReal.ofReal (q * |Q.det|) • volume := by
  rw [chartBaseEquiv, map_affineObservationEquiv_symm, det_chartBaseLinearEquiv,
    abs_mul, abs_of_pos hq]

/-- Retaining a discrete observation label leaves a constant base Jacobian unchanged. -/
theorem map_prod_count_equiv {X Y B : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B]
    (e : X ≃ᵐ Y) (μ : Measure X) (ν : Measure Y) [SFinite μ]
    (J : ENNReal) (hbase : μ.map e = J • ν) :
    (μ.prod (Measure.count : Measure B)).map (e.prodCongr (MeasurableEquiv.refl B)) =
      J • ν.prod Measure.count := by
  change (μ.prod (Measure.count : Measure B)).map (Prod.map e id) = _
  rw [← Measure.map_prod_map μ Measure.count e.measurable measurable_id,
    Measure.map_id, hbase, Measure.prod_smul_left]

/-- For transported hidden bins the exact within-world chart density is
`abs(det Q)/prior` times the assigned original density. -/
theorem normalized_chart_observation_density {B : Type*} [MeasurableSpace B]
    [Countable B] [MeasurableSingletonClass B]
    (t0 q : ℝ) (c u : EuclideanSpace ℝ (Fin 2)) (Q : Matrix (Fin 2) (Fin 2) ℝ)
    (hq : 0 < q) (hQ : Q.det ≠ 0) (prior : ENNReal)
    (ρ : EuclideanSpace ℝ (Fin 3) × B → ENNReal) (hρ : Measurable ρ) :
    ((ENNReal.ofReal q * prior)⁻¹ •
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity ρ).map
      ((chartBaseEquiv t0 q c u Q hq.ne' hQ).symm.prodCongr (MeasurableEquiv.refl B)) =
      ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod Measure.count).withDensity
        (fun y => (ENNReal.ofReal |Q.det| / prior) *
          ρ ((chartBaseEquiv t0 q c u Q hq.ne' hQ).prodCongr (MeasurableEquiv.refl B) y)) := by
  have hbase := map_prod_count_equiv
    (B := B) (chartBaseEquiv t0 q c u Q hq.ne' hQ).symm volume volume
    (ENNReal.ofReal (q * |Q.det|)) (map_chartBaseEquiv_symm t0 q c u Q hq hQ)
  rw [ENNReal.ofReal_mul hq.le] at hbase
  convert normalized_block_density_transport
      ((chartBaseEquiv t0 q c u Q hq.ne' hQ).symm.prodCongr (MeasurableEquiv.refl B))
      (volume.prod Measure.count) (volume.prod Measure.count)
      (ENNReal.ofReal q) (ENNReal.ofReal |Q.det|) prior
      (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top hbase ρ hρ using 1
  congr 1

end Submission.Obl.k4_dyadic_crop_affine_laws.Framework
