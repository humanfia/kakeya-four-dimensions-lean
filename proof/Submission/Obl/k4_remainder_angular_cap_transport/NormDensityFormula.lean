import Submission.Obl.k4_remainder_angular_cap_transport.NormDensity
/- Adapted from this LOT tree, o064, session x0214, commit a612574618456ee4cdb4d54c4cee48847fe99758,
Submission/Obl/k4_terminal_charts_from_scalar_mesh_row_fit/.
The original file names are recorded beside each adapted group below. -/

/-!
# The density transform of normalized problems

`map_withDensity_of_map_eq_smul`: pushing a density measure through a measurable
equivalence that rescales the base measure. The observation base change as a measurable
equivalence `Frame.obsEquiv` (inverse `obsBaseInv`), its effect on `volume.prod count`, and
`Frame.normalized_obs_density`, the exact transform of paper (2.15): the normalized
observation law has density `(ν(A₀) q)⁻¹ |det obsMatrix|⁻¹ h ∘ Φ⁻¹`, with `h` the density of
the chart's original observation law at the composed width (`|det obsMatrix|⁻¹ = q |det D|`).
-/
namespace Submission.Obl.k4_remainder_angular_cap_transport.Geometry
open MeasureTheory MvPolynomial

theorem map_withDensity_of_map_eq_smul {α : Type*} [MeasurableSpace α] (ρ : Measure α)
    (e : α ≃ᵐ α) (c : ENNReal) (he : Measure.map e ρ = c • ρ) (h : α → ENNReal)
    (hh : Measurable h) :
    Measure.map e (ρ.withDensity h) = ρ.withDensity (fun y => c * h (e.symm y)) := by
  ext S hS
  rw [Measure.map_apply e.measurable hS, withDensity_apply _ (e.measurable hS),
    withDensity_apply _ hS]
  have key : ∫⁻ y in S, h (e.symm y) ∂(Measure.map e ρ) = ∫⁻ x in e ⁻¹' S, h x ∂ρ := by
    rw [e.restrict_map, lintegral_map_equiv]
    simp
  rw [he, Measure.restrict_smul, lintegral_smul_measure] at key
  rw [← key, smul_eq_mul]
  exact (lintegral_const_mul c (hh.comp e.symm.measurable)).symm

namespace Frame
variable (F : Frame)

/-- The inverse observation base change: `t = t₀ + q τ`, `y = c + t u + D z`. -/
noncomputable def obsBaseInv (v : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![F.t₀ + F.q * v 0,
    F.c 0 + (F.t₀ + F.q * v 0) * F.u 0 + (F.D 0 0 * v 1 + F.D 0 1 * v 2),
    F.c 1 + (F.t₀ + F.q * v 0) * F.u 1 + (F.D 1 0 * v 1 + F.D 1 1 * v 2)]

theorem obsBaseInv_obsBase (hq : F.q ≠ 0) (hD : IsUnit F.D.det) (v : EuclideanSpace ℝ (Fin 3)) :
    F.obsBaseInv (F.obsBase v) = v := by
  have hm : F.D * F.D⁻¹ = 1 := Matrix.mul_nonsing_inv F.D hD
  have h00 : F.D 0 0 * F.D⁻¹ 0 0 + F.D 0 1 * F.D⁻¹ 1 0 = 1 := by
    have := congrFun (congrFun hm 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : F.D 0 0 * F.D⁻¹ 0 1 + F.D 0 1 * F.D⁻¹ 1 1 = 0 := by
    have := congrFun (congrFun hm 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : F.D 1 0 * F.D⁻¹ 0 0 + F.D 1 1 * F.D⁻¹ 1 0 = 0 := by
    have := congrFun (congrFun hm 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : F.D 1 0 * F.D⁻¹ 0 1 + F.D 1 1 * F.D⁻¹ 1 1 = 1 := by
    have := congrFun (congrFun hm 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  ext i
  fin_cases i <;> simp [obsBaseInv, obsBase] <;> field_simp
  · ring
  · linear_combination (v 1 - F.c 0 - v 0 * F.u 0) * h00 + (v 2 - F.c 1 - v 0 * F.u 1) * h01
  · linear_combination (v 1 - F.c 0 - v 0 * F.u 0) * h10 + (v 2 - F.c 1 - v 0 * F.u 1) * h11

theorem obsBase_obsBaseInv (hq : F.q ≠ 0) (hD : IsUnit F.D.det) (v : EuclideanSpace ℝ (Fin 3)) :
    F.obsBase (F.obsBaseInv v) = v := by
  have hm : F.D⁻¹ * F.D = 1 := Matrix.nonsing_inv_mul F.D hD
  have h00 : F.D⁻¹ 0 0 * F.D 0 0 + F.D⁻¹ 0 1 * F.D 1 0 = 1 := by
    have := congrFun (congrFun hm 0) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h01 : F.D⁻¹ 0 0 * F.D 0 1 + F.D⁻¹ 0 1 * F.D 1 1 = 0 := by
    have := congrFun (congrFun hm 0) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h10 : F.D⁻¹ 1 0 * F.D 0 0 + F.D⁻¹ 1 1 * F.D 1 0 = 0 := by
    have := congrFun (congrFun hm 1) 0; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have h11 : F.D⁻¹ 1 0 * F.D 0 1 + F.D⁻¹ 1 1 * F.D 1 1 = 1 := by
    have := congrFun (congrFun hm 1) 1; simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  ext i
  fin_cases i <;> simp [obsBaseInv, obsBase] <;> field_simp
  · linear_combination v 1 * h00 + v 2 * h01
  · linear_combination v 1 * h10 + v 2 * h11


theorem measurable_obsBaseInv : Measurable F.obsBaseInv := by
  unfold obsBaseInv
  refine (PiLp.volume_preserving_toLp (Fin 3)).measurable.comp ?_
  refine measurable_pi_iff.mpr fun i => ?_
  fin_cases i <;> simp <;> fun_prop

/-- The base change of observations, with the bin kept, as a measurable equivalence. -/
noncomputable def obsEquiv (hq : F.q ≠ 0) (hD : IsUnit F.D.det) :
    (EuclideanSpace ℝ (Fin 3) × ℤ) ≃ᵐ (EuclideanSpace ℝ (Fin 3) × ℤ) where
  toFun := Prod.map F.obsBase id
  invFun := Prod.map F.obsBaseInv id
  left_inv z := by
    show (F.obsBaseInv (F.obsBase z.1), z.2) = z
    rw [F.obsBaseInv_obsBase hq hD]
  right_inv z := by
    show (F.obsBase (F.obsBaseInv z.1), z.2) = z
    rw [F.obsBase_obsBaseInv hq hD]
  measurable_toFun := F.measurable_obsBase.prodMap measurable_id
  measurable_invFun := F.measurable_obsBaseInv.prodMap measurable_id

theorem map_obsEquiv (hq : F.q ≠ 0) (hD : IsUnit F.D.det) :
    Measure.map (F.obsEquiv hq hD) ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
      (Measure.count : Measure ℤ)) =
      ENNReal.ofReal |F.obsMatrix.det|⁻¹ • (volume.prod Measure.count) := by
  show Measure.map (Prod.map F.obsBase id) _ = _
  rw [← Measure.map_prod_map _ _ F.measurable_obsBase measurable_id, F.map_obsBase_volume hq hD,
    Measure.map_id, Measure.prod_smul_left]

/-- **The density transform** (paper (2.15)): the normalized observation law has density
`(ν(A₀) q)⁻¹ |det obsMatrix|⁻¹ h ∘ Φ⁻¹`, where `h` is the density of the original
observation law of the chart's selected incidences at the composed width. -/
theorem normalized_obs_density (hq : 0 < F.q) (hD : IsUnit F.D.det) (ν : Measure Trajectory)
    [IsFiniteMeasure ν] {A₀ : Set Trajectory} {E : Set Incidence} (hA : MeasurableSet A₀)
    (hE : MeasurableSet E) (hsub : ∀ p ∈ E, p.1 ∈ A₀ ∧ p.2 ∈ Set.Icc F.t₀ (F.t₀ + F.q))
    (B δ a : ℝ) (hδ : δ ≠ 0) (h : EuclideanSpace ℝ (Fin 3) × ℤ → ENNReal) (hh : Measurable h)
    (hlaw : Measure.map (obs B (δ * a)) ((ν.prod volume).restrict E) =
      (volume.prod Measure.count).withDensity h) :
    Measure.map (obs (B / δ) a) ((((ν A₀)⁻¹ • Measure.map F.normTraj (ν.restrict A₀)).prod
        volume).restrict (F.normEvent A₀ E)) =
      (volume.prod Measure.count).withDensity (fun z => (ν A₀ * ENNReal.ofReal F.q)⁻¹ *
        (ENNReal.ofReal |F.obsMatrix.det|⁻¹ * h ((F.obsEquiv hq.ne' hD).symm z))) := by
  rw [F.normalized_obs_law hq hD ν hA hE hsub B δ a hδ, hlaw]
  have := map_withDensity_of_map_eq_smul (volume.prod Measure.count) (F.obsEquiv hq.ne' hD)
    _ (F.map_obsEquiv hq.ne' hD) h hh
  have hcoe : ((F.obsEquiv hq.ne' hD) : (EuclideanSpace ℝ (Fin 3) × ℤ) →
      (EuclideanSpace ℝ (Fin 3) × ℤ)) = Prod.map F.obsBase id := rfl
  rw [hcoe] at this
  rw [this, ← withDensity_smul _ (by
    exact measurable_const.mul (hh.comp (F.obsEquiv hq.ne' hD).symm.measurable))]
  rfl

end Frame
end Submission.Obl.k4_remainder_angular_cap_transport.Geometry
