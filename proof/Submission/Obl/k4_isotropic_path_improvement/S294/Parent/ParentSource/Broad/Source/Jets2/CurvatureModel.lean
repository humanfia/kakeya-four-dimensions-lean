-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.Jets2.CurvatureModel, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/Jets2/CurvatureModel.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 2f02dabfaa4891833d78772b63f6d98e404e9c6c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/Jets2/CurvatureModel.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.VelocityModel
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CurvatureVelocityGraph

/-! # The physical coefficient model with arbitrary intercepts -/
set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open MeasureTheory Set MvPolynomial
open SourceGeometry Broad.Velocity
open Submission.Obl.k4_mk_grid_transfer
open scoped ENNReal
noncomputable section
variable {Λ : Type*} [MeasurableSpace Λ]

/-- Every analytic input to the velocity backend is derived from the
same coefficient table. There is no old-test value or gradient premise. -/
theorem coefficientVelocityModel_curvature_valid (ν : Measure Λ) [IsFiniteMeasure ν]
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    {E : Set (Λ×ℝ)} (hE : MeasurableSet E) (ht : E⊆univ×ˢ Icc (0:ℝ) 1)
    {n : ℕ} (cell : Fin n → Fin 4 → ℤ) (hinj : Function.Injective cell)
    (code : Λ×ℝ → Fin n) (hcode : Measurable code)
    {H anchor window K mesh baseMesh liftRho baseRho fraction baseFraction priorScale dimension : ℝ}
    (hH : 1 ≤ H) (hjets : ∀ l, |c l 1|≤H ∧ |c l 2|≤H ∧ |c l 4|≤H ∧ |c l 6|≤H) (hK : 6*H≤K)
    (hbase : 0 < baseMesh) (hmesh : baseMesh ≤ mesh) (hlift : 0 < liftRho)
    (hbaseRho : 0 ≤ baseRho) (hfraction : 0 ≤ fraction) (hfrac : fraction<baseFraction)
    (htangent : 8*K*window^2 < mesh) (hdir : 32*K*window≤liftRho/2)
    (hsupport : ∀ z∈E, |z.2-anchor|≤window ∧
      baseMesh⁻¹ • heightScale (baseMesh/mesh) (coefficientPhysical (c z.1) z.2)∈
        latticeCell (cell (code z)))
    (hprior : ν.real univ≤K*priorScale/mesh^((2:ℝ)/3))
    (hcount : (n:ℝ)≤K*(mesh^((2:ℝ)/3)/baseMesh)^3*(mesh^((2:ℝ)/3)/mesh)^dimension)
    (hbroad : ∀ i, cellBroad ((ν.prod volume).restrict E) code
      (fun z => coefficientBase (c z.1)) baseRho baseFraction i)
    (hconditioned : 1≤K*baseRho^3) (hsmall : 36*K^3*(K*liftRho)≤1) :
    (coefficientVelocityModel ν c E cell code anchor window K mesh baseMesh liftRho
      baseRho fraction baseFraction priorScale dimension).CurvatureValid := by
  let a := coefficientVelocityModel ν c E cell code anchor window K mesh baseMesh liftRho
    baseRho fraction baseFraction priorScale dimension
  have hinc : a.incidence=(ν.prod volume).restrict E :=
    coefficientVelocityModel_incidence ν c hE cell code _ _ _ _ _ _ _ _ _ _ _
  have hfinite : IsFiniteMeasure a.incidence := by
    constructor
    rw [hinc,Measure.restrict_apply_univ]
    apply lt_of_le_of_lt (measure_mono ht)
    rw [Measure.prod_prod,Real.volume_Icc]
    simp only [sub_zero,ENNReal.ofReal_one,mul_one]
    exact measure_lt_top ν univ
  have hHK : H≤K := by linarith
  have hK1 : 1≤K := by linarith
  have hH0 : 0≤H := zero_le_one.trans hH
  change a.CurvatureValid
  refine {
    priorFinite := by change IsFiniteMeasure ν; infer_instance
    incidenceFinite := hfinite
    cellInjective := hinj
    weightMeas := measurable_const.indicator hE
    codeMeas := hcode
    bound_ge := hK1
    mesh_pos := hbase
    mesh_ge := hmesh
    liftRho_pos := hlift
    baseRho_nonneg := hbaseRho
    fraction_nonneg := hfraction
    fraction_lt := hfrac
    timeVelocity := fun _ => rfl
    quadratic := fun l t => coefficient_quadratic (c l) t
    curvature := ?_
    anchorMeas := ?_
    tangentMeas := ?_
    directionMeas := ?_
    tangentError := htangent
    directionError := hdir
    density := ?_
    support := ?_
    priorCap := hprior
    supportCount := hcount
    boundedMeas := MeasurableSet.univ.prod measurableSet_Icc
    boundedFull := ?_
    baseBound := ?_
    scalarBound := ?_
    rawBound := ?_
    baseBroad := ?_
    conditioned := hconditioned
    small := hsmall }
  · intro l
    change |c l 2| ≤ 8*K
    exact (hjets l).2.1.trans (by linarith : H ≤ 8*K)
  · have hm : Measurable (fun l : Λ => coefficientPhysical (c l) anchor) :=
      (measurable_coefficientPhysical hc).comp
        (measurable_id.prodMk (measurable_const (a := anchor)))
    change Measurable (fun l => baseMesh⁻¹ • heightScale (baseMesh/mesh)
      (nativePhysicalCurve (coefficientTest (c l)) (coefficientPosition (c l))
        (coefficientVelocity (c l)) anchor))
    simp_rw [coefficient_physical_eq_native]
    exact ((measurable_heightScale (baseMesh/mesh)).comp hm).const_smul (baseMesh⁻¹)
  · exact (measurable_coefficientTangent hc).comp (measurable_id.prodMk measurable_const)
  · change Measurable (fun z : Λ×ℝ => unitTangent (coefficientTangent (c z.1) z.2))
    exact measurable_unitTangent (measurable_coefficientTangent hc)
  · intro l t
    change E.indicator (fun _ => (1:ENNReal)) (l,t) ≤ ENNReal.ofReal K
    exact (Set.indicator_le_self E (fun _ => (1:ENNReal)) (l,t)).trans
      (by simpa using ENNReal.ofReal_le_ofReal hK1)
  · intro l t hw
    have hz : (l,t)∈E := by
      by_contra hh
      simp only [a,coefficientVelocityModel,Set.indicator_of_notMem hh,ne_eq,
        not_true_eq_false] at hw
    change |t-anchor|≤window ∧ baseMesh⁻¹ • heightScale (baseMesh/mesh)
      (nativePhysicalCurve (coefficientTest (c l)) (coefficientPosition (c l))
        (coefficientVelocity (c l)) t)∈latticeCell (cell (code (l,t)))
    rw [coefficient_physical_eq_native]
    exact hsupport (l,t) hz
  · rw [hinc]
    change ((ν.prod volume).restrict E) (univ×ˢ Icc (0:ℝ) 1)ᶜ=0
    rw [Measure.restrict_apply (MeasurableSet.univ.prod measurableSet_Icc).compl]
    have heq : (univ×ˢ Icc (0:ℝ) 1)ᶜ∩E=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      exact hz.1 (ht hz.2)
    rw [heq,measure_empty]
  · intro z hz j
    change |coefficientBase (c z.1) j|≤K
    fin_cases j
    · simpa [coefficientBase,coefficientVelocity] using hK1
    · exact ((hjets z.1).2.2.1).trans hHK
    · exact ((hjets z.1).2.2.2).trans hHK
  · intro z hz
    exact (coefficient_rate_bound_of_jets hH0 (hjets z.1).1 (hjets z.1).2.1 hz.2).trans (by linarith : 3*H≤K)
  · intro z hz
    exact (coefficient_tangent_bound_of_jets hH (hjets z.1).1 (hjets z.1).2.1
      (hjets z.1).2.2.1 (hjets z.1).2.2.2 hz.2).trans hK
  · rw [hinc]
    exact hbroad

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
