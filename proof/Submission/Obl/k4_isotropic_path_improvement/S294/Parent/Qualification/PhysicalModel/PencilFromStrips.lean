-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.PhysicalModel.PencilFromStrips, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.StripFrame
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Switch.StripBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.FiniteStates

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel

open Set MeasureTheory
open scoped ENNReal RealInnerProductSpace Pointwise

noncomputable section

/-- Rescaling a vector does not change its linear subspace. -/
private theorem smul_submodule_set {c : ℝ} (hc : c≠0)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) : c • (V : Set (EuclideanSpace ℝ (Fin 3)))=(V : Set (EuclideanSpace ℝ (Fin 3))) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact V.smul_mem c hy
  · intro hx
    exact ⟨c⁻¹ • x,V.smul_mem c⁻¹ hx,smul_inv_smul₀ hc x⟩

/-- A near-pencil of normalized lifted directions is contained in one
planar velocity strip. The normalization costs one extra `U+1` factor. -/
theorem normalized_lift_near_subspace_subset_strip
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))) (hV : Module.finrank ℝ V<3)
    {U width δ : ℝ} (hU : 0≤U) (hδ : 0≤δ)
    (hwidth : 2*(U+1)*((U+1)*δ)≤width) (hsmall : (U+1)*δ≤1/4) :
    ∃ (normal : EuclideanSpace ℝ (Fin 2)) (offset : ℝ), ‖normal‖=1 ∧
      ∀ velocity : EuclideanSpace ℝ (Fin 2), ‖velocity‖≤U →
        Metric.infDist (NativeAssigned.direction (Switch.liftDir velocity)) (V : Set _) < δ →
          |inner ℝ normal velocity-offset|≤width := by
  obtain ⟨normal,offset,hn,hsub⟩ := Switch.lift_near_subspace_subset_strip
    V hV U width ((U+1)*δ) hU (by positivity) hwidth hsmall
  refine ⟨normal,offset,hn,?_⟩
  intro velocity hv hnear
  apply hsub velocity hv
  have hne : Switch.liftDir velocity≠0 := by
    intro h
    have h0 := congrArg (fun x : EuclideanSpace ℝ (Fin 3) => x 0) h
    norm_num [Switch.liftDir] at h0
  have hnorm : ‖Switch.liftDir velocity‖≤U+1 := by
    have hsq := Switch.norm_sq_three (Switch.liftDir velocity)
    have hv2 := Switch.norm_sq_two velocity
    change ‖Switch.liftDir velocity‖^2=(1:ℝ)^2+velocity 0^2+velocity 1^2 at hsq
    norm_num only [one_pow] at hsq
    nlinarith [norm_nonneg velocity,norm_nonneg (Switch.liftDir velocity)]
  have hnorm0 : 0<‖Switch.liftDir velocity‖ := norm_pos_iff.mpr hne
  have heq : Switch.liftDir velocity=
      ‖Switch.liftDir velocity‖ • NativeAssigned.direction (Switch.liftDir velocity) := by
    simp only [NativeAssigned.direction,smul_smul,mul_inv_cancel₀ hnorm0.ne',one_smul]
  have hdist : Metric.infDist (Switch.liftDir velocity) (V : Set _)=
      ‖Switch.liftDir velocity‖*
        Metric.infDist (NativeAssigned.direction (Switch.liftDir velocity)) (V : Set _) := by
    conv_lhs => rw [heq]
    rw [←smul_submodule_set hnorm0.ne' V,
      infDist_smul₀ hnorm0.ne',Real.norm_eq_abs,abs_of_pos hnorm0,
      smul_submodule_set hnorm0.ne' V]
  rw [hdist]
  exact (mul_lt_mul_of_pos_left hnear hnorm0).trans_le
    (mul_le_mul_of_nonneg_right hnorm hδ)

/-- The actual two affine velocity coefficients used by scalar support. -/
def planarVelocityVector (p : PhysicalModel) (l : Ln) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![p.scalarCoefficients l 4,p.scalarCoefficients l 6]

theorem lift_planarVelocityVector (p : PhysicalModel) (l : Ln) :
    Switch.liftDir (p.planarVelocityVector l)=p.baseVelocityVector l := rfl

theorem planarVelocityVector_bound (p : PhysicalModel) {H : ℝ} (hH : 0≤H)
    (hc : ∀ l, |p.scalarCoefficients l 4|≤H ∧ |p.scalarCoefficients l 6|≤H) (l : Ln) :
    ‖p.planarVelocityVector l‖≤2*H := by
  have hs := Switch.norm_sq_two (p.planarVelocityVector l)
  change ‖p.planarVelocityVector l‖^2=
    (p.scalarCoefficients l 4)^2+(p.scalarCoefficients l 6)^2 at hs
  have h0 := (abs_le.mp (hc l).1)
  have h1 := (abs_le.mp (hc l).2)
  have hc0 : (p.scalarCoefficients l 4)^2≤H^2 := sq_le_sq' h0.1 h0.2
  have hc1 : (p.scalarCoefficients l 6)^2≤H^2 := sq_le_sq' h1.1 h1.2
  nlinarith [norm_nonneg (p.planarVelocityVector l)]

/-- Current statewise planar strip caps construct the precise normalized
pencil premise used by the original scalar-support preparation. The
state, incidence measure and denominator remain unchanged. -/
theorem pencil_bound_of_current_strip_caps (p : PhysicalModel) (μ : Measure Ev)
    {b U width δ failure : ℝ} (hU : 0≤U) (hδ : 0≤δ)
    (hwidth : 2*(U+1)*((U+1)*δ)≤width) (hsmall : (U+1)*δ≤1/4)
    (hvelocity : ∀ᵐ z ∂μ, ‖p.planarVelocityVector z.1‖≤U)
    (hstrip : ∀ q (normal : EuclideanSpace ℝ (Fin 2)) offset, ‖normal‖=1 →
      μ {z | p.physicalState b z=q ∧
        |inner ℝ normal (p.planarVelocityVector z.1)-offset|≤width} ≤
          ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q})) :
    ∀ q (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ V<3 →
      μ {z | p.physicalState b z=q ∧
        Metric.infDist (NativeAssigned.direction (p.baseVelocityVector z.1)) (V : Set _) < δ} ≤
          ENNReal.ofReal failure*μ ((p.physicalState b) ⁻¹' {q}) := by
  intro q V hV
  obtain ⟨normal,offset,hn,hsub⟩ := normalized_lift_near_subspace_subset_strip
    V hV hU hδ hwidth hsmall
  apply le_trans (measure_mono_ae ?_) (hstrip q normal offset hn)
  filter_upwards [hvelocity] with z hz
  intro hnear
  refine ⟨hnear.1,hsub (p.planarVelocityVector z.1) hz ?_⟩
  rw [lift_planarVelocityVector]
  exact hnear.2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel
