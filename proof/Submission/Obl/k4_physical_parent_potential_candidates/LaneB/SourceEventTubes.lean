import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourcePotentialJets
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.EventTubes

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set MeasureTheory MvPolynomial PhysicalPotentialData

noncomputable section

namespace SourceNormalization

/-- Isotropic physical base normalization and zoom leave every actual
planar line velocity unchanged. -/
theorem lineDir_source_matrix (T:ℕ) (s lam:ℝ) (l:Ln) :
    Analytic.lineDir (lam • matrix T s) l =
      (lam/(scale T s)) • Analytic.GeneralPositionSampling.lift (v l) := by
  ext i
  fin_cases i <;>
    simp [Analytic.lineDir,matrix,Matrix.smul_apply,Matrix.one_apply,
      Analytic.GeneralPositionSampling.lift,v,div_eq_mul_inv] <;> ring

theorem lineDir_source_zero (T:ℕ) (s lam:ℝ) (l:Ln) :
    Analytic.lineDir (lam • matrix T s) l 0 = lam/(scale T s) := by
  rw [lineDir_source_matrix]
  simp [Analytic.GeneralPositionSampling.lift]

theorem lineVelocity_source_matrix (T:ℕ) {s lam:ℝ} (hs:0<s) (hlam:0<lam) (l:Ln) :
    Analytic.lineVelocity (lam • matrix T s) l = v l := by
  have hscale := (scale_pos T hs).ne'
  have hlam0 := hlam.ne'
  ext i
  fin_cases i <;>
    simp [Analytic.lineVelocity,lineDir_source_matrix,
      Analytic.GeneralPositionSampling.lift,v] <;> field_simp

theorem norm_lift_velocity (v0:P2) :
    ‖Analytic.GeneralPositionSampling.lift v0‖ ≤ 1+2*‖v0‖ := by
  have h0 : |v0 0|≤‖v0‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v0 0
  have h1 : |v0 1|≤‖v0‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le v0 1
  calc
    _ ≤ ∑ i:Fin 3, |Analytic.GeneralPositionSampling.lift v0 i| :=
      Submission.Lib.K4NativePreparationNumerics.euclidean_norm_le_sum_abs _
    _ = 1+|v0 0|+|v0 1| := by simp [Fin.sum_univ_three,Analytic.GeneralPositionSampling.lift]
    _ ≤ 1+2*‖v0‖ := by linarith

/-- A physical group-point window gives the actual normalized tube through
an event in the original lifted direction, with its literal physical time
length. No line parameters or velocity palettes are supplied separately. -/
theorem certified_tube_of_physical_window
    (T j:ℕ) (c u:P2) {s lam B:ℝ} (hs:0<s) (hlam:0<lam) (hB:0<B)
    (b cz:Fin 3 → ℝ) (R0 Rc:Po) (Pot:MvPolynomial (Fin 3) ℝ)
    {εfit A₁ σ Vc At τw hδ K:ℝ} (e:Ev) (hAt:1≤At) (hvel:‖v e.1‖≤K)
    (hAtv:1+2*K≤At) (hhδ:0≤hδ)
    (hwindow:scale T s/(8*At*lam)≤τw)
    (hphys:∀t:ℝ,|t-e.2|≤τw → Analytic.PhysicalGroupPoint B⁻¹ R0 Rc Pot εfit A₁ σ Vc
      (Analytic.graphPoint e.1 t))
    (hZ:Analytic.normalizedBase (Analytic.zoomForwardShift (shift T j c u s b) cz lam)
      (lam • matrix T s) B (Analytic.graphPoint e.1 e.2)∈Metric.closedBall (0:P3) 1)
    (anchor:P3)
    (hclose:‖anchor-Analytic.normalizedBase
      (Analytic.zoomForwardShift (shift T j c u s b) cz lam) (lam • matrix T s) B
      (Analytic.graphPoint e.1 e.2)‖≤hδ) :
    Analytic.CertifiedTubeWitness
      (Analytic.transportPolynomial (Analytic.zoomShift (inverseShift T j c u s b)
        (inverseMatrix T s) cz) (Analytic.zoomMatrix (inverseMatrix T s) lam) B⁻¹ R0)
      (Analytic.basePullback (Analytic.zoomShift (inverseShift T j c u s b)
        (inverseMatrix T s) cz) (Analytic.zoomMatrix (inverseMatrix T s) lam) Pot)
      (Analytic.transportPolynomial (Analytic.zoomShift (inverseShift T j c u s b)
        (inverseMatrix T s) cz) (Analytic.zoomMatrix (inverseMatrix T s) lam) B⁻¹ Rc)
      εfit A₁ σ Vc At 1 hδ anchor (Analytic.GeneralPositionSampling.lift (v e.1)) := by
  have hscale : 0<scale T s := scale_pos T hs
  have hAt0 : 0<At := by linarith
  have hinv := inverse T j c u hs b
  have hzinv := Analytic.zoomForward_inverse hinv.1 hinv.2 cz hlam.ne'
  have hD0 : 0<Analytic.lineDir (lam • matrix T s) e.1 0 := by
    rw [lineDir_source_zero]
    exact div_pos hlam hscale
  have hτ : (8*At*Analytic.lineDir (lam • matrix T s) e.1 0)⁻¹≤τw := by
    rw [lineDir_source_zero]
    convert hwindow using 1
    field_simp
  have hLift : ‖Analytic.GeneralPositionSampling.lift
      (Analytic.lineVelocity (lam • matrix T s) e.1)‖≤At := by
    rw [lineVelocity_source_matrix T hs hlam]
    exact (norm_lift_velocity (v e.1)).trans ((by linarith : 1+2*‖v e.1‖≤1+2*K).trans hAtv)
  have hx := Analytic.certifiedTube_of_event hzinv.1 hzinv.2 (inv_mul_cancel₀ hB.ne') e
    hD0 hτ hphys hZ hAt hLift anchor hclose hhδ
  simpa only [lineVelocity_source_matrix T hs hlam] using hx

/-- The literal physical source, its whole-block own fit and clock-interior
window instantiate the preceding tube, with the physical parent itself as
the auxiliary certificate. -/
theorem certified_tube_of_source_window {q T j:ℕ} {ν:Measure Ln} {B a ζ d:ℝ}
    {c u:P2} {P0:Po} {A:Set Ln} {F H:Set Ev}
    (source:PhysicalSource q ν B a ζ d T j c u P0 A F H)
    (hP0:P0.totalDegree≤2) (hB:0<B) (hj:j<2^T) {w:ℝ} (hw:0<w) (hζw:ζ≤w)
    (g:ℤ) (β:Bool) (e:Ev) (he:e∈source.S) (hl:e.1∈source.groupLines w g)
    (htime:e.2∈Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹))
    (hβ:parentBranch P0 e=β) {s lam At τw hδ:ℝ} (hs:0<s) (hlam:0<lam)
    (b cz:Fin 3 → ℝ) (hAt:1≤At) (hAtv:1+2*source.K≤At) (hhδ:0≤hδ)
    (hτreg:τw≤(48*source.K^2)⁻¹) (hwindow:scale T s/(8*At*lam)≤τw)
    (hτold:∀t:ℝ,|t-e.2|≤τw →
      t∈Icc ((j:ℝ)*((2:ℝ)^T)⁻¹) (((j:ℝ)+1)*((2:ℝ)^T)⁻¹))
    (hZ:Analytic.normalizedBase (Analytic.zoomForwardShift (shift T j c u s b) cz lam)
      (lam • matrix T s) B (Analytic.graphPoint e.1 e.2)∈Metric.closedBall (0:P3) 1)
    (anchor:P3)
    (hclose:‖anchor-Analytic.normalizedBase
      (Analytic.zoomForwardShift (shift T j c u s b) cz lam) (lam • matrix T s) B
      (Analytic.graphPoint e.1 e.2)‖≤hδ) :
    Analytic.CertifiedTubeWitness
      (Analytic.transportPolynomial (Analytic.zoomShift (inverseShift T j c u s b)
        (inverseMatrix T s) cz) (Analytic.zoomMatrix (inverseMatrix T s) lam) B⁻¹
        (P0-C (physicalGroupCenter a w g)))
      (zoomPotential T j c u s b cz lam source.Pot)
      (Analytic.transportPolynomial (Analytic.zoomShift (inverseShift T j c u s b)
        (inverseMatrix T s) cz) (Analytic.zoomMatrix (inverseMatrix T s) lam) B⁻¹ P0)
      (2*a*w) (2*source.K) (branchSign β) source.K At 1 hδ anchor
      (Analytic.GeneralPositionSampling.lift (v e.1)) := by
  apply certified_tube_of_physical_window T j c u hs hlam hB b cz
    (P0-C (physicalGroupCenter a w g)) P0 (Broad.parentPotentialPullback T j c u source.Pot)
    e hAt (source.point_bounds e he).2.1 hAtv hhδ hwindow ?_ hZ anchor hclose
  intro t ht
  exact source.physical_group_point_near hP0 hB hj hw hζw e he hl htime hβ
    (hτold t ht) (ht.trans hτreg)

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
