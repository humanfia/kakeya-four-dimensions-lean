-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.Jets2.CurvatureRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/Jets2/CurvatureRows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 2f02dabfaa4891833d78772b63f6d98e404e9c6c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/Jets2/CurvatureRows.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.CurvatureModel
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.CurvatureLiteralRows

/-! # Physical velocity rows for the coefficient model -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open MeasureTheory Set Broad.Velocity
noncomputable section

/-- The checked physical MK4 model returns rows for the actual derivative
of the supplied coefficient signal. The bad-cell moment is charged to
the earlier full-prior scale; the kept source is an original event subset. -/
theorem coefficient_velocity_rows_of_curvature {Λ : Type} [MeasurableSpace Λ]
    (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) {E : Set (Λ×ℝ)} (hE : MeasurableSet E)
    {n : ℕ} (cell : Fin n → Fin 4 → ℤ) (code : Λ×ℝ → Fin n)
    (anchor window K mesh baseMesh liftRho baseRho fraction baseFraction priorScale dimension : ℝ)
    (ha : (coefficientVelocityModel ν c E cell code anchor window K mesh baseMesh liftRho
      baseRho fraction baseFraction priorScale dimension).CurvatureValid)
    (hprior : 0 ≤ priorScale) (hfraction : 0 < fraction) {ε : ℝ} (hε : 0 ≤ ε)
    (hbudget : 256*curvatureRowConstant^3*K^9*mesh^((1-dimension)/3)≤
      (fraction*liftRho/4)^4*ε^4)
    (state : Λ×ℝ → Fin 4 → ℤ) (hstate : ∀ z∈E, cell (code z)=state z) :
    ∃ (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (kept : Set (Λ×ℝ)),
      Measurable row ∧ MeasurableSet kept ∧ kept⊆E ∧
      (∀ q j, |row q j|≤28*K^6) ∧
      ((ν.prod volume).restrict E).real keptᶜ≤
        ε*priorScale+fraction*((ν.prod volume).restrict E).real univ ∧
      ∀ z∈kept,
        |(c z.1 1+2*c z.1 2*z.2)-
          (row (state z) 0+row (state z) 1*c z.1 4+row (state z) 2*c z.1 6)|≤
          80*K^7*liftRho := by
  let a := coefficientVelocityModel ν c E cell code anchor window K mesh baseMesh liftRho
    baseRho fraction baseFraction priorScale dimension
  have hinc : a.incidence=(ν.prod volume).restrict E :=
    coefficientVelocityModel_incidence ν c hE cell code _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨row,T,hrowm,hT,hrow,hloss,hmoment,hfit⟩ :=
    curvature_literal_rows_fixed a ha state E (by
      intro z hz
      exact hstate z hz)
  have hbad : a.broadMass≤ε*priorScale := by
    apply bad_mass_le_of_quartic_remainder
      (coefficient := (fraction*liftRho/4)^4)
      (remainder := 256*curvatureRowConstant^3*K^9*mesh^((1-dimension)/3))
      measureReal_nonneg hprior
      (pow_pos (div_pos (mul_pos hfraction ha.liftRho_pos) (by norm_num)) 4) hε
    · exact hmoment.trans_eq (by dsimp [a,coefficientVelocityModel]; ring)
    · exact hbudget
  let kept := E∩T
  have hkeep : MeasurableSet kept := hE.inter hT
  have hmass : a.incidence.real keptᶜ=a.incidence.real Tᶜ := by
    apply congrArg ENNReal.toReal
    apply measure_congr
    rw [hinc]
    filter_upwards [ae_restrict_mem hE] with z hz
    simp only [kept,mem_compl_iff,mem_inter_iff,hz,true_and]
  refine ⟨row,kept,hrowm,hkeep,inter_subset_left,hrow,?_,?_⟩
  · rw [←hinc,hmass]
    exact hloss.trans (add_le_add hbad le_rfl)
  · intro z hz
    have hh := (hfit z ⟨hz.2,hz.1⟩).2
    change |(2*c z.1 2*z.2+c z.1 1)-
      ∑ j : Fin 3, row (state z) j*coefficientVelocity (c z.1) j.castSucc|≤_ at hh
    simpa [a,coefficientVelocityModel,Fin.sum_univ_three,coefficientVelocity,
      add_comm (2*c z.1 2*z.2) (c z.1 1)] using hh

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
