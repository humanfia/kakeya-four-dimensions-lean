-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.Jets2.DurationRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/Jets2/DurationRows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit 2f02dabfaa4891833d78772b63f6d98e404e9c6c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/Jets2/DurationRows.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.CoarseDuration
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.CurvatureRows
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AssignedGridGeometry
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FiniteStateLaws

/-! # Physical velocity rows paid by an earlier original coarse cell -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open MeasureTheory Set Broad.Velocity
open Submission.Obl.k4_initial_horizon_bound
noncomputable section

/-- The model, retained original prior, and its cap are constructed from
an earlier duration witness. Only literal source geometry, counting,
breadth and numerical scales remain as inputs. -/
theorem coefficient_duration_rows {Λ : Type} [MeasurableSpace Λ]
    (ν : Measure Λ) [IsFiniteMeasure ν] (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (earlier current : Set (Λ×ℝ)) (hearlier : MeasurableSet earlier)
    (hearlierTime : earlier ⊆ univ×ˢ Icc (0:ℝ) 1)
    (hcurrent : MeasurableSet current) (hcurrentTime : current ⊆ univ×ˢ Icc (0:ℝ) 1)
    {coarse : ℝ} (hcoarse : 0 < coarse) (coarseCell : Fin 4 → ℤ)
    {H K baseMesh hidden lossRate liftRho baseRho fraction baseFraction dimension ε : ℝ}
    (hH : 1 ≤ H)
    (hjets : ∀ l, |c l 1| ≤ H ∧ |c l 2| ≤ H ∧ |c l 4| ≤ H ∧ |c l 6| ≤ H)
    (hK : 6*H ≤ K) (hbase : 0 < baseMesh) (hbaseHidden : baseMesh ≤ hidden)
    (hshape : coarse = hidden^((2:ℝ)/3)) (hRate : 0 < lossRate)
    (hRateK : lossRate⁻¹ ≤ K) (hlift : 0 < liftRho) (hbaseRho : 0 ≤ baseRho)
    (hfraction : 0 < fraction) (hfrac : fraction < baseFraction) (hε : 0 ≤ ε)
    (hquad : 8*K*coarse^2 < hidden) (hdir : 32*K*coarse ≤ liftRho/2)
    (hconditioned : 1 ≤ K*baseRho^3) (hsmall : 36*K^3*(K*liftRho) ≤ 1)
    (hbudget : 256*curvatureRowConstant^3*K^9*hidden^((1-dimension)/3) ≤
      (fraction*liftRho/4)^4*ε^4)
    {n : ℕ} (cell : Fin n → Fin 4 → ℤ) (hinj : Function.Injective cell)
    (code : Λ×ℝ → Fin n) (hcode : Measurable code)
    (hcount : (n:ℝ) ≤ K*(coarse/baseMesh)^3*(coarse/hidden)^dimension)
    (hcell : ∀ z ∈ current, cell (code z)=coefficientGridCode c baseMesh hidden z)
    (hcoarseCell : ∀ z ∈ current, coefficientGridCode c coarse coarse z=coarseCell)
    (hlong : ∀ z ∈ current, ENNReal.ofReal (lossRate*coarse) ≤
      incidenceDuration
        (earlier∩coefficientGridCode c coarse coarse ⁻¹' {coarseCell}) z.1)
    (hbroad : ∀ i, cellBroad ((ν.prod volume).restrict current) code
      (fun z => coefficientBase (c z.1)) baseRho baseFraction i) :
    ∃ (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (kept : Set (Λ×ℝ)),
      Measurable row ∧ MeasurableSet kept ∧ kept ⊆ current ∧
      (∀ q j, |row q j| ≤ 28*K^6) ∧
      ((ν.prod volume).restrict current).real keptᶜ ≤
        ε*((ν.prod volume).restrict earlier).real
          (coefficientGridCode c coarse coarse ⁻¹' {coarseCell})+
        fraction*((ν.prod volume).restrict current).real univ ∧
      ∀ z ∈ kept,
        |(c z.1 1+2*c z.1 2*z.2)-
          (row (coefficientGridCode c baseMesh hidden z) 0+
            row (coefficientGridCode c baseMesh hidden z) 1*c z.1 4+
            row (coefficientGridCode c baseMesh hidden z) 2*c z.1 6)| ≤
          80*K^7*liftRho := by
  let coarseCode := coefficientGridCode c coarse coarse
  let fineCode := coefficientGridCode c baseMesh hidden
  let long := {l | ENNReal.ofReal (lossRate*coarse) ≤
    incidenceDuration (earlier∩coarseCode ⁻¹' {coarseCell}) l}
  let prior := ν.restrict long
  let M := ((ν.prod volume).restrict earlier).real (coarseCode ⁻¹' {coarseCell})
  let anchor := coarse*((coarseCell 0:ℝ)+1/2)
  have hinc : (prior.prod volume).restrict current=(ν.prod volume).restrict current :=
    restrict_prior_incidence_eq ν long current hcurrent
      (fun z hz => ⟨hlong z hz,mem_univ _⟩)
  have hprior : prior.real univ ≤ K*M/hidden^((2:ℝ)/3) := by
    have hh := coefficient_duration_prior_cap ν c hc earlier hearlier hearlierTime
      hcoarse hRate coarseCell
    change prior.real univ ≤ _ at hh
    rw [←hshape]
    calc
      _ ≤ M/(lossRate*coarse) := hh
      _ = lossRate⁻¹*M/coarse := by ring
      _ ≤ K*M/coarse := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hRateK measureReal_nonneg) hcoarse.le
  have hsupport (z : Λ×ℝ) (hz : z ∈ current) :
      |z.2-anchor| ≤ coarse ∧ baseMesh⁻¹ • heightScale (baseMesh/hidden)
        (coefficientPhysical (c z.1) z.2) ∈
          Submission.Obl.k4_mk_grid_transfer.latticeCell (cell (code z)) := by
    refine ⟨?_,?_⟩
    · apply time_window_of_floor_code hcoarse (coarseCell 0)
      have hh := congrFun (hcoarseCell z hz) 0
      change ⌊z.2/(if (0:Fin 4)=3 then coarse else coarse)⌋=coarseCell 0 at hh
      simpa only [ite_self] using hh
    · rw [hcell z hz]
      exact anisotropic_point_mem_latticeCell hbase (hbase.trans_le hbaseHidden) _
  have hcount' : (n:ℝ) ≤ K*(hidden^((2:ℝ)/3)/baseMesh)^3*
      (hidden^((2:ℝ)/3)/hidden)^dimension := by
    simpa only [←hshape] using hcount
  have hbroad' : ∀ i, cellBroad ((prior.prod volume).restrict current) code
      (fun z => coefficientBase (c z.1)) baseRho baseFraction i := by
    rw [hinc]
    exact hbroad
  have ha := coefficientVelocityModel_curvature_valid prior c hc hcurrent hcurrentTime
    cell hinj code hcode hH hjets hK hbase hbaseHidden hlift hbaseRho hfraction.le hfrac
    hquad hdir hsupport hprior hcount' hbroad' hconditioned hsmall
  obtain ⟨row,kept,hrow,hkept,hsub,hbound,hloss,hfit⟩ :=
    coefficient_velocity_rows_of_curvature prior c hcurrent cell code anchor coarse K
      hidden baseMesh liftRho baseRho fraction baseFraction M dimension ha
      measureReal_nonneg hfraction hε hbudget fineCode hcell
  rw [hinc] at hloss
  exact ⟨row,kept,hrow,hkept,hsub,hbound,hloss,hfit⟩

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
