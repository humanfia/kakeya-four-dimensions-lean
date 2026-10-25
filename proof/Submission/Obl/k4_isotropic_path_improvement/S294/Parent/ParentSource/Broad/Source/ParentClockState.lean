-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentClockState, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentClockState.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit c1f30c34,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentClockState.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ClockStateCoarsening
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentMovingBandCap

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open MeasureTheory Set Native
open Submission.Lib.K4ParentSignalPreparation.Census
noncomputable section

/-- The physical parent measured in the old clock unit. -/
def clockParentSignal {W : ℕ} (p : PathData W) (old : Fin p.C)
    (P : MvPolynomial (Fin 4) ℝ) (z : Ev) : ℝ :=
  (2:ℝ)^p.T (p.lev old)*MvPolynomial.eval (xp z.1 z.2) P

theorem physicalParent_clock_relation {W : ℕ} (N : ℝ) (p : PathData W) (old : Fin p.C)
    (P : MvPolynomial (Fin 4) ℝ) (z : Ev) :
    (δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))*physicalParentSignal N p old P z =
      clockParentSignal p old P z := by
  have ha : δ N (p.r (p.lev old)) ≠ 0 := by unfold δ; positivity
  unfold physicalParentSignal clockParentSignal
  field_simp [ha]

/-- The actual height/clock conversion is an integer power of two. -/
theorem parent_height_clock_ratio_zpow {W : ℕ} (N : ℝ) (p : PathData W) (old : Fin p.C) :
    δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹) =
      (2:ℝ)^((p.T (p.lev old):ℤ)-⌊p.r (p.lev old)*Real.log N/Real.log 2⌋) := by
  change (2:ℝ)^(-(⌊p.r (p.lev old)*Real.log N/Real.log 2⌋:ℤ))/
      (((2:ℝ)^p.T (p.lev old))⁻¹)=_
  rw [div_inv_eq_mul,←zpow_natCast,←zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  congr 1
  ring

theorem measurable_clockParentSignal {W : ℕ} (N : ℝ) (p : PathData W) (old : Fin p.C)
    (P : MvPolynomial (Fin 4) ℝ) : Measurable (clockParentSignal p old P) := by
  have heq : clockParentSignal p old P = fun z =>
      (δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹))*physicalParentSignal N p old P z := by
    funext z
    exact (physicalParent_clock_relation N p old P z).symm
  rw [heq]
  exact (measurable_physicalParentSignal N p old P).const_mul _

/-- Every actual clock-scaled coarse state is an exact deterministic
coarsening of the original fine physical parent state. -/
theorem parent_clock_state_coarsening {W : ℕ} (N : ℝ) (p : PathData W) (old : Fin p.C)
    (P : MvPolynomial (Fin 4) ℝ) {ε : ℝ} (hε : 0 < ε) (baseSteps : ℕ)
    (hbound : δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹) ≤ (2:ℝ)^baseSteps) :
    ∃ heightSteps : ℕ, ∀ z : Ev,
      gridCode (fun z j => unshearedPacketBase p old z j) (clockParentSignal p old P)
        (ε*(2:ℝ)^baseSteps) (ε*(2:ℝ)^baseSteps) z =
      coarsenProductGrid baseSteps heightSteps
        (gridCode (fun z j => unshearedPacketBase p old z j) (physicalParentSignal N p old P) ε ε z) := by
  have hθ : 0 < δ N (p.r (p.lev old))/(((2:ℝ)^p.T (p.lev old))⁻¹) := by unfold δ; positivity
  obtain ⟨heightSteps,hscale⟩ := exists_dyadic_height_coarsening _
    (parent_height_clock_ratio_zpow N p old) baseSteps hbound
  refine ⟨heightSteps,?_⟩
  intro z
  have hh := clock_gridCode_dyadic_coarsening (fun z j => unshearedPacketBase p old z j)
    (physicalParentSignal N p old P) hε hθ baseSteps heightSteps hscale z
  simpa only [physicalParent_clock_relation] using hh

end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
