-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Gradient.ClockParentPrior, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Gradient/ClockParentPrior.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1027, commit c5f477fdc5b972684b967b4654ceacc9f5a8f0ff,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Gradient/ClockParentPrior.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ClockParentJets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalNativeCoordinates

/-! # The original parent jets on the full old assignment -/

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal
open MeasureTheory Set Native Broad.Source
noncomputable section

/-- The good-line predicate used to bound the four jets has full measure
under the original prior. -/
theorem original_clockJetGood_ae {d : ProblemData} (hd : d.Valid)
    (k : ℕ) (w : Fin (d.W k)) :
    ∀ᵐ l ∂d.ν k w, l∈clockJetGood (d.P k w) (d.K k) (d.B k w) := by
  have hgood := (original_parent_bounds (show pb d.N d.K d.L d.d d.S d.η
    d.W d.ω d.ν d.E d.P d.B d.f d.g d.G from hd) k w).2.2.1
  filter_upwards [hgood,hd.native_bounds k w] with l hl hv
  refine ⟨hl, ?_⟩
  exact (le_add_of_nonneg_left (norm_nonneg (y l 0))).trans (hv 0 (by norm_num))

/-- Making the four-jet bounds pointwise costs exactly zero original mass. -/
theorem original_restrict_clockJetGood {d : ProblemData} (hd : d.Valid)
    (k : ℕ) (w : Fin (d.W k)) (E : Set Ev) :
    ((d.ν k w).prod volume).restrict
      (E∩Prod.fst ⁻¹' clockJetGood (d.P k w) (d.K k) (d.B k w)) =
      ((d.ν k w).prod volume).restrict E := by
  have hprod : ∀ᵐ z ∂(d.ν k w).prod (volume : Measure ℝ),
      z.1∈clockJetGood (d.P k w) (d.K k) (d.B k w) :=
    (Measure.ae_prod_iff_ae_ae
      ((measurableSet_clockJetGood _ _ _).preimage measurable_fst)).mpr
        ((original_clockJetGood_ae hd k w).mono fun _ h =>
          Filter.Eventually.of_forall fun _ => h)
  apply Measure.restrict_congr_set
  filter_upwards [hprod] with z hz
  simp only [mem_inter_iff,mem_preimage,hz,and_true]

section Path
variable {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd

/-- Passing to the complete old assignment preserves the original
almost-sure jet bounds; no selected incidence posterior is involved. -/
theorem assigned_clockJetGood_ae (old : Fin p.C) :
    ∀ᵐ (l : (hp.frozenPacket old).AssignedLine)
      ∂(hp.frozenPacket old).assignedPrior (d.ν k (p.γ old)),
      (l : Ln)∈clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) := by
  let packet := hp.frozenPacket old
  have hprior : ∀ᵐ l ∂packet.prior (d.ν k (p.γ old)),
      l∈clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) := by
    rw [packet.prior_eq]
    exact Measure.ae_smul_measure
      (ae_restrict_of_ae (original_clockJetGood_ae hd k (p.γ old))) _
  have hmap : ∀ᵐ l ∂(packet.assignedPrior (d.ν k (p.γ old))).map
      ((↑) : packet.AssignedLine → Ln),
      l∈clockJetGood (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) := by
    rw [packet.map_assignedPrior]
    exact hprior
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable hmap

end Path
end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.ParentSignal
