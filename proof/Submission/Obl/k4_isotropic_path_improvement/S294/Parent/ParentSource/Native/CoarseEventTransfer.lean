-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.CoarseEventTransfer, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/CoarseEventTransfer.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/CoarseEventTransfer.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/CoarseEventTransfer.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/CoarseEventTransfer.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.CoarsePacketWitness

/-! Events of the fixed labelled coarse law transfer exactly to the
unchanged native packet posterior, including their omission costs. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set

/-- A law supported on one world loses no event information when that fixed
world label is dropped and then restored. -/
theorem map_snd_fixed_world_apply {W : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Measure (Fin W × X)) (w : Fin W) (hworld : ∀ᵐ z ∂μ, z.1 = w)
    (D : Set (Fin W × X)) (hD : MeasurableSet D) :
    (μ.map Prod.snd) (Prod.mk w ⁻¹' D) = μ D := by
  rw [Measure.map_apply measurable_snd (hD.preimage measurable_prodMk_left)]
  apply measure_congr
  filter_upwards [hworld] with z hz
  have heq : (w, z.2) = z := Prod.ext hz.symm rfl
  simpa only [mem_preimage, heq]

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)

/-- Any measurable coarse-posterior omission has exactly the SAME cost in
the native current-parent posterior. The latter is not renormalized again. -/
theorem PreparedAngularPath.coarse_event_to_native (b : Fin p.C) (c : ℕ)
    (hC : MeasurableSet (Q.coarseSupport (p.lev b) c))
    (hPacket : ∀ z ∈ Q.coarseSupport (p.lev b) c, z.1 = p.γ b ∧ z.2 ∈ p.F b)
    (hmap : (Q.coarseLaw (p.lev b) c).map Prod.snd = ProbabilityTheory.cond (Q.currentParentLaw b) univ)
    (D : Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ))) (hD : MeasurableSet D)
    (hDC : D ⊆ Q.coarseSupport (p.lev b) c) :
    MeasurableSet (Prod.mk (p.γ b) ⁻¹' D) ∧
      Prod.mk (p.γ b) ⁻¹' D ⊆ Q.residual (p.γ b) ∩ p.F b ∧
      ProbabilityTheory.cond (Q.currentParentLaw b) univ (Prod.mk (p.γ b) ⁻¹' D) =
        Q.coarseLaw (p.lev b) c D := by
  have hworld : ∀ᵐ z ∂Q.coarseLaw (p.lev b) c, z.1 = p.γ b := by
    filter_upwards [ProbabilityTheory.ae_cond_mem (μ := Q.law) hC] with z hz
    exact (hPacket z hz).1
  refine ⟨hD.preimage measurable_prodMk_left, ?_, ?_⟩
  · intro x hx
    have hh := hDC hx
    exact ⟨hh.1, (hPacket _ hh).2⟩
  · rw [← hmap]
    exact map_snd_fixed_world_apply _ (p.γ b) hworld D hD

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
