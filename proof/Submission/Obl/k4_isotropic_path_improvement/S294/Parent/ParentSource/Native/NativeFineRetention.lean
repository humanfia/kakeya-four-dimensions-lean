-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.NativeFineRetention, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/NativeFineRetention.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/NativeFineRetention.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/NativeFineRetention.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/NativeFineRetention.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineRetention
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeConditionalOmissions
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.CoarseEventTransfer

/-! Actual native fine-state retention cuts have the same uniform cost in
fixed current posteriors, the single prepared law and ORIGINAL weighted mass. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped ENNReal BigOperators

section Certificate

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
  {H : Fin (d.W k) → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {u : T → ℝ} {τ : ℝ}
  (Q : PreparedAngularPath d k p m H u τ)
  {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}

noncomputable def PreparedAngularPath.fineRetentionOmissions
    (active : Fin p.C → Prop) (code : Fin p.C → ℕ) (stop : ℕ)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)))
    (α : ENNReal) (b : Fin p.C) : Set ((ℕ × (Fin 6 → ℝ)) × ℝ) := by
  classical
  exact if active b then Prod.mk (p.γ b) ⁻¹'
    (U b ∩ finitePacketHistory p.lev p.γ p.F stop ⁻¹'
      fineRetentionFailures (Q.coarseLaw (p.lev b) (code b))
        (finitePacketHistory p.lev p.γ p.F stop) (U b) α) else ∅

theorem PreparedAngularPath.fine_retention_omission_bounds (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (i : ℕ) (hi : i < m) (active : Fin p.C → Prop) (code : Fin p.C → ℕ) (stop : ℕ)
    (hcode : ∀ b, active b →
      (∀ z ∈ Q.coarseSupport (p.lev b) (code b), z.1 = p.γ b ∧ z.2 ∈ p.F b) ∧
      Q.law (Q.coarseSupport (p.lev b) (code b)) ≠ 0 ∧
      (Q.coarseLaw (p.lev b) (code b)).map Prod.snd = ProbabilityTheory.cond (Q.currentParentLaw b) univ)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)))
    (hU : ∀ b, active b → MeasurableSet (U b))
    (hUC : ∀ b, active b → U b ⊆ Q.coarseSupport (p.lev b) (code b)) (α : ENNReal) :
    (∀ b, MeasurableSet (Q.fineRetentionOmissions active code stop U α b)) ∧
      (∀ b, Q.fineRetentionOmissions active code stop U α b ⊆ Q.residual (p.γ b) ∩ p.F b) ∧
      (∀ b, ProbabilityTheory.cond (Q.currentParentLaw b) univ
        (Q.fineRetentionOmissions active code stop U α b) ≤ α) ∧
      Q.law (labelledSupport (Q.packetFamilyResidual i (Q.fineRetentionOmissions active code stop U α))) ≤ α ∧
      (∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume)
        (Q.packetFamilyResidual i (Q.fineRetentionOmissions active code stop U α) w)) ≤ α := by
  classical
  have hκ : 0 < p.κ := lt_of_lt_of_le zero_lt_one hp.1
  let := Q.probability hd hHE hκ
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hhist := measurable_finitePacketHistory p.lev p.γ p.F hF stop
  have hS := measurableSet_labelledSupport Q.residual Q.residual_measurable
  let D := Q.fineRetentionOmissions active code stop U α
  have hdata (b : Fin p.C) (hb : active b) : MeasurableSet (D b) ∧
      D b ⊆ Q.residual (p.γ b) ∩ p.F b ∧
      ProbabilityTheory.cond (Q.currentParentLaw b) univ (D b) ≤ α := by
    obtain ⟨hPacket, hCpos, hmap⟩ := hcode b hb
    let π := Q.coarseLaw (p.lev b) (code b)
    let Bad := fineRetentionFailures π (finitePacketHistory p.lev p.γ p.F stop) (U b) α
    let A := U b ∩ finitePacketHistory p.lev p.γ p.F stop ⁻¹' Bad
    have hA : MeasurableSet A := (hU b hb).inter
      (hhist ((Set.to_countable Bad).measurableSet))
    have hC : MeasurableSet (Q.coarseSupport (p.lev b) (code b)) :=
      hS.inter (measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF _) measurable_const)
    have ht := Q.coarse_event_to_native b (code b) hC hPacket hmap A hA
      (inter_subset_left.trans (hUC b hb))
    let : IsProbabilityMeasure π := ProbabilityTheory.cond_isProbabilityMeasure (μ := Q.law) hCpos
    have hcap : π A ≤ α := by
      simpa only [measure_univ, mul_one] using
        fine_retention_failures_mass_le π (finitePacketHistory p.lev p.γ p.F stop) hhist (U b) α
    simpa only [D, fineRetentionOmissions, ite_eq_left hb] using
      (show MeasurableSet (Prod.mk (p.γ b) ⁻¹' A) ∧
        Prod.mk (p.γ b) ⁻¹' A ⊆ Q.residual (p.γ b) ∩ p.F b ∧
        ProbabilityTheory.cond (Q.currentParentLaw b) univ (Prod.mk (p.γ b) ⁻¹' A) ≤ α from
          ⟨ht.1, ht.2.1, ht.2.2.trans_le hcap⟩)
  have hDm (b : Fin p.C) : MeasurableSet (D b) := by
    by_cases hb : active b
    · exact (hdata b hb).1
    · simp only [D, fineRetentionOmissions, ite_eq_right hb]
      exact MeasurableSet.empty
  have hDs (b : Fin p.C) : D b ⊆ Q.residual (p.γ b) ∩ p.F b := by
    by_cases hb : active b
    · exact (hdata b hb).2.1
    · simp only [D, fineRetentionOmissions, ite_eq_right hb]
      exact empty_subset _
  have hDc (b : Fin p.C) : ProbabilityTheory.cond (Q.currentParentLaw b) univ (D b) ≤ α := by
    by_cases hb : active b
    · exact (hdata b hb).2.2
    · simp only [D, fineRetentionOmissions, ite_eq_right hb, measure_empty]
      exact zero_le
  refine ⟨hDm, hDs, hDc, Q.conditional_omission_prepared_mass_le hd hp hHE hH i hi D hDm hDs
    α (fun b _ => hDc b), ?_⟩
  have hbound := Q.conditional_omission_original_mass_le hd hp hHE hH i hi D hDm hDs α
    (fun b _ => hDc b)
  exact hbound.trans (by
    simpa only [mul_one] using mul_le_mul le_rfl (Q.original_total_le_one hd hHE) zero_le zero_le)

theorem PreparedAngularPath.fine_retention_survives
    (active : Fin p.C → Prop) (code : Fin p.C → ℕ) (stop : ℕ)
    (U : Fin p.C → Set (Fin (d.W k) × ((ℕ × (Fin 6 → ℝ)) × ℝ)))
    (α : ENNReal) (b : Fin p.C) (hb : active b)
    (x : (ℕ × (Fin 6 → ℝ)) × ℝ) (hxU : (p.γ b, x) ∈ U b)
    (hx : x ∉ Q.fineRetentionOmissions active code stop U α b) :
    finitePacketHistory p.lev p.γ p.F stop (p.γ b, x) ∉
      fineRetentionFailures (Q.coarseLaw (p.lev b) (code b))
        (finitePacketHistory p.lev p.γ p.F stop) (U b) α := by
  intro he
  apply hx
  simpa only [fineRetentionOmissions, ite_eq_left hb, mem_preimage, mem_inter_iff] using
    (show (p.γ b, x) ∈ U b ∧ finitePacketHistory p.lev p.γ p.F stop (p.γ b, x) ∈
      fineRetentionFailures (Q.coarseLaw (p.lev b) (code b))
        (finitePacketHistory p.lev p.γ p.F stop) (U b) α from ⟨hxU, he⟩)

end Certificate

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
