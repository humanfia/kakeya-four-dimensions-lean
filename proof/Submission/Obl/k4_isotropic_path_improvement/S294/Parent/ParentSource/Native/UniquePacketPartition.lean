-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.UniquePacketPartition, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/UniquePacketPartition.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/UniquePacketPartition.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/UniquePacketPartition.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FineContainment

/-! Original packet membership is an exact finite partition on the fixed
endpoint-cleaned residual, for any measure used in a later calculation. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal BigOperators

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.unique_residual_mass_eq_sum
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (μ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (J : Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hJ : MeasurableSet J) (w : Fin W)
    (hcover : ∀ x ∈ J, ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ x ∈ p.F b)
    (hunique : ∀ x ∈ J, packetUnique p.lev p.γ p.F w x) (i : ℕ) (hi : i < m) :
    μ J = ∑ b, if p.lev b = i ∧ p.γ b = w then μ (J ∩ p.F b) else 0 := by
  classical
  let ids := Finset.univ.filter (fun b => p.lev b = i ∧ p.γ b = w)
  have hF (b : Fin p.C) : MeasurableSet (p.F b) :=
    (hp.2.2.2.2.2.2.2 b).2.2.2.2.2.2.2.2.2.1
  have hunion : J = ⋃ b ∈ ids, J ∩ p.F b := by
    ext x
    constructor
    · intro hx
      obtain ⟨t, ht, htγ, hxt⟩ := hcover x hx
      obtain ⟨b, hb, hbγ, _, hbt⟩ := ancestor_of_parent p.lev p.par p.γ p.A p.F hp.parent t i (by omega)
      refine mem_iUnion.mpr ⟨b, mem_iUnion.mpr ⟨?_, hx, hbt hxt⟩⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb, hbγ.trans htγ⟩
    · intro hx
      obtain ⟨b, hb⟩ := mem_iUnion.mp hx
      obtain ⟨_, hxb⟩ := mem_iUnion.mp hb
      exact hxb.1
  have hdisj : (ids : Set (Fin p.C)).PairwiseDisjoint (fun b => J ∩ p.F b) := by
    intro b hb b' hb' hne
    apply Set.disjoint_left.mpr
    intro x hxb hxb'
    obtain ⟨hbi, hbγ⟩ := (Finset.mem_filter.mp hb).2
    obtain ⟨hb'i, hb'γ⟩ := (Finset.mem_filter.mp hb').2
    exact hne (hunique x hxb.1 b b' (hbi.trans hb'i.symm) hbγ hb'γ hxb.2 hxb'.2)
  conv_lhs => rw [hunion]
  rw [measure_biUnion_finset hdisj (fun b _ => hJ.inter (hF b))]
  simpa only [ids] using Finset.sum_filter (s := Finset.univ)
    (fun b => p.lev b = i ∧ p.γ b = w) (fun b => μ (J ∩ p.F b))

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
