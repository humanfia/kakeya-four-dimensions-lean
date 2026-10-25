-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FineContainment, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FineContainment.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FineContainment.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FineContainment.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.NativeFinePacketBridge

/-! A common original incidence identifies the full old ancestor packet.
This yields whole-assignment inclusion, beyond the selected incidence set. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set

section Path

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

theorem PathData.Valid.containment_of_common_unique
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (b f : Fin p.C) (hlev : p.lev b ≤ p.lev f) (hγ : p.γ f = p.γ b)
    (x : (ℕ × (Fin 6 → ℝ)) × ℝ) (hunique : packetUnique p.lev p.γ p.F (p.γ b) x)
    (hxb : x ∈ p.F b) (hxf : x ∈ p.F f) : p.A f ⊆ p.A b ∧ p.F f ⊆ p.F b := by
  obtain ⟨a, ha, haγ, haA, haF⟩ := ancestor_of_parent p.lev p.par p.γ p.A p.F hp.parent f (p.lev b) hlev
  have hab : a = b := hunique a b ha (haγ.trans hγ) rfl (haF hxf) hxb
  simpa only [hab] using And.intro haA haF

end Path

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
