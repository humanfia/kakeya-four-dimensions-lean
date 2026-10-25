-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.NativePacketModel, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/NativePacketModel.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/NativePacketModel.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PathBridge
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPathPackets

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory
open scoped ENNReal

noncomputable section

section Path

variable {W : ℕ} {p : Native.PathData W}
  {Nk L κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
  {ω : Fin W → ℝ} {ν : Fin W → Measure Ln}
  {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
  (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

/-- The actual old packet in the version-2 native geometry interface.
The original assignment and complete counted chart are preserved. -/
def Native.PathData.Valid.frozenPacket (b : Fin p.C) : Broad.Source.FrozenPacket :=
  Broad.Source.originalPathPacket hp.toOriginal b

theorem Native.PathData.Valid.frozenPacket_assignment (b : Fin p.C) :
    (hp.frozenPacket b).assigned = p.A b := rfl

theorem Native.PathData.Valid.frozenPacket_counted (b : Fin p.C) :
    (hp.frozenPacket b).counted = p.F b := rfl

/-- The native prior conditions the full old assignment once. -/
theorem Native.PathData.Valid.frozenPacket_prior_probability (hN : 0 < Nk) (b : Fin p.C)
    [IsFiniteMeasure (ν (p.γ b))] :
    IsProbabilityMeasure ((hp.frozenPacket b).prior (ν (p.γ b))) :=
  Broad.Source.originalPathPacket_prior_probability hp.toOriginal hN b

/-- No later residual mass is used as a denominator in these native bounds. -/
theorem Native.PathData.Valid.frozenPacket_mass_bounds (hN : 0 < Nk) (b : Fin p.C)
    [IsFiniteMeasure (ν (p.γ b))] :
    (ENNReal.ofReal (p.κ ^ 2))⁻¹ ≤ (hp.frozenPacket b).law (ν (p.γ b)) Set.univ ∧
      (hp.frozenPacket b).law (ν (p.γ b)) Set.univ ≤ 1 :=
  Broad.Source.originalPathPacket_mass_bounds hp.toOriginal hN b

/-- The seven actual scalar-normal coefficients have a small geometric
bound independent of the original format exponent. -/
theorem Native.PathData.Valid.frozenPacket_scalar_coefficients (b : Fin p.C) :
    ∀ᵐ z ∂(hp.frozenPacket b).law (ν (p.γ b)),
      ∀ i, |(hp.frozenPacket b).scalarCoefficients z.1 i| ≤ 17 * p.κ :=
  Broad.Source.originalPathPacket_scalar_coefficients hp.toOriginal b

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
