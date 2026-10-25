-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.FrozenPathPackets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/FrozenPathPackets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/FrozenPathPackets.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o106, branch x0352, commit 38d075b9;
-- source Submission/Obl/k4_isotropic_path_improvement/FrozenPathPackets.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_finite_positive_mixed_cover_realization.Path
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.FrozenPacketScalarModel

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

abbrev OriginalPathData := Submission.Obl.k4_finite_positive_mixed_cover_realization.PathData

section Path

variable {W m Mp Dp : ℕ} {p : OriginalPathData W} {ℓ Nk L κ₁ δ₀ σ : ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure FrozenPacket.Line}
    {E : Fin W → Set FrozenPacket.Incidence} {B : Fin W → ℝ} {f : ℝ → ℝ} {s : ℕ → ℝ}
    (hp : p.Valid ℓ Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)

include hp

/-- The old frozen path node itself supplies the packet. No new chart,
assignment, counted event, trajectory tag, or tolerance is chosen. -/
def originalPathPacket (b : Fin p.C) : FrozenPacket where
  size := Nk
  formatExponent := Mp
  formatDegree := Dp
  slack := p.κ
  timeDepth := p.T (p.lev b)
  timeBin := p.bin b
  depth := p.r (p.lev b)
  derivativeScale := B (p.world b)
  originalEvent := E (p.world b)
  center := p.center b
  speed := p.velocity b
  matrix := p.frame b
  originalTest := p.test b
  assigned := p.assigned b
  counted := p.counted b
  valid := hp.chart b

theorem originalPathPacket_assignment_nonzero (hNk : 0 < Nk) (b : Fin p.C)
    [IsFiniteMeasure (ν (p.world b))] : ν (p.world b) (p.assigned b) ≠ 0 := by
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.one_le_slack
  have hdet : 0 < |(p.frame b).det| := abs_pos.mpr (hp.chart b).1
  have hmass : 0 < ((ν (p.world b)).prod volume) (p.counted b) :=
    lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (div_pos
      (mul_pos (Real.rpow_pos_of_pos hNk _) hdet) (by positivity))) (hp.saturation b).1
  intro hzero
  have hnull : ((ν (p.world b)).prod volume) (p.assigned b ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.prod_prod, hzero, zero_mul]
  apply hmass.ne'
  apply measure_mono_null _ hnull
  intro z hz
  exact ⟨(hp.counted_support b z hz).2.1, mem_univ _⟩

/-- The actual packet law has inverse-square original slack mass and
total mass at most one, with the full old assignment as denominator. -/
theorem originalPathPacket_mass_bounds (hNk : 0 < Nk) (b : Fin p.C)
    [IsFiniteMeasure (ν (p.world b))] :
    (ENNReal.ofReal (p.κ ^ 2))⁻¹ ≤ (originalPathPacket hp b).law (ν (p.world b)) univ ∧
      (originalPathPacket hp b).law (ν (p.world b)) univ ≤ 1 := by
  have hA := originalPathPacket_assignment_nonzero hp hNk b
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.one_le_slack
  have hq := (originalPathPacket hp b).unitFrame_length_pos
  let T : ℝ := Nk ^ (-f (p.r (p.lev b))) * |(p.frame b).det|
  have hupper := (hp.saturation b).2
  have hlower := (hp.saturation b).1
  have hreal : p.κ * Nk ^ (-f (p.r (p.lev b))) * |(p.frame b).det| = p.κ * T := by
    dsimp [T]
    ring
  rw [hreal] at hupper
  change ENNReal.ofReal (T / ((2 : ℝ) ^ p.T (p.lev b) * p.κ)) ≤
    ((ν (p.world b)).prod volume) (p.counted b) at hlower
  have hid : (originalPathPacket hp b).unitFrame.q * (p.κ * T) =
      p.κ ^ 2 * (T / ((2 : ℝ) ^ p.T (p.lev b) * p.κ)) := by
    dsimp [originalPathPacket, FrozenPacket.unitFrame]
    field_simp [hκ.ne']
    <;> ring
  have hbudget : ENNReal.ofReal (originalPathPacket hp b).unitFrame.q *
      ν (p.world b) (p.assigned b) ≤ ENNReal.ofReal (p.κ ^ 2) *
        ((ν (p.world b)).prod volume) (p.counted b) := by
    calc
      _ ≤ ENNReal.ofReal (originalPathPacket hp b).unitFrame.q * ENNReal.ofReal (p.κ * T) :=
        mul_le_mul' le_rfl hupper
      _ = ENNReal.ofReal ((originalPathPacket hp b).unitFrame.q * (p.κ * T)) := by
        rw [ENNReal.ofReal_mul hq.le]
      _ = ENNReal.ofReal (p.κ ^ 2) *
          ENNReal.ofReal (T / ((2 : ℝ) ^ p.T (p.lev b) * p.κ)) := by
        rw [← ENNReal.ofReal_mul (sq_nonneg _), hid]
      _ ≤ _ := mul_le_mul' le_rfl hlower
  exact ⟨(originalPathPacket hp b).law_mass_lower_of_original_budget (ν (p.world b)) hA hκ hbudget,
    (originalPathPacket hp b).law_mass_le_one (ν (p.world b)) hA⟩

/-- This probability is conditioned only on the FULL old assignment. -/
theorem originalPathPacket_prior_probability (hNk : 0 < Nk) (b : Fin p.C)
    [IsFiniteMeasure (ν (p.world b))] :
    IsProbabilityMeasure ((originalPathPacket hp b).prior (ν (p.world b))) :=
  (originalPathPacket hp b).prior_probability (ν (p.world b))
    (originalPathPacket_assignment_nonzero hp hNk b)

/-- The SAME original frozen packet has a genuine conditional time
kernel, its actual line marginal, long-time caps, and original short loss. -/
theorem originalPathPacket_time_kernel (hNk : 0 < Nk) (b : Fin p.C)
    [IsFiniteMeasure (ν (p.world b))] :
    let packet := originalPathPacket hp b
    let μ := packet.law (ν (p.world b))
    IsFiniteMeasure μ ∧ ∃ κ : Kernel FrozenPacket.Line ℝ,
      IsMarkovKernel κ ∧ μ.fst ⊗ₘ κ = μ ∧
      (∀ q : ENNReal, 0 < q →
        ∀ l ∈ Submission.Lib.K4Homogenization.durationRetained unitTimeReference
          (originalUnitEventDensity packet.event) univ q, κ l ≤ (1 / q) • volume) ∧
      (∀ q : ENNReal, μ (Prod.fst ⁻¹'
        (Submission.Lib.K4Homogenization.durationRetained unitTimeReference
          (originalUnitEventDensity packet.event) univ q)ᶜ) ≤ q) :=
  (originalPathPacket hp b).law_time_kernel (ν (p.world b))
    (originalPathPacket_assignment_nonzero hp hNk b)

theorem originalPathPacket_scalar_coefficients (b : Fin p.C) :
    ∀ᵐ z ∂(originalPathPacket hp b).law (ν (p.world b)),
      ∀ i, |(originalPathPacket hp b).scalarCoefficients z.1 i| ≤ 17 * p.κ :=
  (originalPathPacket hp b).scalar_coefficients_on_original_law (ν (p.world b))

end Path

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source
