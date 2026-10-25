-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentSelection, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentSelection.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentSelection.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.NativePacketModel
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.SelectedPacketLaw
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.DensePackets

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- Original mixed mass selects an actual old parent with the same
relative source mass. The full old assignment supplies its native prior. -/
theorem Native.PathData.Valid.exists_original_parent_source
    {W : ℕ} {p : Native.PathData W}
    {Nk L κ₁ δ₀ σ : ℝ} {m Mp Dp : ℕ} {s : ℕ → ℝ}
    {ω : Fin W → ℝ} {ν : Fin W → Measure Ln}
    {E : Fin W → Set Ev} {B : Fin W → ℝ} {f : ℝ → ℝ}
    (hp : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hν : ∀ w, IsProbabilityMeasure (ν w)) (hω : ∀ w, 0 ≤ ω w)
    (hsum : ∑ w, ω w = 1)
    (J : Fin W → Set Ev) (hJ : ∀ w, MeasurableSet (J w))
    (hcover : ∀ w, J w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    {α : ℝ} (hα : 0 < α)
    (hmass : ENNReal.ofReal α ≤ ∑ w, ENNReal.ofReal (ω w) * (ν w).prod volume (J w))
    (i : ℕ) (hi : i < m) :
    ∃ b : Fin p.C, p.lev b = i ∧ 0 < ω (p.γ b) ∧ ν (p.γ b) (p.A b) ≠ 0 ∧
      ENNReal.ofReal α ≤
        (hp.frozenPacket b).selectedLaw (ν (p.γ b)) (J (p.γ b) ∩ p.F b) univ ∧
      (hp.frozenPacket b).selectedLaw (ν (p.γ b)) (J (p.γ b) ∩ p.F b) ≤
        (hp.frozenPacket b).law (ν (p.γ b)) ∧
      (∀ᵐ z ∂(hp.frozenPacket b).selectedLaw (ν (p.γ b)) (J (p.γ b) ∩ p.F b),
        ∀ e, |(hp.frozenPacket b).scalarCoefficients z.1 e| ≤ 17 * p.κ) := by
  obtain ⟨b, hb, hw, hA, hdense⟩ :=
    path_exists_dense_packet hp hν hω hsum J hcover hα hmass i hi
  letI : IsProbabilityMeasure (ν (p.γ b)) := hν _
  have hmeas : MeasurableSet (J (p.γ b) ∩ p.F b) :=
    (hJ _).inter (path_packet_measurable hp b).2
  have hsub : J (p.γ b) ∩ p.F b ⊆ (hp.frozenPacket b).counted := inter_subset_right
  have hdom := (hp.frozenPacket b).selectedLaw_le (ν (p.γ b)) hsub
  refine ⟨b, hb, hw, hA, ?_, hdom,
    (ae_mono hdom) (hp.frozenPacket_scalar_coefficients b)⟩
  apply (hp.frozenPacket b).selectedLaw_mass_lower (ν (p.γ b)) hA hmeas hsub
  change ENNReal.ofReal α *
    (ENNReal.ofReal (((2 : ℝ) ^ p.T (p.lev b))⁻¹) * ν (p.γ b) (p.A b)) ≤ _
  rw [← mul_assoc, ← ENNReal.ofReal_mul hα.le]
  simpa only [hb, div_eq_mul_inv] using hdense

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
