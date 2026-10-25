-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.HistoryPackets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/HistoryPackets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/HistoryPackets.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/HistoryPackets.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/HistoryPackets.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Histories
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.Partitions

/-! Packet conditionals coincide with the finite-history conditionals under
the original world measure, including after arbitrary residual restrictions. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set

section ValidPath

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

/-- The code is fixed by the original path packet before the residual is
chosen. Closed endpoint overlaps are invisible under the original law. -/
theorem PathData.Valid.history_code_of_packet
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 0 < Nk) (b : Fin p.C) :
    ∃ code : ℕ, ∀ᵐ z ∂(ν (p.γ b)).prod volume,
      finitePacketHistory p.lev p.γ p.F (p.lev b) (p.γ b, z) = code ↔ z ∈ p.F b := by
  apply exists_history_code_of_packet ((ν (p.γ b)).prod volume) p.lev p.γ p.F b
    _ _ (h.packet_mass_pos hNk b)
  · intro i hi
    obtain ⟨a, hlev, hγ, _, hF⟩ :=
      ancestor_of_parent p.lev p.par p.γ p.A p.F h.parent b i hi
    exact ⟨a, hlev, hγ, hF⟩
  · intro a a' hne hlev hγ hγ'
    simpa only [hγ] using h.packet_aedisjoint a a' hne hlev (hγ.trans hγ'.symm)

theorem PathData.Valid.history_packet_conditionals
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ) (hNk : 0 < Nk) (b : Fin p.C) :
    ∃ code : ℕ, ∀ H : Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      ProbabilityTheory.cond ((ν (p.γ b)).prod volume)
        (H ∩ {z | finitePacketHistory p.lev p.γ p.F (p.lev b) (p.γ b, z) = code}) =
          ProbabilityTheory.cond ((ν (p.γ b)).prod volume) (H ∩ p.F b) := by
  obtain ⟨code, hcode⟩ := h.history_code_of_packet hNk b
  exact ⟨code, fun H => cond_eq_packet_of_history_code ((ν (p.γ b)).prod volume)
    p.lev p.γ p.F b code hcode H⟩

end ValidPath

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
