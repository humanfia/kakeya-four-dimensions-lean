-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PreparedHistoryPackets, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PreparedHistoryPackets.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PreparedHistoryPackets.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/PreparedHistoryPackets.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/PreparedHistoryPackets.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.HistoryPackets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PreparedPosteriors

/-! Fixed coarse-history posteriors under the single labelled prepared law
are exactly the original native packet posteriors. -/

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal

section ValidPath

variable {W : ℕ} {p : PathData W} {Nk L : ℝ} {ω : Fin W → ℝ}
  {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
  {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
  {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
  {Mp Dp : ℕ} {σ : ℝ}

/-- One path-determined code works for every later residual. Conditioning the
prepared labelled law at that code gives the same original packet posterior. -/
theorem PathData.Valid.prepared_history_packet_posterior_strong
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (b : Fin p.C) (hω : 0 < ω (p.γ b)) :
    ∃ code : ℕ,
      (∀ z, finitePacketHistory p.lev p.γ p.F (p.lev b) z = code → z.1 = p.γ b ∧ z.2 ∈ p.F b) ∧
      ∀ H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (labelledResidual (fun w => (ν w).prod volume) ω H) univ ≠ ∞ →
      (ProbabilityTheory.cond (preparedResidualLaw (fun w => (ν w).prod volume) ω H)
        {z | finitePacketHistory p.lev p.γ p.F (p.lev b) z = code}).map Prod.snd =
          ProbabilityTheory.cond ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b) := by
  obtain ⟨code, hcode⟩ := h.history_code_of_packet hNk b
  have hw := finitePacketHistory_packet_of_packet_code ((ν (p.γ b)).prod volume)
    p.lev p.γ p.F b code hcode (h.packet_mass_pos hNk b)
  refine ⟨code, hw, ?_⟩
  intro H htotal
  have hF : ∀ a, MeasurableSet (p.F a) := by
    intro a
    exact (h.2.2.2.2.2.2.2 a).2.2.2.2.2.2.2.2.2.1
  have hD : MeasurableSet {z | finitePacketHistory p.lev p.γ p.F (p.lev b) z = code} :=
    measurableSet_eq_fun (measurable_finitePacketHistory p.lev p.γ p.F hF _) measurable_const
  calc
    _ = ProbabilityTheory.cond ((ν (p.γ b)).prod volume)
        (H (p.γ b) ∩ {q | finitePacketHistory p.lev p.γ p.F (p.lev b) (p.γ b, q) = code}) :=
      prepared_world_posterior (fun w => (ν w).prod volume) ω H _ hD (p.γ b)
        (fun z hz => (hw z hz).1) hω htotal
    _ = _ := cond_eq_packet_of_history_code ((ν (p.γ b)).prod volume)
      p.lev p.γ p.F b code hcode (H (p.γ b))

/-- The original posterior interface, with the stronger pointwise packet
membership available from `prepared_history_packet_posterior_strong`. -/
theorem PathData.Valid.prepared_history_packet_posterior
    (h : p.Valid Nk L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hNk : 0 < Nk) (b : Fin p.C) (hω : 0 < ω (p.γ b)) :
    ∃ code : ℕ,
      (∀ z, finitePacketHistory p.lev p.γ p.F (p.lev b) z = code → z.1 = p.γ b) ∧
      ∀ H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ),
      (labelledResidual (fun w => (ν w).prod volume) ω H) univ ≠ ∞ →
      (ProbabilityTheory.cond (preparedResidualLaw (fun w => (ν w).prod volume) ω H)
        {z | finitePacketHistory p.lev p.γ p.F (p.lev b) z = code}).map Prod.snd =
          ProbabilityTheory.cond ((ν (p.γ b)).prod volume) (H (p.γ b) ∩ p.F b) := by
  obtain ⟨code, hcode, hpost⟩ := h.prepared_history_packet_posterior_strong hNk b hω
  exact ⟨code, fun z hz => (hcode z hz).1, hpost⟩

end ValidPath

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
