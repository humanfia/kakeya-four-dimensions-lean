-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.PureBoundsGrid, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/PureBoundsGrid.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/PureBoundsGrid.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PureDepthGrid
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.PureGridCeiling

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open scoped ENNReal

/-- A fixed finite menu brackets every later actual depth on both sides. -/
theorem exists_fixed_two_sided_depth_grid {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) :
    ∃ n : ℕ, 0 < n ∧ ∃ depths : Fin (n + 1) ⊕ Fin (n + 1) → ℝ,
      (∀ i, 0 ≤ depths i ∧ depths i ≤ L) ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ L → ∃ i, depths i ≤ r ∧ r - depths i ≤ ε) ∧
      (∀ r : ℝ, 0 ≤ r → r ≤ L → ∃ i, r ≤ depths i ∧ depths i - r ≤ ε) := by
  obtain ⟨n, hn, depths, hdepths, hgrid⟩ := exists_fixed_lower_depth_grid hL hε
  refine ⟨n, hn, Sum.elim depths (fun i => L - depths i), ?_, ?_, ?_⟩
  · intro i
    cases i with
    | inl i => exact hdepths i
    | inr i => dsimp; constructor <;> linarith [(hdepths i).1, (hdepths i).2]
  · intro r hr hrL
    obtain ⟨i, hi, hnear⟩ := hgrid r hr hrL
    exact ⟨Sum.inl i, hi, hnear⟩
  · intro r hr hrL
    obtain ⟨i, hi, hnear⟩ := hgrid (L - r) (by linarith) (by linarith)
    exact ⟨Sum.inr i, by dsimp; linarith, by dsimp; linarith⟩

/-- Upper test depths supply the original density floor at every actual
depth, with only the requested grid-spacing error. -/
theorem ProblemData.Valid.pure_floor_of_upper_tests {I : Type*}
    {d : ProblemData} (hd : d.Valid) (k : ℕ) (w : Fin (d.W k))
    (ρ : Measure ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hρ : ρ ≤ d.μ k w)
    (depths : I → ℝ) (hdepth : ∀ i, 0 ≤ depths i ∧ depths i ≤ d.L)
    (τ ε : ℝ)
    (htests : ∀ i, ∀ᵐ q ∂ρ,
      ENNReal.ofReal (d.N k ^ (-d.f (depths i) - τ)) ≤
        d.g k w (depths i) (obs (d.B k w) (δ (d.N k) (depths i)) q))
    (hgrid : ∀ r : ℝ, 0 ≤ r → r ≤ d.L → ∃ i, r ≤ depths i ∧ depths i - r ≤ ε)
    {r : ℝ} (hr : 0 ≤ r) (hrL : r ≤ d.L) :
    ∀ᵐ q ∂ρ, ENNReal.ofReal (d.N k ^ (-d.f r - τ - ε)) ≤
      d.g k w r (obs (d.B k w) (δ (d.N k) r) q) := by
  obtain ⟨i, hri, hgap⟩ := hgrid r hr hrL
  have hmono := (ae_mono hρ) (hd.pure_density_antitone k w hr hri (hdepth i).2)
  have hprofile : d.f (depths i) - d.f r ≤ depths i - r := by
    rcases hd with ⟨_, _, _, _, _, _, _, _, _, _, _, hf, _⟩
    exact (hf _ _ hr hri (hdepth i).2).2
  have hpow : ENNReal.ofReal (d.N k ^ (-d.f r - τ - ε)) ≤
      ENNReal.ofReal (d.N k ^ (-d.f (depths i) - τ)) := by
    apply ENNReal.ofReal_le_ofReal
    apply Real.rpow_le_rpow_of_exponent_le ((by norm_num : (1 : ℝ) ≤ 2).trans (hd.1 k))
    linarith
  filter_upwards [hmono, htests i] with q hq hqt
  exact hpow.trans (hqt.trans hq)

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
