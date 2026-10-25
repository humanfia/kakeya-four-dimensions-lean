-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripWidth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripWidth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripWidth.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripWidth.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripWidth.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPath
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripSystem
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripCoverage
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripBudget

/-! An original-law narrow velocity cover yields precisely the width alternative
in the frozen discovery statement. The strip exponent remains explicit. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped BigOperators RealInnerProductSpace

theorem PathData.Valid.width_of_strip_refinement
    {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (h : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hN : 1 ≤ N) (hB : ∀ w, 0 ≤ B w)
    (i : ℕ) (hi : i < m) {gain τ loss stripExponent : ℝ} {Mi : ℕ}
    (hdepth : p.r i + 2 * gain * L ≤ L) (hrL : p.r i ≤ L)
    (d : StripRefinement (p.StripLevel i)) (hM : Mp ≤ Mi)
    (hκτ : p.κ ≤ N ^ τ) (hslack : 4 ≤ N ^ τ) (hr : 0 < d.radius)
    (he : ∀ b j, ‖d.tangent b j‖ = 1) (hn : ∀ b j, ‖d.normal b j‖ = 1)
    (hen : ∀ b j, inner ℝ (d.tangent b j) (d.normal b j) = 0)
    (hbins : p.κ ≤ (d.bins : ℝ) * d.radius)
    (hformat : 2 * N ^ Mp + 2 * (d.count : ℝ) + 2 ≤ N ^ Mi)
    (hcard : (p.C : ℝ) * ((d.count : ℝ) * (2 * (d.bins : ℝ) + 1)) ≤ N ^ Mi)
    (hdata : ∀ a : d.Label,
      ‖d.center (p.stripParent i) a‖ + ‖d.velocity (p.stripParent i) a‖ ≤ N ^ Mi ∧
      (∑ e : Fin 2, ∑ e' : Fin 2,
        (|d.frame (p.stripParent i) p.κ a e e'| + |(d.frame (p.stripParent i) p.κ a)⁻¹ e e'|)) ≤ N ^ Mi ∧
      (∑ e : Fin 2, ∑ e' : Fin 2, |d.frame (p.stripParent i) p.κ a e e'|) ≤
        N ^ τ / (2 : ℝ) ^ p.T i)
    (hlist : p.κ * ((d.count : ℝ) * (2 * (d.normalBudget : ℝ) + 1)) ≤ N ^ τ)
    (hfactor : p.κ * (1 + (d.normalBudget : ℝ)) ≤ N ^ loss)
    (hradius : d.radius ≤ N ^ (-stripExponent))
    (hgain : δ₀ * L + loss + gain * L ≤ stripExponent)
    (hmass : ENNReal.ofReal (N ^ (-τ)) ≤
      ∑ b : p.StripLevel i, ENNReal.ofReal (ω (p.γ b)) *
        (ν (p.γ b)).prod volume (d.coveredIncidences (p.stripParent i) b)) :
    width N L W ω ν E B m p.r p.T p.nw gain Mi (max Dp 1) τ := by
  classical
  refine ⟨i, hi, hdepth, ?_⟩
  apply d.system_of_cover (p.stripParent i) (h.stripParent_valid i) hN hM h.1 hκτ
    hslack hB hr he hn hen hbins hformat ?_ hdata (h.stripParent_disjoint i)
    (p.stripParentList N L i) (h.stripParentList_known hN i hrL) ?_
    (fun Q => |Q.det| * (4 : ℝ) ^ p.T i ≤ N ^ (-(p.nw i + gain * L))) ?_ hmass
  · have hc : Fintype.card (p.StripLevel i) ≤ p.C := by
      simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun b : Fin p.C => p.lev b = i)
    have hc' : (Fintype.card (p.StripLevel i) : ℝ) ≤ p.C := Nat.cast_le.mpr hc
    exact (mul_le_mul_of_nonneg_right hc' (by positivity)).trans hcard
  · intro w o
    exact (mul_le_mul_of_nonneg_right (h.stripParentList_card i w o)
      (show 0 ≤ (d.count : ℝ) * (2 * (d.normalBudget : ℝ) + 1) by positivity)).trans hlist
  · intro a
    exact strip_determinant_power_bound (p.stripParent i a.1).frame (p.T i) hN
      (by linarith [h.1]) (by positivity) hr (he _ _) (hn _ _) (hen _ _)
      (h.stripParent_determinant_bound i a.1) hfactor hradius hgain

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
