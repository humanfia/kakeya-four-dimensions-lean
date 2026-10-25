-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripUniformWidth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripUniformWidth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripUniformWidth.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripUniformWidth.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripUniformWidth.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripWidth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripNumerics
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripPowerBudgets

/-! A single polynomial output exponent works for every requested width slack.
All remaining hypotheses concern the original covered mass and strip geometry. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped BigOperators RealInnerProductSpace

def stripOutputExponent (Mp J U : ℕ) : ℕ := max (2 * J + 6) (Mp + U + 7)

theorem PathData.Valid.width_of_strip_envelope
    {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {Ev : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (h : p.Valid N L ω ν Ev B f κ₁ m s δ₀ Mp Dp σ)
    (hN : 2 ≤ N) (hB : ∀ w, 0 ≤ B w)
    (i : ℕ) (hi : i < m) {gain τ loss stripExponent E : ℝ}
    (hdepth : p.r i + 2 * gain * L ≤ L) (hrL : p.r i ≤ L)
    (d : StripRefinement (p.StripLevel i)) (J U : ℕ)
    (hJ : Mp ≤ J) (htime : (2 : ℝ) ^ p.T i ≤ N ^ J)
    (hE : 1 ≤ E) (hEN : E ≤ N) (hκE : p.κ ≤ E)
    (hr : 0 < d.radius) (hr1 : d.radius ≤ 1) (hrinv : d.radius⁻¹ ≤ N ^ U)
    (he : ∀ b j, ‖d.tangent b j‖ = 1) (hn : ∀ b j, ‖d.normal b j‖ = 1)
    (hen : ∀ b j, inner ℝ (d.tangent b j) (d.normal b j) = 0)
    (hbins : p.κ ≤ (d.bins : ℝ) * d.radius)
    (hbinUpper : (d.bins : ℝ) * d.radius ≤ 2 * E)
    (hβ : ∀ b j, |d.offset b j| ≤ 3 * E)
    (hcount : (d.count : ℝ) ≤ 3 * E ^ 2)
    (hnormal : (d.normalBudget : ℝ) ≤ 5 * E)
    (hslack : 100 * E ^ 8 ≤ N ^ τ) (hdetSlack : 6 * E ^ 2 ≤ N ^ loss)
    (hradius : d.radius ≤ N ^ (-stripExponent))
    (hgain : δ₀ * L + loss + gain * L ≤ stripExponent)
    (hmass : ENNReal.ofReal ((100 * E ^ 8)⁻¹) ≤
      ∑ b : p.StripLevel i, ENNReal.ofReal (ω (p.γ b)) *
        (ν (p.γ b)).prod volume (d.coveredIncidences (p.stripParent i) b)) :
    width N L W ω ν Ev B m p.r p.T p.nw gain (stripOutputExponent Mp J U) (max Dp 1) τ := by
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hE0 : 0 ≤ E := by linarith
  have hMi1 : 2 * J + 6 ≤ stripOutputExponent Mp J U := le_max_left _ _
  have hMi2 : Mp + U + 7 ≤ stripOutputExponent Mp J U := le_max_right _ _
  have hM : Mp ≤ stripOutputExponent Mp J U := by omega
  have hpow (a b : ℕ) (hab : a ≤ b) : N ^ a ≤ N ^ b := pow_le_pow_right₀ hN1 hab
  obtain ⟨hfour, hEslack, hsizeSlack, hlistSlack, _⟩ := strip_slack_of_power_envelope hE hslack
  obtain ⟨hfactor, hsize, hlist⟩ := strip_slack_envelope h.1 hE hκE
    (show 0 ≤ (d.normalBudget : ℝ) by positivity) hnormal
    (show 0 ≤ (d.count : ℝ) by positivity) hcount hr.le hr1
  have hformat : 2 * N ^ Mp + 2 * (d.count : ℝ) + 2 ≤ N ^ stripOutputExponent Mp J U :=
    (strip_format_power_budget hN hE hEN hcount Mp).trans (hpow _ _ (by omega))
  have hcard : (p.C : ℝ) * ((d.count : ℝ) * (2 * (d.bins : ℝ) + 1)) ≤
      N ^ stripOutputExponent Mp J U := by
    calc
      _ ≤ N ^ Mp * ((d.count : ℝ) * (2 * (d.bins : ℝ) + 1)) := by
        gcongr
        exact h.2.2.1
      _ ≤ N ^ (Mp + U + 7) := strip_card_power_budget hN hE hEN hcount
        (by positivity) hr hbinUpper Mp U hrinv
      _ ≤ _ := hpow _ _ hMi2
  have hdata := d.geometry_budgets (p.stripParent i) (h.stripParent_valid i) h.1 hr
    (one_le_pow₀ hN1 : 1 ≤ N ^ J) (show 1 ≤ 8 * E by linarith)
    (hpow Mp J hJ) htime he hn hen hbinUpper hβ
    (show 2 * E + 2 * (3 * E) ≤ 8 * E by linarith)
    (show 4 * (N ^ J) ^ 2 * (8 * E) ≤ N ^ stripOutputExponent Mp J U from by
      calc
        _ = 32 * (N ^ J) ^ 2 * E := by ring
        _ ≤ N ^ (2 * J + 6) := strip_center_power_budget hN hEN J
        _ ≤ _ := hpow _ _ hMi1)
    ((strip_entry_power_budget hN h.1 hE hκE hEN (by positivity) hnormal hr hr1 Mp U hrinv).trans
      (hpow _ _ (by omega)))
    (hsize.trans hsizeSlack)
  apply h.width_of_strip_refinement hN1 hB i hi hdepth hrL d hM (hκE.trans hEslack)
    hfour hr he hn hen hbins hformat hcard hdata (hlist.trans hlistSlack)
    (hfactor.trans hdetSlack) hradius hgain
  apply le_trans (ENNReal.ofReal_le_ofReal ?_) hmass
  rw [Real.rpow_neg hN0]
  simpa only [one_div] using one_div_le_one_div_of_le
    (show 0 < 100 * E ^ 8 by positivity) hslack

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
