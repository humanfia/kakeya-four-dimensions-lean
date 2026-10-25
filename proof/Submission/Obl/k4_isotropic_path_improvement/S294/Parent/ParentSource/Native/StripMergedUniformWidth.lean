-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.StripMergedUniformWidth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/StripMergedUniformWidth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/StripMergedUniformWidth.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/StripMergedUniformWidth.lean.
-- Existing source attributions are preserved below.

/- Adapted from LOT obligation o116, branch x0389, commit e3859a9b;
   original file Submission/Obl/k4_isotropic_residual_candidates/StripMergedUniformWidth.lean.
   Original comments and attributions are preserved below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedSystem
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripMergedBudgets
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.StripUniformWidth

/-! The heavy net and fine witness unions may have fixed polynomial size.
Only the genuine path, list and frame envelope must be subpower. All output
polynomial exponents are chosen before the requested width slack. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips
open scoped BigOperators RealInnerProductSpace

def stripMergedOutputExponent (Mp J U V F : ℕ) : ℕ :=
  max (2 * J + 6) (Mp + U + V + F + 9)

theorem PathData.Valid.width_of_merged_strip_envelope
    {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {Ev : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (h : p.Valid N L ω ν Ev B f κ₁ m s δ₀ Mp Dp σ)
    (hN : 2 ≤ N) (hB : ∀ w, 0 ≤ B w)
    (i : ℕ) (hi : i < m) {gain τ loss stripExponent E w Hs : ℝ} {Ds : ℕ}
    (hdepth : p.r i + 2 * gain * L ≤ L)
    (d : StripRefinement (p.StripLevel i)) (J U V F : ℕ)
    (hJ : Mp ≤ J) (htime : (2 : ℝ) ^ p.T i ≤ N ^ J)
    (hE : 1 ≤ E) (hEN : E ≤ N) (hκE : p.κ ≤ E)
    (hr : 0 < d.radius) (hr1 : d.radius ≤ 1) (hrinv : d.radius⁻¹ ≤ N ^ U)
    (he : ∀ b j, ‖d.tangent b j‖ = 1) (hn : ∀ b j, ‖d.normal b j‖ = 1)
    (hen : ∀ b j, inner ℝ (d.tangent b j) (d.normal b j) = 0)
    (hbinUpper : (d.bins : ℝ) * d.radius ≤ 2 * E)
    (hβ : ∀ b j, |d.offset b j| ≤ 3 * E)
    (hcount : (d.count : ℝ) ≤ N ^ V) (hnormal : (d.normalBudget : ℝ) ≤ 5 * E)
    (hwidth : w + 3 * (1 + 2 * p.κ) * d.radius ≤ (d.normalBudget : ℝ) * d.radius)
    (success : p.StripLevel i → StripParameterCode → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hSmeas : ∀ b q, MeasurableSet (success b q)) (hHs : 0 ≤ Hs) (hHspow : Hs ≤ N ^ F)
    (hS : ∀ b q copy, Submission.Lib.K4XInterface.gfmt 7 Hs Ds
      {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈ success b q})
    (paramList : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset d.MergedParameterLabel)
    (hknown : ∀ a x, x ∈ d.mergedIncidence (p.stripParent i) w success a →
      d.mergedParameterLabel a ∈ paramList (p.γ a.1)
        (Submission.Lib.K4XInterface.gobs (B (p.γ a.1))
          (Submission.Lib.K4XInterface.gδ N L) x))
    (hparam : ∀ γ o, ((paramList γ o).card : ℝ) ≤ 3 * E ^ 3)
    (hslack : 100 * E ^ 8 ≤ N ^ τ) (hdetSlack : 6 * E ^ 2 ≤ N ^ loss)
    (hradius : d.radius ≤ N ^ (-stripExponent))
    (hgain : δ₀ * L + loss + gain * L ≤ stripExponent)
    (hmass : ENNReal.ofReal ((100 * E ^ 8)⁻¹) ≤
      ∑ a : d.MergedLabel, ENNReal.ofReal (ω (p.γ a.1)) *
        (ν (p.γ a.1)).prod volume (d.mergedIncidence (p.stripParent i) w success a)) :
    width N L W ω ν Ev B m p.r p.T p.nw gain (stripMergedOutputExponent Mp J U V F)
      (max (max Dp 1) Ds) τ := by
  classical
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hMi1 : 2 * J + 6 ≤ stripMergedOutputExponent Mp J U V F := le_max_left _ _
  have hMi2 : Mp + U + V + F + 9 ≤ stripMergedOutputExponent Mp J U V F := le_max_right _ _
  have hM : Mp ≤ stripMergedOutputExponent Mp J U V F := by omega
  have hpow (a b : ℕ) (hab : a ≤ b) : N ^ a ≤ N ^ b := pow_le_pow_right₀ hN1 hab
  obtain ⟨hfour, hEslack, hsizeSlack, hlistSlack, _⟩ := strip_slack_of_power_envelope hE hslack
  obtain ⟨hfactor, hsize, _⟩ := strip_slack_envelope h.1 hE hκE
    (show 0 ≤ (d.normalBudget : ℝ) by positivity) hnormal
    (count := 0) (by norm_num) (by positivity) hr.le hr1
  have hformat : 2 * N ^ Mp + 2 * (d.count : ℝ) + 2 + Hs ≤
      N ^ stripMergedOutputExponent Mp J U V F :=
    (strip_merged_format_power_budget hN Mp V F hcount hHspow).trans
      (hpow _ _ (by omega))
  have hcard : (Fintype.card (p.StripLevel i) : ℝ) *
      ((d.count : ℝ) * (2 * (d.bins : ℝ) + 1)) ≤ N ^ stripMergedOutputExponent Mp J U V F := by
    have hc : Fintype.card (p.StripLevel i) ≤ p.C := by
      simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun b : Fin p.C => p.lev b = i)
    have hc' : (Fintype.card (p.StripLevel i) : ℝ) ≤ N ^ Mp :=
      (Nat.cast_le.mpr hc).trans h.2.2.1
    calc
      _ ≤ N ^ Mp * ((d.count : ℝ) * (2 * (d.bins : ℝ) + 1)) := by gcongr
      _ ≤ N ^ (Mp + V + U + 4) := strip_merged_card_power_budget hN hE hEN
        (by positivity) Mp U V hcount (by positivity) hr hbinUpper hrinv
      _ ≤ _ := hpow _ _ (by omega)
  have hdata := d.geometry_budgets (p.stripParent i) (h.stripParent_valid i) h.1 hr
    (one_le_pow₀ hN1 : 1 ≤ N ^ J) (show 1 ≤ 8 * E by linarith)
    (hpow Mp J hJ) htime he hn hen hbinUpper hβ
    (show 2 * E + 2 * (3 * E) ≤ 8 * E by linarith)
    (show 4 * (N ^ J) ^ 2 * (8 * E) ≤ N ^ stripMergedOutputExponent Mp J U V F from by
      calc
        _ = 32 * (N ^ J) ^ 2 * E := by ring
        _ ≤ N ^ (2 * J + 6) := strip_center_power_budget hN hEN J
        _ ≤ _ := hpow _ _ hMi1)
    ((strip_entry_power_budget hN h.1 hE hκE hEN (by positivity) hnormal hr hr1 Mp U hrinv).trans
      (hpow _ _ (by omega))) (hsize.trans hsizeSlack)
  refine ⟨i, hi, hdepth, ?_⟩
  apply d.system_of_merged_family (p.stripParent i) (h.stripParent_valid i) hN1 hM h.1
    (hκE.trans hEslack) hfour hB hr he hn hen (h.stripParent_velocity_bound i) hwidth
    success hSmeas hHs hS hformat (by exact_mod_cast hcard) hdata (h.stripParent_disjoint i)
    paramList hknown ?_
    (fun Q => |Q.det| * (4 : ℝ) ^ p.T i ≤ N ^ (-(p.nw i + gain * L))) ?_ ?_
  · intro γ o
    have hl := strip_merged_list_envelope hE (hparam γ o) hnormal (by positivity)
    exact_mod_cast hl.trans hlistSlack
  · intro a
    exact strip_determinant_power_bound (p.stripParent i a.1).frame (p.T i) hN1
      (by linarith [h.1]) (by positivity) hr (he _ _) (hn _ _) (hen _ _)
      (h.stripParent_determinant_bound i a.1) (hfactor.trans hdetSlack) hradius hgain
  · apply le_trans (ENNReal.ofReal_le_ofReal ?_) hmass
    rw [Real.rpow_neg hN0]
    simpa only [one_div] using one_div_le_one_div_of_le
      (show 0 < 100 * E ^ 8 by positivity) hslack

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
