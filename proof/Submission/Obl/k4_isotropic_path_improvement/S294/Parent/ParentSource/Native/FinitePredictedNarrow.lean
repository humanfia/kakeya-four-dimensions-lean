-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Native.FinitePredictedNarrow, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Native/FinitePredictedNarrow.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Native/FinitePredictedNarrow.lean.
All earlier source attributions below are retained. -/
-- Adapted from this LOT tree, o204, branch x0749, commit e4d9e4b8c9b3;
-- source Submission/Obl/k4_uniform_sampled_isotropic_branches/Native/FinitePredictedNarrow.lean.
-- Existing source attributions are preserved below.

import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.FiniteMergedPrediction
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.MergedAtlasEnvelope
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.OriginalAtlasMass

/-! A uniformly finite family of actual old-fine-packet strip predictions
constructs the EXACT frozen weak narrow atlas. Original H mass and the whole
old-ancestor trajectory/incidence containments are retained. -/

noncomputable section

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native

open MeasureTheory Set
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface
open scoped BigOperators RealInnerProductSpace

theorem PathData.Valid.narrow_of_finitely_predicted_strip_cover
    {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {Ev : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν Ev B f κ₁ m s δ₀ Mp Dp σ)
    (hN : 2 ≤ N) (hB : ∀ w, 0 ≤ B w)
    (i stop : ℕ) (hi : i < m) (himiddle : 1 / 4 ≤ s i ∧ s i ≤ 1 / 2)
    {gain u0 β α loss stripExponent E width r₀ r₁ : ℝ}
    (hβlow : u0 ≤ β) (hβhigh : β ≤ 4 * gain)
    (d : StripRefinement (p.StripLevel i)) (J U V Jpred : ℕ)
    (hJ : Mp ≤ J) (htime : (2 : ℝ) ^ p.T i ≤ N ^ J)
    (hE : 100 ≤ E) (hEN : E ≤ N) (hκE : p.κ ≤ E) (hmκE : (m : ℝ) * p.κ ≤ E)
    (hpred : 250 * (Jpred : ℝ) ≤ E)
    (hr : 0 < d.radius) (hr1 : d.radius ≤ 1) (hrinv : d.radius⁻¹ ≤ N ^ U)
    (he : ∀ b j, ‖d.tangent b j‖ = 1) (hn : ∀ b j, ‖d.normal b j‖ = 1)
    (hen : ∀ b j, inner ℝ (d.tangent b j) (d.normal b j) = 0)
    (hbins : p.κ ≤ (d.bins : ℝ) * d.radius)
    (hbinUpper : (d.bins : ℝ) * d.radius ≤ 2 * E)
    (hoffset : ∀ b j, |d.offset b j| ≤ 3 * E)
    (hcount : (d.count : ℝ) ≤ N ^ V) (hnormal : (d.normalBudget : ℝ) ≤ 5 * E)
    (hwidth : width + 3 * (1 + 2 * p.κ) * d.radius ≤ (d.normalBudget : ℝ) * d.radius)
    (hmeshes : r₁ ≤ d.radius) (hrawWidth : r₀ + (1 + 2 * p.κ) * r₁ ≤ width)
    (rawNormal : Fin Jpred → p.StripLevel i → Fin p.C → StripSpace)
    (rawOffset : Fin Jpred → p.StripLevel i → Fin p.C → ℝ)
    (R H : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (hRH : ∀ w, R w ⊆ H w)
    (hcover : ∀ w, R w ⊆ {x | ∃ (b : p.StripLevel i) (a : Fin p.C) (t : Fin Jpred),
      p.γ b = w ∧ x ∈ (p.stripParent i b).incidences ∧
      x ∈ p.packetWitness m stop (p.γ b) a ∧
      packetVelocity (((2 : ℝ) ^ p.T i)⁻¹) (p.stripParent i b).frame
        (p.stripParent i b).velocity x.1 ∈ affineStrip (rawNormal t b a) (rawOffset t b a) r₀ ∧
      (∃ j, stripParametersClose (rawNormal t b a) (rawOffset t b a)
        (d.normal b j) (d.offset b j) r₁) ∧
      packetVelocity (((2 : ℝ) ^ p.T i)⁻¹) (p.stripParent i b).frame
        (p.stripParent i b).velocity x.1 ∉
          stripFarOverlap (d.normal b) (d.offset b) width d.radius (2 * p.κ)})
    (hslack : 100 * E ^ 8 ≤ N ^ α) (hdetSlack : 6 * E ^ 2 ≤ N ^ loss)
    (hradius : d.radius ≤ N ^ (-stripExponent))
    (hgain : δ₀ * L + loss + β * L ≤ stripExponent)
    (hmass : ENNReal.ofReal (p.κ⁻¹ / 8) ≤
      ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (R w)) :
    narrow N L W ω ν Ev B m s p.r p.T p.nw gain u0 p.κ
      (stripMergedOutputExponent Mp J U V (4 * Mp + 3)) (max Dp 1) α
      p.C p.lev p.γ p.j p.A p.F H := by
  classical
  let success := FiniteMergedPrediction.success d rawNormal rawOffset m stop
  let paramList := FiniteMergedPrediction.parameterList d rawNormal rawOffset m
  have hSmeas (b : p.StripLevel i) (q : StripParameterCode) : MeasurableSet (success b q) :=
    FiniteMergedPrediction.measurableSet_success d rawNormal rawOffset hp stop b q
  have hS (b : p.StripLevel i) (q : StripParameterCode) (copy : ℕ) :
      gfmt 7 ((Jpred : ℝ) * N ^ (4 * Mp + 2)) Dp
        {z : Fin 7 → ℝ | ((copy, fun j : Fin 6 => z j.castSucc), z 6) ∈ success b q} :=
    FiniteMergedPrediction.success_section_format d rawNormal rawOffset hp hN stop b q copy
  have hSpow : (Jpred : ℝ) * N ^ (4 * Mp + 2) ≤ N ^ (4 * Mp + 3) := by
    have hJpred : (Jpred : ℝ) ≤ N :=
      (by nlinarith [show (0 : ℝ) ≤ Jpred from Nat.cast_nonneg _] : (Jpred : ℝ) ≤ E).trans hEN
    calc
      _ ≤ N * N ^ (4 * Mp + 2) := mul_le_mul_of_nonneg_right hJpred (by positivity)
      _ = _ := by
        rw [show 4 * Mp + 3 = (4 * Mp + 2) + 1 by omega, pow_succ N (4 * Mp + 2)]
        ring
  have hknown : ∀ a x, x ∈ d.mergedIncidence (p.stripParent i) width success a →
      d.mergedParameterLabel a ∈ paramList (p.γ a.1) (gobs (B (p.γ a.1)) (gδ N L) x) := by
    intro a x hx
    exact FiniteMergedPrediction.merged_parameter_known d rawNormal rawOffset hp stop width (gδ N L) rfl a x hx
  have hparam (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
      ((paramList w o).card : ℝ) ≤ 3 * E ^ 3 := by
    have h := FiniteMergedPrediction.parameterList_card d rawNormal rawOffset hp w o
    have hmk : 0 ≤ (m : ℝ) * p.κ := mul_nonneg (Nat.cast_nonneg _) (by linarith [hp.1])
    have hsquare : ((m : ℝ) * p.κ) ^ 2 ≤ E ^ 2 := pow_le_pow_left₀ hmk hmκE 2
    calc
      _ ≤ (Jpred : ℝ) * (250 * ((m : ℝ) * p.κ) ^ 2) := h
      _ = (250 * (Jpred : ℝ)) * (((m : ℝ) * p.κ) ^ 2) := by ring
      _ ≤ E * E ^ 2 := mul_le_mul hpred hsquare (sq_nonneg _) (by linarith)
      _ ≤ 3 * E ^ 3 := by nlinarith [pow_nonneg (by linarith : 0 ≤ E) 3]
  have hcovered := FiniteMergedPrediction.original_residual_covered d rawNormal rawOffset hp stop hr hn hbins
    hmeshes hrawWidth R hcover
  have hmerged := d.weighted_merged_original_inter_mass_le (p.stripParent i)
    (fun w => (ν w).prod volume) ω width success R H hRH hcovered
  let aux := fun (w : Fin W) (jt : Fin (2 ^ p.T i)) (At : Set (ℕ × (Fin 6 → ℝ)))
      (Ft : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)) (known : Prop) =>
    known ∧ ∃ b : Fin p.C, p.lev b = i ∧ p.γ b = w ∧ p.j b = (jt : ℕ) ∧ At ⊆ p.A b ∧ Ft ⊆ p.F b
  have haux : ∀ a : d.MergedLabel, ∀ known : Prop, known →
      aux (p.γ a.1) (p.stripParent i a.1).timeIndex
        (d.mergedAssignment (p.stripParent i) width a) (d.mergedIncidence (p.stripParent i) width success a) known := by
    intro a known hknown
    refine ⟨hknown, a.1.val, a.1.property, rfl, ?_,
      d.mergedAssignment_subset (p.stripParent i) width a,
      d.mergedIncidence_subset (p.stripParent i) width success a⟩
    have hj : p.j a.1.val < 2 ^ p.T i := by
      simpa only [a.1.property] using (hp.2.2.2.2.2.2.2 a.1.val).2.1
    simp only [PathData.stripParent, Nat.mod_eq_of_lt hj]
  have hfinal := hp.atlas_of_merged_strip_envelope hN hB i d J U V (4 * Mp + 3)
    hJ htime (by linarith) hEN hκE hr hr1 hrinv he hn hen hbinUpper hoffset hcount hnormal hwidth
    success hSmeas (by positivity) hSpow hS paramList hknown hparam hslack hdetSlack hradius hgain
    aux haux (ENNReal.ofReal (p.κ⁻¹ / 8)) (fun w F => ((ν w).prod volume) (F ∩ H w)) (hmass.trans hmerged)
  refine ⟨i, β, hi, himiddle.1, himiddle.2, hβlow, hβhigh, ?_⟩
  simpa only [max_eq_left (le_max_left Dp 1)] using hfinal

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
