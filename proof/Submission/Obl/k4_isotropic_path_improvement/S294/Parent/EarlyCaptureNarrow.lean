-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.EarlyCaptureNarrow, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/EarlyCaptureNarrow.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FiniteStripNarrow
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.AncestorPredictions

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.EarlyCaptureNarrow

open MeasureTheory Set
open ParentSource ParentSource.Native
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface

noncomputable section

/-- Construct the actual finite strip refinement from the supplied
unit strips. Its binning and all whole-block and format estimates are
those of the original path, and all covered original mass is retained. -/
theorem narrow_of_unit_strips
    {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hN : 2 ≤ N) (hB : ∀ w, 0 ≤ B w)
    (i : ℕ) (hi : i < m) (hrL : p.r i ≤ L)
    (himiddle : 1 / 4 ≤ s i ∧ s i ≤ 1 / 2)
    {gain u0 β α loss stripExponent envelope width radius : ℝ}
    (hβlow : u0 ≤ β) (hβhigh : β ≤ 4 * gain)
    (Jpred : ℕ) (normal : p.StripLevel i → Fin Jpred → StripSpace)
    (offset : p.StripLevel i → Fin Jpred → ℝ)
    (hn : ∀ b j, ‖normal b j‖ = 1)
    (hoffset : ∀ b j, |offset b j| ≤ 2 * p.κ + width)
    (J U V : ℕ) (hJ : Mp ≤ J) (htime : (2 : ℝ) ^ p.T i ≤ N ^ J)
    (hEN : envelope ≤ N) (hκE : 3 * p.κ ≤ envelope)
    (hr : 0 < radius) (hr1 : radius ≤ 1) (hrinv : radius⁻¹ ≤ N ^ U)
    (hwidth : width ≤ radius) (hcount : (Jpred : ℝ) ≤ N ^ V)
    (hsmallCount : (Jpred : ℝ) ≤ 3 * envelope ^ 2)
    (R H : Fin W → Set Ev) (hRH : ∀ w, R w ⊆ H w)
    (hcover : ∀ w, R w ⊆ {x | ∃ b : p.StripLevel i,
      p.γ b = w ∧ x ∈ p.F b ∧ p.normalizedVelocity b x ∈
        ⋃ j, affineStrip (normal b j) (offset b j) width})
    (hslack : 100 * envelope ^ 8 ≤ N ^ α)
    (hdetSlack : 6 * envelope ^ 2 ≤ N ^ loss)
    (hradius : radius ≤ N ^ (-stripExponent))
    (hgain : δ₀ * L + loss + β * L ≤ stripExponent)
    (hmass : ENNReal.ofReal (p.κ⁻¹ / 8) ≤
      ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (R w)) :
    ParentSource.narrow N L W ω ν E B m s p.r p.T p.nw gain u0 p.κ
      (stripMergedOutputExponent Mp J U V 0) (max Dp 1) α
      p.C p.lev p.γ p.j p.A p.F H := by
  let D := ⌈4 + 6 * p.κ⌉₊
  let ref : StripRefinement (p.StripLevel i) := {
    count := Jpred
    bins := stripMidpointBinCount p.κ radius
    normalBudget := D
    radius := radius
    normal := normal
    tangent := fun b j => stripTangent (normal b j)
    offset := offset }
  have hκ : 0 ≤ p.κ := by linarith [hp.1]
  have hE : 1 ≤ envelope := by linarith [hp.1]
  have hDlow : 4 + 6 * p.κ ≤ (D : ℝ) := Nat.le_ceil _
  have hDup : (D : ℝ) ≤ 5 + 6 * p.κ := by
    have hh := (Nat.ceil_lt_add_one (show 0 ≤ 4 + 6 * p.κ by positivity)).le
    dsimp only [D]
    linarith
  apply FiniteStripNarrow.narrow_of_finite_refinement hp hN hB i hi hrL himiddle
    (width := width) (envelope := envelope)
    hβlow hβhigh ref J U V hJ htime hE hEN (by linarith) hr hr1 hrinv
    (fun b j => (stripTangent_norm _).trans (hn b j)) hn
    (fun b j => stripTangent_inner _) (stripMidpointBinCount_lower hr) ?_ ?_
    hcount hsmallCount (by dsimp only [ref]; linarith [hp.1]) ?_ R H hRH ?_
    hslack hdetSlack hradius hgain hmass
  · exact (stripMidpointBinCount_upper hκ hr).trans (by linarith [hp.1])
  · intro b j
    exact (hoffset b j).trans (by linarith [hp.1])
  · dsimp only [ref]
    have hh := mul_le_mul_of_nonneg_right hDlow hr.le
    nlinarith
  · intro w x hx
    obtain ⟨b,hbw,hb,hv⟩ := hcover w hx
    refine ⟨b,hbw,hb,?_⟩
    simpa only [packetVelocity,PathData.normalizedVelocity,b.property,ParentSource.Native.v,gv]
      using hv

/-- An early saturated capture gives the EXACT frozen middle-quarter
narrow exit. The strips are constructed from its actual bounded
prediction arrays on fixed descendant ancestors; all original captured
mass, assignments and full-block geometry are retained. -/
theorem narrow_of_early_capture {T : Type*}
    {d : ProblemData} (hd : d.Valid) {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A r fraction : ℝ}
    {θ : ENNReal} {F : PaletteFamily Q i stop a A θ}
    (P : PaletteStripSaturation F r fraction)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b = m - 1 ∧ p.γ b = w ∧ z ∈ p.F b})
    (hi : i ≤ stop) (hstop : stop < m) (targetLevel : ℕ)
    (htarget : targetLevel < m) (horder : stop ≤ targetLevel)
    (hrL : p.r targetLevel ≤ d.L)
    (himiddle : 1 / 4 ≤ s targetLevel ∧ s targetLevel ≤ 1 / 2)
    (Jpred : ℕ) (hJpred : fraction⁻¹ ≤ (Jpred : ℝ)) (hr : 0 ≤ r)
    {width radius gain u0 β α loss stripExponent envelope : ℝ}
    (hw : 0 ≤ width)
    (hscale : r * (p.κ ^ 2 * d.N k ^ (2 * δ₀ * d.L)) ≤ width)
    (hβlow : u0 ≤ β) (hβhigh : β ≤ 4 * gain)
    (J U V : ℕ) (hJ : Mp ≤ J) (htime : (2 : ℝ) ^ p.T targetLevel ≤ d.N k ^ J)
    (hEN : envelope ≤ d.N k) (hκE : 3 * p.κ ≤ envelope)
    (hradius0 : 0 < radius) (hradius1 : radius ≤ 1) (hrinv : radius⁻¹ ≤ d.N k ^ U)
    (hwidth : width ≤ radius) (hcount : (Jpred : ℝ) ≤ d.N k ^ V)
    (hsmallCount : (Jpred : ℝ) ≤ 3 * envelope ^ 2)
    (hslack : 100 * envelope ^ 8 ≤ d.N k ^ α)
    (hdetSlack : 6 * envelope ^ 2 ≤ d.N k ^ loss)
    (hradius : radius ≤ d.N k ^ (-stripExponent))
    (hgain : δ₀ * d.L + loss + β * d.L ≤ stripExponent)
    (hmass : ENNReal.ofReal (9 * p.κ⁻¹ / 64) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.captureResidual w)) :
    ParentSource.narrow (d.N k) d.L (d.W k) (d.ω k) (d.ν k) (d.E k) (d.B k)
      m s p.r p.T p.nw gain u0 p.κ (stripMergedOutputExponent Mp J U V 0) (max Dp 1) α
      p.C p.lev p.γ p.j p.A p.F H := by
  have hN : 1 ≤ d.N k := le_trans (by norm_num) (hd.1 k)
  obtain ⟨normal,offset,hn,hoff,hcover⟩ :=
    AncestorPredictions.exists_descendant_capture_strips P hp hN hH hi hstop targetLevel
      htarget horder Jpred hJpred hr hw hscale
  have hκ : 0 < p.κ := zero_lt_one.trans_le hp.1
  have hmass' : ENNReal.ofReal (p.κ⁻¹ / 8) ≤
      ∑ w, ENNReal.ofReal (d.ω k w) * ((d.ν k w).prod volume) (P.cleanCapture w) := by
    rw [P.cleanCapture_original_mass hp]
    exact (ENNReal.ofReal_le_ofReal (by nlinarith [inv_pos.mpr hκ])).trans hmass
  exact narrow_of_unit_strips hp (hd.1 k) (fun w => (hd.parent_signal_data k w).1.le)
    targetLevel htarget hrL himiddle hβlow hβhigh Jpred normal offset hn hoff J U V hJ htime
    hEN hκE hradius0 hradius1 hrinv hwidth hcount hsmallCount (P.cleanCapture) H
    (fun w x hx => P.captureResidual_subset_H w hx.1.1) hcover
    hslack hdetSlack hradius hgain hmass'

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.EarlyCaptureNarrow
