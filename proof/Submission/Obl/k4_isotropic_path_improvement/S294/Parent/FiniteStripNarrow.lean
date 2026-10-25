-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.FiniteStripNarrow, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/FiniteStripNarrow.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.MergedAtlasEnvelope
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native.OriginalAtlasMass

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FiniteStripNarrow

open MeasureTheory Set
open ParentSource ParentSource.Native
open Submission.Lib.K4VelocityStrips Submission.Lib.K4XInterface

noncomputable section

/-- A small finite strip family attached to each actual middle-quarter
packet gives the frozen original narrow atlas. Its whole-trajectory
priority partition keeps all covered mass; no overlap deletion or new
posterior law is needed. -/
theorem narrow_of_finite_refinement
    {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
    (hN : 2 ≤ N) (hB : ∀ w, 0 ≤ B w)
    (i : ℕ) (hi : i < m) (hrL : p.r i ≤ L)
    (himiddle : 1 / 4 ≤ s i ∧ s i ≤ 1 / 2)
    {gain u0 β α loss stripExponent envelope width : ℝ}
    (hβlow : u0 ≤ β) (hβhigh : β ≤ 4 * gain)
    (d : StripRefinement (p.StripLevel i)) (J U V : ℕ)
    (hJ : Mp ≤ J) (htime : (2 : ℝ) ^ p.T i ≤ N ^ J)
    (hE : 1 ≤ envelope) (hEN : envelope ≤ N) (hκE : p.κ ≤ envelope)
    (hr : 0 < d.radius) (hr1 : d.radius ≤ 1) (hrinv : d.radius⁻¹ ≤ N ^ U)
    (he : ∀ b j, ‖d.tangent b j‖ = 1) (hn : ∀ b j, ‖d.normal b j‖ = 1)
    (hen : ∀ b j, inner ℝ (d.tangent b j) (d.normal b j) = 0)
    (hbins : p.κ ≤ (d.bins : ℝ) * d.radius)
    (hbinUpper : (d.bins : ℝ) * d.radius ≤ 2 * envelope)
    (hoffset : ∀ b j, |d.offset b j| ≤ 3 * envelope)
    (hcount : (d.count : ℝ) ≤ N ^ V)
    (hsmallCount : (d.count : ℝ) ≤ 3 * envelope ^ 2)
    (hnormal : (d.normalBudget : ℝ) ≤ 5 * envelope)
    (hwidth : width + 3 * (1 + 2 * p.κ) * d.radius ≤
      (d.normalBudget : ℝ) * d.radius)
    (R H : Fin W → Set Ev) (hRH : ∀ w, R w ⊆ H w)
    (hcover : ∀ w, R w ⊆ {x | ∃ b : p.StripLevel i,
      p.γ b = w ∧ x ∈ p.F b ∧
      packetVelocity (((2 : ℝ) ^ p.T i)⁻¹) (p.Q b) (p.u b) x.1 ∈
        ⋃ j, affineStrip (d.normal b j) (d.offset b j) width})
    (hslack : 100 * envelope ^ 8 ≤ N ^ α)
    (hdetSlack : 6 * envelope ^ 2 ≤ N ^ loss)
    (hradius : d.radius ≤ N ^ (-stripExponent))
    (hgain : δ₀ * L + loss + β * L ≤ stripExponent)
    (hmass : ENNReal.ofReal (p.κ⁻¹ / 8) ≤
      ∑ w, ENNReal.ofReal (ω w) * ((ν w).prod volume) (R w)) :
    ParentSource.narrow N L W ω ν E B m s p.r p.T p.nw gain u0 p.κ
      (stripMergedOutputExponent Mp J U V 0) (max Dp 1) α
      p.C p.lev p.γ p.j p.A p.F H := by
  classical
  have hN1 : 1 ≤ N := by linarith
  let success : p.StripLevel i → StripParameterCode → Set Ev := fun _ _ => univ
  let paramList : Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset d.MergedParameterLabel :=
    fun w o => (p.stripParentList N L i w o).sigma (fun _ => Finset.univ)
  have hknown : ∀ a x, x ∈ d.mergedIncidence (p.stripParent i) width success a →
      d.mergedParameterLabel a ∈ paramList (p.γ a.1) (gobs (B (p.γ a.1)) (gδ N L) x) := by
    intro a x hx
    apply Finset.mem_sigma.mpr
    exact ⟨hp.stripParentList_known hN1 i hrL a.1 x hx.1.1,Finset.mem_univ _⟩
  have hparam (w : Fin W) (o : EuclideanSpace ℝ (Fin 3) × ℤ) :
      ((paramList w o).card : ℝ) ≤ 3 * envelope ^ 3 := by
    have hcard : (paramList w o).card ≤ (p.stripParentList N L i w o).card * d.count := by
      dsimp only [paramList]
      rw [Finset.card_sigma]
      calc
        _ ≤ ∑ _b ∈ p.stripParentList N L i w o, d.count := by
          apply Finset.sum_le_sum
          intro b hb
          simpa only [Finset.card_univ] using
            stripCodeLabel_card_le d.radius (d.normal b) (d.offset b)
        _ = _ := by simp
    calc
      _ ≤ ((p.stripParentList N L i w o).card : ℝ) * d.count := by exact_mod_cast hcard
      _ ≤ p.κ * d.count := mul_le_mul_of_nonneg_right
        (hp.stripParentList_card i w o) (Nat.cast_nonneg _)
      _ ≤ envelope * (3 * envelope ^ 2) := mul_le_mul hκE hsmallCount
        (Nat.cast_nonneg _) (by linarith)
      _ = _ := by ring
  have hcovered := d.original_residual_covered_by_merged_incidence (p.stripParent i)
    (hp.stripParent_valid i) hr hn hbins success R (by
      intro w x hx
      obtain ⟨b,hbw,hb,hv⟩ := hcover w hx
      refine ⟨b,hbw,hb,?_,fun _ _ => mem_univ _⟩
      exact hv)
  have hmerged := d.weighted_merged_original_inter_mass_le (p.stripParent i)
    (fun w => (ν w).prod volume) ω width success R H hRH hcovered
  let aux := fun (w : Fin W) (jt : Fin (2 ^ p.T i)) (At : Set Ln)
      (Ft : Set Ev) (known : Prop) => known ∧
    ∃ b : Fin p.C, p.lev b = i ∧ p.γ b = w ∧ p.j b = (jt : ℕ) ∧ At ⊆ p.A b ∧ Ft ⊆ p.F b
  have haux : ∀ a : d.MergedLabel, ∀ known : Prop, known →
      aux (p.γ a.1) (p.stripParent i a.1).timeIndex
        (d.mergedAssignment (p.stripParent i) width a)
        (d.mergedIncidence (p.stripParent i) width success a) known := by
    intro a known hknown
    refine ⟨hknown,a.1.val,a.1.property,rfl,?_,
      d.mergedAssignment_subset (p.stripParent i) width a,
      d.mergedIncidence_subset (p.stripParent i) width success a⟩
    have hj : p.j a.1.val < 2 ^ p.T i := by
      simpa only [a.1.property] using (hp.2.2.2.2.2.2.2 a.1.val).2.1
    simp only [PathData.stripParent,Nat.mod_eq_of_lt hj]
  have hfinal := hp.atlas_of_merged_strip_envelope hN hB i d J U V 0 hJ htime
    hE hEN hκE hr hr1 hrinv he hn hen hbinUpper hoffset hcount hnormal hwidth success
    (fun _ _ => MeasurableSet.univ) (by norm_num : (0 : ℝ) ≤ 0)
    (show (0 : ℝ) ≤ N ^ 0 by positivity)
    (fun _ _ _ => gfmt_univ 7 0 (by norm_num) 0)
    paramList hknown hparam hslack hdetSlack hradius hgain aux haux
    (ENNReal.ofReal (p.κ⁻¹ / 8)) (fun w F => ((ν w).prod volume) (F ∩ H w))
    (hmass.trans hmerged)
  refine ⟨i,β,hi,himiddle.1,himiddle.2,hβlow,hβhigh,?_⟩
  simpa only [max_eq_left (le_max_left Dp 1),max_eq_left (Nat.zero_le _)] using hfinal

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.FiniteStripNarrow
