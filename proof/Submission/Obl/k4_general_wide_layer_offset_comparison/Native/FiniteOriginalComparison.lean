-- Adapted from this LOT tree, obligation o200, branch x0934, commit 2510f406, file Submission/Obl/k4_finite_projected_horizontal_candidates/FiniteOriginalComparison.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.Native.
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.PrunedDomainTables
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.GlobalPartnerLists
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ReferenceNumerators
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.GlobalFamilyAgreement

/-! Complete finite-domain comparison with original true/projected label lists. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set
open scoped ENNReal Classical

noncomputable section

/-- Prune both original colors, compare their actual source laws on all domains,
and recover the original partner lists on one retained submeasure. Original
true labels have two native branches; projected labels have one polynomial. -/
theorem finite_original_comparison_with_agreement {Ω Q : Type*} [MeasurableSpace Ω]
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → Q) (hcode : Measurable code)
    {D N₁ N₂ : ℕ} {d a B F L ε C Λ Rtotal : ℝ} (K : NNReal)
    (M : ∀ q, ComparisonMesh (codePieces μ code q))
    (signal : Ω → ℝ) (hs : Measurable signal)
    (f₁ f₂ : ∀ q, OriginalSheetFamily (codePieces μ code q) D a K (M q).base signal)
    (trueDecode : ∀ q, Fin (f₁ q).n → Fin N₁ × Bool)
    (projectedDecode : ∀ q, Fin (f₂ q).n → Fin N₂)
    (htrue : ∀ q, Function.Injective (trueDecode q))
    (hprojected : ∀ q, Function.Injective (projectedDecode q))
    (ha : 0 < a) (hB : 0 < B) (hF : 0 < F)
    (hL : 1 ≤ L) (hLfloor : 14 * B * F ≤ L)
    (T : Q → ℝ) (hT : ∀ q, 0 < T q)
    (palette : Q → ℝ≥0∞) (hp : ∀ q, palette q ≠ 0) (hpt : ∀ q, palette q ≠ ⊤)
    (hresolve : ∀ q, 2 * (K : ℝ) * (M q).diameter ≤ a / 2)
    (hvolume : ∀ q, (∑ _j : Fin (M q).n, (M q).vol) ≤ 1)
    (hnative : ∀ q (R : ℝ), a ≤ R → ∀ j x,
      codePieces μ code q {p | (M q).code p = j ∧ ⌊signal p / R⌋ = x} ≤
        (ENNReal.ofReal (B * T q * (R / a) ^ d) * palette q) * (M q).vol)
    (href : (∑ q, (((f₁ q).n : ℝ) * (T q * (palette q).toReal) +
      ((f₂ q).n : ℝ) * (T q * (palette q).toReal))) ≤ Rtotal)
    (H : ComparisonEstimate D d ε C) (hC : 0 ≤ C)
    (hΛ : C * L ^ (1 / ε) ≤ Λ) (hΛ1 : 1 ≤ Λ) :
    ∃ (ρ : Measure Ω) (forward : Q → Fin N₁ → Finset (Fin N₂))
      (reverse : Q → Fin N₂ → Finset (Fin N₁)),
      ρ ≤ μ ∧
      μ univ ≤ ρ univ + ENNReal.ofReal (Rtotal / F) +
        ENNReal.ofReal (C * (6 * B) * Λ ^ (-ε) * Rtotal) ∧
      (∀ q i, ((forward q i).card : ℝ) ≤ 2 * (L * Λ ^ d)) ∧
      (∀ q j, ((reverse q j).card : ℝ) ≤ L * Λ ^ d) ∧
      (∀ᵐ p ∂ρ,
        projectedDecode (code p) ((f₂ (code p)).index p) ∈
          forward (code p) ((trueDecode (code p) ((f₁ (code p)).index p)).1) ∧
        (trueDecode (code p) ((f₁ (code p)).index p)).1 ∈
          reverse (code p) (projectedDecode (code p) ((f₂ (code p)).index p))) ∧
      ∀ᵐ p ∂ρ, ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
        ‖(f₁ (code p)).f ((f₁ (code p)).index p) (emb x) -
          (f₂ (code p)).f ((f₂ (code p)).index p) (emb x)‖ ≤ Λ * a := by
  obtain ⟨law, active, table, hle, hbudget, hinactive, hlaw, hrefsum, hdata⟩ :=
    exists_pruned_domain_tables μ code K M signal hs f₁ f₂ ha hB hF hLfloor
      T hT palette hp hpt hresolve hvolume hnative
  let loss (q : Q) : ℝ≥0∞ :=
    ((f₁ q).n : ℝ≥0∞) * (ENNReal.ofReal (T q / F) * palette q) +
      ((f₂ q).n : ℝ≥0∞) * (ENNReal.ofReal (T q / F) * palette q)
  have hbudget' (q : Q) : codePieces μ code q univ ≤ law q univ + loss q := by
    simpa only [loss, add_assoc] using hbudget q
  obtain ⟨ν, ρ, G, hν, hρ, hρμ, hG, hmass, hrestrict, hactive, hagreement⟩ :=
    global_domain_comparison μ code hcode law hle loss hbudget' active hinactive
      H hC ha hL (by positivity) hΛ table hlaw (hrefsum.trans href)
  have hcost : (∑ q, loss q) ≤ ENNReal.ofReal (Rtotal / F) := by
    have heq := two_color_reference_cutoff (fun q => (f₁ q).n) (fun q => (f₂ q).n)
      T (fun q => (hT q).le) palette hpt hF
    change (∑ q, (((f₁ q).n : ℝ≥0∞) * (ENNReal.ofReal (T q / F) * palette q) +
      ((f₂ q).n : ℝ≥0∞) * (ENNReal.ofReal (T q / F) * palette q))) ≤ _
    rw [heq]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right href hF.le)
  choose idx₁ idx₂ hinj₁ hinj₂ hfloor₁ hfloor₂ hsame₁ hsame₂ hdecode using
    fun q : active => (hdata q).2
  let trueIdx (q : active) (i : Fin (table q).n₁) : Fin N₁ × Bool :=
    trueDecode q.val (idx₁ q i)
  let projectedIdx (q : active) (j : Fin (table q).n₂) : Fin N₂ :=
    projectedDecode q.val (idx₂ q j)
  have htrueIdx (q : active) : Function.Injective (trueIdx q) :=
    (htrue q.val).comp (hinj₁ q)
  have hprojectedIdx (q : active) : Function.Injective (projectedIdx q) :=
    (hprojected q.val).comp (hinj₂ q)
  have htablelaw (q : active) : (table q).law = ν.restrict {p | code p = q.val} :=
    (hlaw q).trans (hrestrict q.val).symm
  have hcurrent (q : active) : ∀ᵐ p ∂(table q).law,
      (trueIdx q ((table q).i₁ p)).1 = (trueDecode q.val ((f₁ q.val).index p)).1 ∧
      projectedIdx q ((table q).i₂ p) = projectedDecode q.val ((f₂ q.val).index p) := by
    rw [hlaw q]
    filter_upwards [hdecode q] with p hp
    exact ⟨congrArg (fun i => (trueDecode q.val i).1) hp.1,
      congrArg (projectedDecode q.val) hp.2⟩
  obtain ⟨forward, reverse, hforward, hreverse, hmem⟩ := global_original_partner_lists
    ν code hcode active hactive G hG ha (zero_le_one.trans hL) hΛ1 table htablelaw
    (fun q => (hdata q).1) hagreement
    (fun q i => (trueIdx q i).1) projectedIdx
    (fun q => native_branch_fiber_card_le_two (trueIdx q) (htrueIdx q))
    (fun q => injective_fiber_card_le_one (projectedIdx q) (hprojectedIdx q))
    (fun q p => (trueDecode q ((f₁ q).index p)).1)
    (fun q p => projectedDecode q ((f₂ q).index p)) hcurrent
  have hfamilyCurrent (q : active) : ∀ᵐ p ∂(table q).law,
      idx₁ q ((table q).i₁ p) = (f₁ q.val).index p ∧
      idx₂ q ((table q).i₂ p) = (f₂ q.val).index p := by
    rw [hlaw q]
    exact hdecode q
  have hfamilyAgreement := global_original_family_agreement ν code hcode active hactive G hG
    table htablelaw hagreement (fun q => (f₁ q).n) (fun q => (f₂ q).n)
    (fun q i => (f₁ q).f i) (fun q j => (f₂ q).f j) idx₁ idx₂ hsame₁ hsame₂
    (fun q => (f₁ q).index) (fun q => (f₂ q).index) hfamilyCurrent
  refine ⟨ρ, forward, reverse, hρμ, ?_, ?_, ?_, ?_, ?_⟩
  · exact hmass.trans (add_le_add (add_le_add le_rfl hcost) le_rfl)
  · simpa only [Nat.cast_ofNat] using hforward
  · simpa only [Nat.cast_one, one_mul] using hreverse
  · simpa only [hρ] using hmem
  · simpa only [hρ] using hfamilyAgreement

/-- The list-only form of the complete original comparison. -/
theorem finite_original_comparison {Ω Q : Type*} [MeasurableSpace Ω]
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → Q) (hcode : Measurable code)
    {D N₁ N₂ : ℕ} {d a B F L ε C Λ Rtotal : ℝ} (K : NNReal)
    (M : ∀ q, ComparisonMesh (codePieces μ code q))
    (signal : Ω → ℝ) (hs : Measurable signal)
    (f₁ f₂ : ∀ q, OriginalSheetFamily (codePieces μ code q) D a K (M q).base signal)
    (trueDecode : ∀ q, Fin (f₁ q).n → Fin N₁ × Bool)
    (projectedDecode : ∀ q, Fin (f₂ q).n → Fin N₂)
    (htrue : ∀ q, Function.Injective (trueDecode q))
    (hprojected : ∀ q, Function.Injective (projectedDecode q))
    (ha : 0 < a) (hB : 0 < B) (hF : 0 < F)
    (hL : 1 ≤ L) (hLfloor : 14 * B * F ≤ L)
    (T : Q → ℝ) (hT : ∀ q, 0 < T q)
    (palette : Q → ℝ≥0∞) (hp : ∀ q, palette q ≠ 0) (hpt : ∀ q, palette q ≠ ⊤)
    (hresolve : ∀ q, 2 * (K : ℝ) * (M q).diameter ≤ a / 2)
    (hvolume : ∀ q, (∑ _j : Fin (M q).n, (M q).vol) ≤ 1)
    (hnative : ∀ q (R : ℝ), a ≤ R → ∀ j x,
      codePieces μ code q {p | (M q).code p = j ∧ ⌊signal p / R⌋ = x} ≤
        (ENNReal.ofReal (B * T q * (R / a) ^ d) * palette q) * (M q).vol)
    (href : (∑ q, (((f₁ q).n : ℝ) * (T q * (palette q).toReal) +
      ((f₂ q).n : ℝ) * (T q * (palette q).toReal))) ≤ Rtotal)
    (H : ComparisonEstimate D d ε C) (hC : 0 ≤ C)
    (hΛ : C * L ^ (1 / ε) ≤ Λ) (hΛ1 : 1 ≤ Λ) :
    ∃ (ρ : Measure Ω) (forward : Q → Fin N₁ → Finset (Fin N₂))
      (reverse : Q → Fin N₂ → Finset (Fin N₁)),
      ρ ≤ μ ∧
      μ univ ≤ ρ univ + ENNReal.ofReal (Rtotal / F) +
        ENNReal.ofReal (C * (6 * B) * Λ ^ (-ε) * Rtotal) ∧
      (∀ q i, ((forward q i).card : ℝ) ≤ 2 * (L * Λ ^ d)) ∧
      (∀ q j, ((reverse q j).card : ℝ) ≤ L * Λ ^ d) ∧
      ∀ᵐ p ∂ρ,
        projectedDecode (code p) ((f₂ (code p)).index p) ∈
          forward (code p) ((trueDecode (code p) ((f₁ (code p)).index p)).1) ∧
        (trueDecode (code p) ((f₁ (code p)).index p)).1 ∈
          reverse (code p) (projectedDecode (code p) ((f₂ (code p)).index p)) := by
  obtain ⟨ρ, forward, reverse, hρ, hmass, hforward, hreverse, hmem, -⟩ :=
    finite_original_comparison_with_agreement μ code hcode K M signal hs f₁ f₂
      trueDecode projectedDecode htrue hprojected ha hB hF hL hLfloor T hT palette hp hpt
      hresolve hvolume hnative href H hC hΛ hΛ1
  exact ⟨ρ, forward, reverse, hρ, hmass, hforward, hreverse, hmem⟩

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
