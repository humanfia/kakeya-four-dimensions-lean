-- Adapted from this LOT tree, obligation o254, branch x0898, commit f25a0cc9, file Submission/Obl/k4_general_parent_wide_layer_candidates/Native/GlobalPartnerLists.lean. Namespace and internal imports renamed to Submission.Obl.k4_general_wide_layer_offset_comparison.
/- Adapted from this LOT tree, obligation o200, session x0934, commit 3ef9d3b45123d3245f500a2dc2bd85270a8fff3d,
   Submission/Obl/k4_finite_projected_horizontal_candidates/GlobalPartnerLists.lean. Original source attributions are retained below. -/
import Mathlib
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.DecodedPartnerLists
import Submission.Obl.k4_general_wide_layer_offset_comparison.Native.ComparisonTables

/-! Actual original-label partner lists on the one retained source law. -/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison

open MeasureTheory Set
open scoped Classical

noncomputable section

theorem global_original_partner_lists {Ω Q : Type*} [MeasurableSpace Ω]
    [Fintype Q] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (ν : Measure Ω) (code : Ω → Q) (hcode : Measurable code)
    (active : Finset Q) (hactive : ∀ᵐ p ∂ν, code p ∈ active)
    (G : Set Ω) (hG : MeasurableSet G)
    {D N₁ N₂ J₁ J₂ : ℕ} {d a L CT Λ : ℝ}
    (ha : 0 < a) (hL : 0 ≤ L) (hΛ : 1 ≤ Λ)
    (table : (q : active) → ComparisonTable Ω D d a L CT)
    (hlaw : ∀ q, (table q).law = ν.restrict {p | code p = q.val})
    (hquarter : ∀ q, QuarterListBound a L d (table q).f₁ (table q).f₂)
    (hagreement : ∀ (q : active) p, p ∈ G → code p = q.val →
      ∀ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ≤ 1 / 4 →
        ‖(table q).f₁ ((table q).i₁ p) (emb x) -
          (table q).f₂ ((table q).i₂ p) (emb x)‖ ≤ Λ * a)
    (idx₁ : (q : active) → Fin (table q).n₁ → Fin N₁)
    (idx₂ : (q : active) → Fin (table q).n₂ → Fin N₂)
    (hfiber₁ : ∀ q i, (Finset.univ.filter fun j => idx₁ q j = i).card ≤ J₁)
    (hfiber₂ : ∀ q i, (Finset.univ.filter fun j => idx₂ q j = i).card ≤ J₂)
    (old₁ : Q → Ω → Fin N₁) (old₂ : Q → Ω → Fin N₂)
    (hdecode : ∀ q, ∀ᵐ p ∂(table q).law,
      idx₁ q ((table q).i₁ p) = old₁ q.val p ∧ idx₂ q ((table q).i₂ p) = old₂ q.val p) :
    ∃ (forward : Q → Fin N₁ → Finset (Fin N₂))
      (reverse : Q → Fin N₂ → Finset (Fin N₁)),
      (∀ q i, ((forward q i).card : ℝ) ≤ (J₁ : ℝ) * (L * Λ ^ d)) ∧
      (∀ q j, ((reverse q j).card : ℝ) ≤ (J₂ : ℝ) * (L * Λ ^ d)) ∧
      ∀ᵐ p ∂ν.restrict G,
        old₂ (code p) p ∈ forward (code p) (old₁ (code p) p) ∧
        old₁ (code p) p ∈ reverse (code p) (old₂ (code p) p) := by
  have hlocal (q : active) := (hquarter q).decoded_lists ha hL hΛ
    (table q).i₁ (table q).i₂ (G ∩ {p | code p = q.val})
    (fun p hp => hagreement q p hp.1 hp.2) (idx₁ q) (idx₂ q) (hfiber₁ q) (hfiber₂ q)
  choose forwardLocal reverseLocal hforward hreverse hmem using hlocal
  let forward (q : Q) : Fin N₁ → Finset (Fin N₂) :=
    if hq : q ∈ active then forwardLocal ⟨q, hq⟩ else fun _ => ∅
  let reverse (q : Q) : Fin N₂ → Finset (Fin N₁) :=
    if hq : q ∈ active then reverseLocal ⟨q, hq⟩ else fun _ => ∅
  have hB : 0 ≤ L * Λ ^ d := mul_nonneg hL (Real.rpow_nonneg (by linarith only [hΛ]) _)
  have hdecode' (q : active) : ∀ᵐ p ∂ν, code p = q.val →
      idx₁ q ((table q).i₁ p) = old₁ q.val p ∧ idx₂ q ((table q).i₂ p) = old₂ q.val p := by
    have hqmeas : MeasurableSet {p | code p = q.val} := hcode (measurableSet_singleton q.val)
    apply (ae_restrict_iff' hqmeas).mp
    rw [← hlaw q]
    exact hdecode q
  have hall : ∀ᵐ p ∂ν, ∀ q : active, code p = q.val →
      idx₁ q ((table q).i₁ p) = old₁ q.val p ∧ idx₂ q ((table q).i₂ p) = old₂ q.val p :=
    ae_all_iff.mpr hdecode'
  refine ⟨forward, reverse, ?_, ?_, ?_⟩
  · intro q i
    by_cases hq : q ∈ active
    · simpa only [forward, dif_pos hq] using hforward ⟨q, hq⟩ i
    · simpa only [forward, dif_neg hq, Finset.card_empty, Nat.cast_zero] using
        mul_nonneg (Nat.cast_nonneg J₁) hB
  · intro q j
    by_cases hq : q ∈ active
    · simpa only [reverse, dif_pos hq] using hreverse ⟨q, hq⟩ j
    · simpa only [reverse, dif_neg hq, Finset.card_empty, Nat.cast_zero] using
        mul_nonneg (Nat.cast_nonneg J₂) hB
  · filter_upwards [ae_restrict_mem hG, ae_restrict_of_ae hactive, ae_restrict_of_ae hall]
      with p hp hpa hpd
    let q : active := ⟨code p, hpa⟩
    have hm := hmem q p ⟨hp, rfl⟩
    obtain ⟨hd₁, hd₂⟩ := hpd q rfl
    rw [hd₁, hd₂] at hm
    simpa only [forward, reverse, dif_pos hpa] using hm

end

end Submission.Obl.k4_general_wide_layer_offset_comparison.Native.SheetComparison
