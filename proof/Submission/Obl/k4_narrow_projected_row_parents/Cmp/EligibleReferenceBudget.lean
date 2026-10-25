/- Adapted from this LOT tree, obligation o200, session x0934, commit 2510f40626244312a0552650c06c57bcfd48d368,
   Submission/Obl/k4_finite_projected_horizontal_candidates/EligibleReferenceBudget.lean.
   Namespace renamed from Submission.Obl.k4_finite_projected_horizontal_candidates to Submission.Obl.k4_narrow_projected_row_parents.Cmp; earlier source attributions retained. -/
import Mathlib
import Submission.Obl.k4_narrow_projected_row_parents.Cmp.EligibleDomainFamilies

/-! The reference budget after keeping geometrically eligible original labels. -/

namespace Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison

open scoped Classical

noncomputable section

theorem eligible_original_reference_budget {Q Code : Type*} [Fintype Q]
    {N₁ N₂ : ℕ} (decode : Q → Code) (hdecode : Function.Injective decode)
    (trueMenus : Fin N₁ → Finset Code) (projectedMenus : Fin N₂ → Finset Code)
    (n₁ n₂ : Q → ℕ)
    (trueIdx : ∀ q, Fin (n₁ q) → Fin N₁ × Bool)
    (projectedIdx : ∀ q, Fin (n₂ q) → Fin N₂)
    (htrue : ∀ q, Function.Injective (trueIdx q))
    (hprojected : ∀ q, Function.Injective (projectedIdx q))
    (heligible₁ : ∀ q i, decode q ∈ trueMenus (trueIdx q i).1)
    (heligible₂ : ∀ q j, decode q ∈ projectedMenus (projectedIdx q j))
    (w : Code → ℝ) (hw : ∀ c, 0 ≤ w c) :
    (∑ q, ((n₁ q : ℝ) * w (decode q) + (n₂ q : ℝ) * w (decode q))) ≤
      2 * (∑ i, ∑ c ∈ trueMenus i, w c) + ∑ j, ∑ c ∈ projectedMenus j, w c := by
  let T (q : Q) := eligibleDomainLabels trueMenus decode q
  let P (q : Q) := eligibleDomainLabels projectedMenus decode q
  have hcount₁ (q : Q) : n₁ q ≤ 2 * (T q).card := by
    let f : Fin (n₁ q) → (T q) × Bool := fun i =>
      (⟨(trueIdx q i).1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heligible₁ q i⟩⟩,
        (trueIdx q i).2)
    have hf : Function.Injective f := by
      intro i j hij
      apply htrue q
      exact Prod.ext (congrArg (fun p : (T q) × Bool => p.1.val) hij)
        (congrArg (fun p : (T q) × Bool => p.2) hij)
    have h := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_fin, Fintype.card_prod, Fintype.card_coe, Fintype.card_bool,
      Nat.mul_comm] using h
  have hcount₂ (q : Q) : n₂ q ≤ (P q).card := by
    let f : Fin (n₂ q) → (P q) := fun j =>
      ⟨projectedIdx q j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heligible₂ q j⟩⟩
    have hf : Function.Injective f := fun i j hij => hprojected q (congrArg Subtype.val hij)
    have h := Fintype.card_le_of_injective f hf
    simpa only [Fintype.card_fin, Fintype.card_coe] using h
  calc
    _ ≤ ∑ q, (2 * (((T q).card : ℝ) * w (decode q)) +
        ((P q).card : ℝ) * w (decode q)) := by
      apply Finset.sum_le_sum
      intro q hq
      have ht : (n₁ q : ℝ) ≤ 2 * ((T q).card : ℝ) := by exact_mod_cast hcount₁ q
      have hp : (n₂ q : ℝ) ≤ ((P q).card : ℝ) := by exact_mod_cast hcount₂ q
      have h := add_le_add (mul_le_mul_of_nonneg_right ht (hw (decode q)))
        (mul_le_mul_of_nonneg_right hp (hw (decode q)))
      simpa only [mul_assoc] using h
    _ = 2 * (∑ q, ((T q).card : ℝ) * w (decode q)) +
        ∑ q, ((P q).card : ℝ) * w (decode q) := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (eligible_domain_reference_sum trueMenus decode hdecode w hw)
        (by norm_num))
      (eligible_domain_reference_sum projectedMenus decode hdecode w hw)

end

end Submission.Obl.k4_narrow_projected_row_parents.Cmp.SheetComparison
