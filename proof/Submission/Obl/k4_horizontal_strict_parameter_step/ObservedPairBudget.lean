/- Adapted from this LOT tree, obligation o245, session x0852,
branch x0852 at 284f3abd62fca77df9833a51ed09d79dce656f03, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/ObservedPairBudget.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.ObservedPairs
import Submission.Obl.k4_horizontal_strict_parameter_step.PaletteCellBudgets

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Set
open Submission.Obl.k4_row_cell_regularization

noncomputable section

namespace ObservedPairs

variable {Ω Γ J : Type*} [MeasurableSpace Ω] [DecidableEq Γ] [DecidableEq J]
  {m n : ℕ} {S : Set Ω} {A : Fin m → Set Ω} {B : Fin n → Set Ω}
  (T : ObservedPairs S A B) (group : Fin m → Γ) (block : Fin n → J)

def witnessGroups (i : Fin n) : Finset Γ :=
  ((T.witnessMenu group).filter (fun p => p.1 = i)).image Prod.snd

theorem witness_group_representative {i : Fin n} {g : Γ}
    (hg : g ∈ T.witnessGroups group i) :
    ∃ p ∈ S, p ∈ B i ∧ ∃ h : Fin m, group h = g ∧ p ∈ A h := by
  obtain ⟨key, hkey, rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨p, hp, hpB, h, hgroup, hpA⟩ :=
    T.witness_representative group ⟨key, (Finset.mem_filter.mp hkey).1⟩
  refine ⟨p, hp, ?_, h, hgroup, hpA⟩
  simpa only [(Finset.mem_filter.mp hkey).2] using hpB

/-- The true-entry domains are grouped by their original native label. -/
theorem witness_sum_by_native (weight : Γ × J → ℝ) :
    (∑ p ∈ T.witnessMenu group, weight (p.2, block p.1)) =
      ∑ i, ∑ g ∈ T.witnessGroups group i, weight (g, block i) := by
  classical
  rw [← Finset.sum_fiberwise (T.witnessMenu group) Prod.fst
    (fun p => weight (p.2, block p.1))]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [witnessGroups]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro p hp
    rw [(Finset.mem_filter.mp hp).2]
  · intro p hp p' hp' he
    exact Prod.ext ((Finset.mem_filter.mp hp).2.trans
      (Finset.mem_filter.mp hp').2.symm) he

/-- Each matching index is counted once on its own side, regardless of how
many observed pair marks share that index. -/
theorem sum_colours (weight : Γ × J → ℝ) :
    (∑ i : T.Index group block, weight (T.colour group block i)) =
      (∑ p ∈ T.sourceMenu block, weight (group p.1, p.2)) +
      ∑ i, ∑ g ∈ T.witnessGroups group i, weight (g, block i) := by
  rw [← T.witness_sum_by_native group block weight]
  change (∑ i : (T.sourceMenu block) ⊕ (T.witnessMenu group),
    weight (T.colour group block i)) = _
  rw [Fintype.sum_sum_type]
  change (∑ i : T.sourceMenu block, weight (group i.val.1, i.val.2)) +
    (∑ i : T.witnessMenu group, weight (i.val.2, block i.val.1)) = _
  exact congrArg₂ (fun a b : ℝ => a + b)
    (Finset.sum_coe_sort (T.sourceMenu block) (fun p => weight (group p.1, p.2)))
    (Finset.sum_coe_sort (T.witnessMenu group) (fun p => weight (p.2, block p.1)))

/-- Repeating an old chart over dyadic time blocks costs exactly one unit of
duration. Unobserved source domains can only decrease this budget. -/
theorem source_weight_budget [Fintype J] (weight : Γ → ℝ)
    (hweight : ∀ g, 0 ≤ weight g) {q : ℝ} (hq : 0 ≤ q)
    (hqJ : q * (Fintype.card J : ℝ) = 1) :
    (∑ p ∈ T.sourceMenu block, q * weight (group p.1)) ≤ ∑ i, weight (group i) := by
  classical
  calc
    _ ≤ ∑ p : Fin m × J, q * weight (group p.1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro p _ _
      exact mul_nonneg hq (hweight _)
    _ = ∑ i : Fin m, weight (group i) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      calc
        _ = (q * (Fintype.card J : ℝ)) * weight (group i) := by ring
        _ = _ := by rw [hqJ, one_mul]

/-- The complete native comparison threshold budget is controlled by the old
layer and original true assignment floors. Neither pair counts nor fine palette
counts occur in the estimate. -/
theorem reference_budget [Fintype J]
    (group : Fin m → Fin 3 → ℤ) (π : Measure ℝ) {χ D q a d K Q : ℝ}
    (hq : 0 ≤ q) (ha : 0 ≤ a) (hK : 0 ≤ K)
    (hqJ : q * (Fintype.card J : ℝ) = 1)
    (hold : (∑ i, D ^ 2 * a ^ d * binWeight π χ (group i 0)) ≤ Q)
    (hnative : (n : ℝ) * q ^ 4 * a ^ d ≤ K ^ 2)
    (harea : ∀ i, (∑ g ∈ T.witnessGroups group i, D ^ 2 * binWeight π χ (g 0)) ≤
      128 * K ^ 3 * q ^ 3) :
    (∑ i : T.Index group block, q * D ^ 2 * a ^ d *
      binWeight π χ ((T.colour group block i).1 0)) ≤ Q + 128 * K ^ 5 := by
  have hs := T.source_weight_budget group block
    (fun g => D ^ 2 * a ^ d * binWeight π χ (g 0))
    (fun g => mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg ha _))
      (binWeight_nonneg π χ _)) hq hqJ
  have hw := true_reference_domain_budget π (T.witnessGroups group) hq ha hK hnative harea
  rw [T.sum_colours group block
    (fun c => q * D ^ 2 * a ^ d * binWeight π χ (c.1 0))]
  apply add_le_add _ hw
  apply le_trans _ (hs.trans hold)
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro p hp
  ring

end ObservedPairs

end

end Submission.Obl.k4_horizontal_strict_parameter_step
