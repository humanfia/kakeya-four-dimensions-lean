import Submission.Obl.k4_true_forest_own_depth_preparation.Model
import Submission.Obl.k4_coarsened_outer_horizon_composition.FormatRule
import Submission.Obl.k4_coarsened_outer_horizon_composition.Pruning

namespace Submission.Obl.k4_true_forest_own_depth_preparation

open MeasureTheory Set
open Submission.Obl.k4_coarsened_outer_horizon_composition

/-- A world keeps only points that survive every applicable chart restriction. -/
def commonGood {X ι β : Type*} (γ : ι → β) (F H : ι → Set X) (w : β) : Set X :=
  {p | ∀ b, γ b = w → p ∈ F b → p ∈ H b}

/-- Each chart inherits its own restriction after the common world cutoff. -/
theorem commonGood_subset {X ι β : Type*} (γ : ι → β) (F H : ι → Set X) (b : ι) :
    F b ∩ commonGood γ F H (γ b) ⊆ H b :=
  fun _ hp => hp.2 b rfl hp.1

/-- A common world cutoff preserves all parent incidence inclusions. -/
theorem commonGood_nested {X ι β : Type*} (γ : ι → β) (F H : ι → Set X)
    {a b : ι} (hγ : γ a = γ b) (hF : F b ⊆ F a) :
    F b ∩ commonGood γ F H (γ b) ⊆ F a ∩ commonGood γ F H (γ a) := by
  intro p hp
  exact ⟨hF hp.1, hγ ▸ hp.2⟩

theorem commonGood_compl {X ι β : Type*} (γ : ι → β) (F H : ι → Set X) (w : β) :
    (commonGood γ F H w)ᶜ = ⋃ b, {p | γ b = w ∧ p ∈ F b \ H b} := by
  classical
  ext p
  simp [commonGood, not_forall]

theorem measurableSet_commonGood {X ι β : Type*} [MeasurableSpace X] [Finite ι]
    (γ : ι → β) (F H : ι → Set X) (hF : ∀ b, MeasurableSet (F b))
    (hH : ∀ b, MeasurableSet (H b)) (w : β) :
    MeasurableSet (commonGood γ F H w) := by
  classical
  have heq := congrArg (fun s : Set X => sᶜ) (commonGood_compl γ F H w)
  simp only [compl_compl] at heq
  rw [heq]
  apply MeasurableSet.compl
  exact MeasurableSet.iUnion fun b => by
    by_cases hb : γ b = w
    · simpa only [hb, true_and, Set.ofPred_mem_eq] using (hF b).diff (hH b)
    · simp only [hb, false_and, ofPred_false]
      exact MeasurableSet.empty

/-- The common cutoff is charged once to the sum of the actual deletions,
without any factor from the number of labels or worlds. -/
theorem commonGood_loss_le {X ι β : Type*} [MeasurableSpace X] [Fintype ι] [Fintype β]
    (μ : β → Measure X) (ω : β → ENNReal) (γ : ι → β) (F H : ι → Set X) :
    (∑ w, ω w * μ w (commonGood γ F H w)ᶜ) ≤
      ∑ b, ω (γ b) * μ (γ b) (F b \ H b) := by
  classical
  simp_rw [commonGood_compl]
  calc
    _ ≤ ∑ w, ω w * ∑ b, μ w {p | γ b = w ∧ p ∈ F b \ H b} := by
      exact Finset.sum_le_sum fun w _ => mul_le_mul_right (measure_iUnion_fintype_le (μ w) _) _
    _ = ∑ b, ∑ w, ω w * μ w {p | γ b = w ∧ p ∈ F b \ H b} := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      have ht (w) : ω w * μ w {p | γ b = w ∧ p ∈ F b \ H b} =
          if w = γ b then ω (γ b) * μ (γ b) (F b \ H b) else 0 := by
        by_cases hw : w = γ b
        · subst w
          rw [if_pos rfl]
          congr 2
          ext p
          simp
        · have hw' : γ b ≠ w := Ne.symm hw
          simp [hw, hw']
      simp_rw [ht]
      simp

/-- An arbitrary common-world retention rule is a Boolean rule on twice the
original number of chart predicates. -/
theorem format_commonGood {n C W D : ℕ} {h : ℝ}
    (γ : Fin C → Fin W) (F H : Fin C → Set (Fin n → ℝ))
    (hF : ∀ b, fmt n h D (F b)) (hH : ∀ b, fmt n h D (H b)) (w : Fin W) :
    fmt n ((2 * C : ℕ) * h) D (commonGood γ F H w) := by
  let V : Fin C ⊕ Fin C → Set (Fin n → ℝ) := Sum.elim F H
  have hV : ∀ b, fmt n h D (V b) := by
    intro b
    cases b with
    | inl b => exact hF b
    | inr b => exact hH b
  have hf := fmt_rule_uniform V h hV
    (fun pred => ∀ b, γ b = w → pred (.inl b) → pred (.inr b))
  simpa only [commonGood, V, Sum.elim_inl, Sum.elim_inr,
    Fintype.card_sum, Fintype.card_fin, two_mul] using hf

/-- Pulling the common cutoff through any coordinate map commutes with its
finite Boolean rule. -/
theorem preimage_commonGood {X Y ι β : Type*} (γ : ι → β) (F H : ι → Set X)
    (w : β) (φ : Y → X) :
    φ ⁻¹' commonGood γ F H w =
      commonGood γ (fun b => φ ⁻¹' F b) (fun b => φ ⁻¹' H b) w := rfl

/-- The bounded point multiplicity of a layer turns a common-world exceptional
mass into a bound for that layer's total deleted mass. -/
theorem weighted_common_cut_loss {X ι β : Type*} [MeasurableSpace X]
    [Fintype ι] [Fintype β] [DecidableEq β] (μ : β → Measure X) (ω : β → ENNReal)
    (γ : ι → β) (F : ι → Set X) (G : β → Set X)
    (hF : ∀ b, MeasurableSet (F b)) (hG : ∀ w, MeasurableSet (G w))
    (hmult : ∀ w p, (∑ b ∈ Finset.univ.filter (fun b => γ b = w),
      (F b).indicator (1 : X → ENNReal) p) ≤ 2) :
    (∑ b, ω (γ b) * μ (γ b) (F b \ G (γ b))) ≤
      2 * ∑ w, ω w * μ w (G w)ᶜ := by
  classical
  rw [← Finset.sum_fiberwise Finset.univ γ]
  calc
    _ = ∑ w, ω w * ∑ b ∈ Finset.univ.filter (fun b => γ b = w),
        μ w (F b ∩ (G w)ᶜ) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [(Finset.mem_filter.mp hb).2, Set.sdiff_eq]
    _ ≤ ∑ w, ω w * (2 * μ w (G w)ᶜ) := by
      apply Finset.sum_le_sum
      intro w _
      apply mul_le_mul_right
      exact sum_measure_inter_le_two (μ w) _ F hF (hmult w) (hG w).compl
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring

end Submission.Obl.k4_true_forest_own_depth_preparation
