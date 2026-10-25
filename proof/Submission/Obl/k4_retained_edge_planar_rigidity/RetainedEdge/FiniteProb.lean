-- Ported from this tree's o018 branch x0052 (session x0052), commit 82e5b5c26a09, file Submission/Obl/k4_framework_from_matching_clustering_conic/RetainedEdge/FiniteProb.lean;
-- only the namespace and module paths were renamed to o071's.
import Mathlib

/-!
# Finite product laws

Independent samples from finitely supported laws, written as weighted finite sums. A law on a
finite type `β` is a weight function `w` with total mass one; the `ι`-fold independent product has
weight `pw w ω = ∏ j, w (ω j)` on `ι → β`. We record its total mass, the product rule for
independent events, the resampling identity (one coordinate may be redrawn independently), and
the bound for events that constrain all coordinates but one in terms of that one.
-/

namespace Submission.Obl.k4_retained_edge_planar_rigidity

set_option linter.unusedSectionVars false

noncomputable section

open Finset

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]

/-- The weight of a sample `ω : ι → β` under the independent product of the law `w`. -/
def pw (w : β → ℝ) (ω : ι → β) : ℝ := ∏ j, w (ω j)

theorem pw_nonneg {w : β → ℝ} (hw : ∀ x, 0 ≤ w x) (ω : ι → β) : 0 ≤ pw w ω :=
  Finset.prod_nonneg fun j _ => hw (ω j)

theorem sum_pw_mul_prod (w : β → ℝ) (f : ι → β → ℝ) :
    ∑ ω : ι → β, pw w ω * ∏ j, f j (ω j) = ∏ j, ∑ x, w x * f j x := by
  rw [Fintype.prod_sum (fun j x => w x * f j x)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [pw, ← Finset.prod_mul_distrib]

theorem sum_pw (w : β → ℝ) (hw : ∑ x, w x = 1) : ∑ ω : ι → β, pw w ω = 1 := by
  have := sum_pw_mul_prod (ι := ι) w (fun _ _ => 1)
  simp only [Finset.prod_const_one, mul_one] at this
  rw [this, hw, Finset.prod_const_one]

/-- Splitting a sample at the coordinate `i`. -/
theorem sum_split_at (i : ι) (F : (ι → β) → ℝ) :
    ∑ ω : ι → β, F ω = ∑ y : β, ∑ ω' : {j // j ≠ i} → β, F ((Equiv.funSplitAt i β).symm (y, ω')) := by
  rw [← Fintype.sum_prod_type (fun p => F ((Equiv.funSplitAt i β).symm p))]
  refine Fintype.sum_equiv (Equiv.funSplitAt i β) _ _ (fun ω => ?_)
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj; simp [Equiv.funSplitAt_symm_apply]
  · simp [Equiv.funSplitAt_symm_apply, hj]

theorem pw_split (w : β → ℝ) (i : ι) (y : β) (ω' : {j // j ≠ i} → β) :
    pw w ((Equiv.funSplitAt i β).symm (y, ω')) = w y * ∏ j : {j // j ≠ i}, w (ω' j) := by
  rw [pw, Fintype.prod_eq_mul_prod_subtype_ne _ i]
  congr 1
  · simp [Equiv.funSplitAt_symm_apply]
  · refine Finset.prod_congr rfl fun j _ => ?_
    simp [Equiv.funSplitAt_symm_apply, j.2]

theorem update_split (i : ι) (x y : β) (ω' : {j // j ≠ i} → β) :
    Function.update ((Equiv.funSplitAt i β).symm (y, ω')) i x =
      (Equiv.funSplitAt i β).symm (x, ω') := by
  funext j
  by_cases hj : j = i
  · subst hj; simp [Equiv.funSplitAt_symm_apply]
  · simp [Equiv.funSplitAt_symm_apply, hj]

/-- **Resampling**: under an independent product law, redrawing one coordinate independently
does not change expectations. -/
theorem sum_resample (w : β → ℝ) (hw : ∑ x, w x = 1) (i : ι) (g : (ι → β) → ℝ) :
    ∑ ω : ι → β, pw w ω * g ω = ∑ ω : ι → β, pw w ω * ∑ x, w x * g (Function.update ω i x) := by
  rw [sum_split_at i, sum_split_at i]
  simp only [pw_split, update_split]
  have lhs : ∑ y : β, ∑ ω' : {j // j ≠ i} → β,
      w y * (∏ j : {j // j ≠ i}, w (ω' j)) * g ((Equiv.funSplitAt i β).symm (y, ω')) =
      ∑ ω' : {j // j ≠ i} → β, (∏ j : {j // j ≠ i}, w (ω' j)) *
        ∑ y : β, w y * g ((Equiv.funSplitAt i β).symm (y, ω')) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    ring
  have rhs : ∑ y : β, ∑ ω' : {j // j ≠ i} → β,
      w y * (∏ j : {j // j ≠ i}, w (ω' j)) *
        ∑ x : β, w x * g ((Equiv.funSplitAt i β).symm (x, ω')) =
      ∑ ω' : {j // j ≠ i} → β, (∏ j : {j // j ≠ i}, w (ω' j)) *
        ∑ x : β, w x * g ((Equiv.funSplitAt i β).symm (x, ω')) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, hw, one_mul]
  rw [lhs, rhs]

/-- The product rule for independent events. -/
theorem sum_pw_forall (w : β → ℝ) (S : ι → β → Prop) [∀ j, DecidablePred (S j)] :
    ∑ ω : ι → β, pw w ω * (if ∀ j, S j (ω j) then 1 else 0) =
      ∏ j, ∑ x, w x * (if S j x then 1 else 0) := by
  rw [← sum_pw_mul_prod]
  refine Finset.sum_congr rfl fun ω _ => ?_
  congr 1
  by_cases h : ∀ j, S j (ω j)
  · rw [ite_eq_left h, Finset.prod_eq_one fun j _ => ite_eq_left (h j)]
  · rw [ite_eq_right h]
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)).symm

/-- Events in which all coordinates but `i` lie in a set determined by the `i`-th coordinate. -/
theorem sum_pw_forall_ne_le (w : β → ℝ) (hw0 : ∀ x, 0 ≤ w x) (hw : ∑ x, w x = 1) (i : ι)
    (T : β → β → Prop) [∀ y, DecidablePred (T y)] (π : ℝ)
    (hT : ∀ y, ∑ x, w x * (if T y x then 1 else 0) ≤ π) :
    ∑ ω : ι → β, pw w ω * (if ∀ j, j ≠ i → T (ω i) (ω j) then 1 else 0) ≤
      π ^ (Fintype.card ι - 1) := by
  rw [sum_split_at i]
  simp only [pw_split]
  have hπ : 0 ≤ π := by
    obtain ⟨y⟩ : Nonempty β := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      simp at hw
    exact le_trans (Finset.sum_nonneg fun x _ => mul_nonneg (hw0 x) (by split_ifs <;> norm_num))
      (hT y)
  have key : ∀ y : β, ∑ ω' : {j // j ≠ i} → β, w y * (∏ j : {j // j ≠ i}, w (ω' j)) *
      (if ∀ j, j ≠ i → T ((Equiv.funSplitAt i β).symm (y, ω') i)
        ((Equiv.funSplitAt i β).symm (y, ω') j) then 1 else 0) =
      w y * ∏ _j : {j // j ≠ i}, ∑ x, w x * (if T y x then 1 else 0) := by
    intro y
    rw [← sum_pw_forall (ι := {j // j ≠ i}) w (fun _ x => T y x), Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω' _ => ?_
    rw [pw, mul_assoc]
    congr 2
    have e1 : (Equiv.funSplitAt i β).symm (y, ω') i = y := by simp [Equiv.funSplitAt_symm_apply]
    have e2 : ∀ j : ι, (hj : j ≠ i) → (Equiv.funSplitAt i β).symm (y, ω') j = ω' ⟨j, hj⟩ := by
      intro j hj; simp [Equiv.funSplitAt_symm_apply, hj]
    rw [e1]
    by_cases h : ∀ j : {j // j ≠ i}, T y (ω' j)
    · rw [ite_eq_left h, ite_eq_left]
      intro j hj
      rw [e2 j hj]
      exact h ⟨j, hj⟩
    · rw [ite_eq_right h, ite_eq_right]
      intro h'
      apply h
      intro j
      have := h' j j.2
      rwa [e2 j j.2] at this
  rw [Finset.sum_congr rfl fun y _ => key y]
  have hcard : Fintype.card {j // j ≠ i} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  calc ∑ y : β, w y * ∏ _j : {j // j ≠ i}, ∑ x, w x * (if T y x then 1 else 0)
      ≤ ∑ y : β, w y * π ^ (Fintype.card ι - 1) := by
        refine Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (hw0 y)
        rw [Finset.prod_const, Finset.card_univ, hcard]
        exact pow_le_pow_left₀ (Finset.sum_nonneg fun x _ =>
          mul_nonneg (hw0 x) (by split_ifs <;> norm_num)) (hT y) _
    _ = π ^ (Fintype.card ι - 1) := by rw [← Finset.sum_mul, hw, one_mul]

end

end Submission.Obl.k4_retained_edge_planar_rigidity
