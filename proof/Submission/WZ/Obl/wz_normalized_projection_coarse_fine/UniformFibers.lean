-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_coarse_fine.UniformFibers.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_tower_balanced_refinement.Regularize
import Submission.WZ.Obl.wz_normalized_projection_coarse_fine.ScaleSelection

namespace WangZahlLot.Obl.wz_normalized_projection_coarse_fine

open Finset
open WangZahlLot.Obl.wz_tower_balanced_refinement

/-- Balanced fibers compare each occupied cell with the total count. -/
lemma balanced_fiber_card_bounds {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (p : α → β) {R : ℝ} (hbal : Balanced S p R)
    {i : α} (hi : i ∈ S) :
    ((S.image p).card : ℝ) * (leafFiber S p i).card ≤ R * S.card ∧
      (S.card : ℝ) ≤ R * (S.image p).card * (leafFiber S p i).card := by
  classical
  have hsum : (S.card : ℝ) = ∑ y ∈ S.image p, ((S.filter (fun j => p j = y)).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image p S
  constructor
  · calc
      _ = ∑ _y ∈ S.image p, ((leafFiber S p i).card : ℝ) := by simp
      _ ≤ ∑ y ∈ S.image p, R * ((S.filter (fun j => p j = y)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro y hy
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        have hfiber : S.filter (fun a => p a = p j) = leafFiber S p j := by
          ext a
          simp [leafFiber]
        rw [hfiber]
        exact hbal i hi j hj
      _ = R * S.card := by rw [← Finset.mul_sum, ← hsum]
  · calc
      (S.card : ℝ) = ∑ y ∈ S.image p, ((S.filter (fun j => p j = y)).card : ℝ) := hsum
      _ ≤ ∑ _y ∈ S.image p, R * ((leafFiber S p i).card : ℝ) := by
        apply Finset.sum_le_sum
        intro y hy
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
        have hfiber : S.filter (fun a => p a = p j) = leafFiber S p j := by
          ext a
          simp [leafFiber]
        rw [hfiber]
        exact hbal j hj i hi
      _ = _ := by simp; ring

/-- Count growth of occupied cells becomes an upper bound inside every occupied fiber. -/
lemma balanced_fiber_scale_ratio {α β γ : Type*}
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (S : Finset α) (p : α → β) (q : α → γ) {R A : ℝ} (hR : 0 ≤ R)
    (hp : Balanced S p R) (hq : Balanced S q R)
    (hcount : ((S.image p).card : ℝ) * A ≤ (S.image q).card)
    {i j : α} (hi : i ∈ S) (hj : j ∈ S) :
    ((leafFiber S q j).card : ℝ) * A ≤ R ^ 2 * (leafFiber S p i).card := by
  have hcp : 0 < ((S.image p).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨p i, Finset.mem_image_of_mem p hi⟩
  have hbq := (balanced_fiber_card_bounds S q hq hj).1
  have hbp := (balanced_fiber_card_bounds S p hp hi).2
  apply (mul_le_mul_iff_right₀ hcp).mp
  calc
    _ = (((S.image p).card : ℝ) * A) * (leafFiber S q j).card := by ring
    _ ≤ ((S.image q).card : ℝ) * (leafFiber S q j).card :=
      mul_le_mul_of_nonneg_right hcount (Nat.cast_nonneg _)
    _ ≤ R * S.card := hbq
    _ ≤ R * (R * (S.image p).card * (leafFiber S p i).card) :=
      mul_le_mul_of_nonneg_left hbp hR
    _ = _ := by ring

/-- A balanced hierarchy with enough terminal leaves has a coarse level at which every
occupied cell satisfies the same Frostman count at each finer level. -/
theorem exists_uniform_frostman_scale {α ι : Type*} [DecidableEq α] [Fintype ι]
    {β : ι → Type*} [∀ j, DecidableEq (β j)]
    (S : Finset α) (hS : S.Nonempty) (p : ∀ j, α → β j) (t : ι → ℝ) (i₀ : ι)
    {B L s d e ε R : ℝ} (hB : 1 < B) (hL : t i₀ < L)
    (hs : 0 ≤ s) (hd : 0 ≤ d) (he : 0 ≤ e) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hR : 0 ≤ R) (ht : ∀ i, t i ≤ L) (hbal : ∀ j, Balanced S (p j) R)
    (hpacking : ∀ i, ((S.image (p i₀)).card : ℝ) *
      B ^ (s * (L - t i₀) - e - d * (L - t i)) ≤ (S.image (p i)).card) :
    ∃ j, t j ≤ L - ε * (L - t i₀) ∧
      ∀ k, ∀ i ∈ S, ∀ i' ∈ S,
        ((leafFiber S (p k) i').card : ℝ) *
          B ^ (s * (t k - t j) -
            (d * ε + e / (L - t i₀)) * (L - t j)) ≤
          R ^ 2 * (leafFiber S (p j) i).card := by
  have hN (j : ι) : 0 < ((S.image (p j)).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (hS.image (p j))
  obtain ⟨j, hj, hjk⟩ := exists_frostman_count_scale t
    (fun j => ((S.image (p j)).card : ℝ)) i₀ hB hN hL hs hd he hε hε1 ht hpacking
  exact ⟨j, hj, fun k i hi i' hi' =>
    balanced_fiber_scale_ratio S (p j) (p k) hR (hbal j) (hbal k) (hjk k) hi hi'⟩

end WangZahlLot.Obl.wz_normalized_projection_coarse_fine
