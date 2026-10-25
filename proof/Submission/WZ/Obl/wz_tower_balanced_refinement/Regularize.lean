-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_tower_balanced_refinement.Regularize.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_tower_balanced_refinement

open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Weighted pigeonholing, written without division so it also covers infinite weights. -/
theorem weighted_color {α : Type*} [DecidableEq α] {q : ℕ} (hq : 0 < q)
    (S : Finset α) (c : α → Fin q) (w : α → ℝ≥0∞) :
    ∃ b : Fin q, (∑ i ∈ S, w i) ≤ q * ∑ i ∈ S.filter (fun i => c i = b), w i := by
  classical
  haveI : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨b, hb, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun b : Fin q => ∑ i ∈ S.filter (fun i => c i = b), w i) Finset.univ_nonempty
  refine ⟨b, ?_⟩
  calc
    (∑ i ∈ S, w i) = ∑ b : Fin q, ∑ i ∈ S.filter (fun i => c i = b), w i := by
      symm
      exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
    _ ≤ ∑ _b : Fin q, ∑ i ∈ S.filter (fun i => c i = b), w i :=
      Finset.sum_le_sum fun a ha => hmax a ha
    _ = q * ∑ i ∈ S.filter (fun i => c i = b), w i := by simp

/-- The fiber containing a chosen leaf. -/
def leafFiber {α β : Type*} [DecidableEq α] (S : Finset α) (p : α → β) (i : α) : Finset α :=
  S.filter fun a => p a = p i

/-- Every two occupied fibers have comparable cardinalities. -/
def Balanced {α β : Type*} [DecidableEq α] (S : Finset α) (p : α → β) (R : ℝ) : Prop :=
  ∀ i ∈ S, ∀ i' ∈ S,
    ((leafFiber S p i).card : ℝ) ≤ R * (leafFiber S p i').card

lemma leafFiber_eq_of_eq {α β : Type*} [DecidableEq α]
    (S : Finset α) (p : α → β) {i i' : α} (h : p i = p i') :
    leafFiber S p i = leafFiber S p i' := by
  simp only [leafFiber, h]

lemma leafFiber_pos {α β : Type*} [DecidableEq α]
    {S : Finset α} (p : α → β) {i : α} (hi : i ∈ S) : 0 < (leafFiber S p i).card := by
  apply Finset.card_pos.mpr
  exact ⟨i, by simp [leafFiber, hi]⟩

lemma leafFiber_card_le {α β : Type*} [DecidableEq α]
    (S : Finset α) (p : α → β) (i : α) : (leafFiber S p i).card ≤ S.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

/-- A selection by a coarser fiber keeps each occupied finer fiber intact. -/
lemma leafFiber_filter {α β γ : Type*} [DecidableEq α] [DecidableEq γ]
    (S : Finset α) (p : α → β) (c : α → γ) (b : γ)
    (hc : ∀ a a', p a = p a' → c a = c a')
    {i : α} (hi : i ∈ S.filter (fun a => c a = b)) :
    leafFiber (S.filter (fun a => c a = b)) p i = leafFiber S p i := by
  classical
  have hci := (Finset.mem_filter.mp hi).2
  ext a
  simp only [leafFiber, Finset.mem_filter]
  constructor
  · rintro ⟨⟨ha, _⟩, hp⟩
    exact ⟨ha, hp⟩
  · rintro ⟨ha, hp⟩
    exact ⟨⟨ha, (hc a i hp).trans hci⟩, hp⟩

/-- Regularize all nested partitions with at most one weighted pigeonhole loss per level.
The coloring of positive integers packages any convenient multiplicative size bins. -/
theorem regularize_nested {α : Type*} [DecidableEq α] {β : ℕ → Type*}
    (p : ∀ j, α → β j) (J q n : ℕ) (hq : 0 < q) (R : ℝ)
    (color : ℕ → Fin q)
    (hcolor : ∀ a b : ℕ, 0 < a → a ≤ n → 0 < b → b ≤ n →
      color a = color b → (a : ℝ) ≤ R * b)
    (hnest : ∀ j k, j ≤ k → k < J → ∀ i i', p k i = p k i' → p j i = p j i')
    (U : Finset α) (hU : U.card ≤ n) (w : α → ℝ≥0∞) :
    ∃ S : Finset α, S ⊆ U ∧
      (∑ i ∈ U, w i) ≤ (q : ℝ≥0∞) ^ J * ∑ i ∈ S, w i ∧
      ∀ j, j < J → Balanced S (p j) R := by
  classical
  induction J generalizing β with
  | zero =>
      refine ⟨U, Finset.Subset.refl _, ?_, ?_⟩
      · simp
      · intro j hj
        omega
  | succ J ih =>
      obtain ⟨S, hSU, hmass, hbal⟩ := ih (fun j => p (j + 1))
        (by intro j k hjk hk; exact hnest (j + 1) (k + 1) (by omega) (by omega))
      let c : α → Fin q := fun i => color (leafFiber S (p 0) i).card
      obtain ⟨b, hb⟩ := weighted_color hq S c w
      let S' := S.filter fun i => c i = b
      have hS'S : S' ⊆ S := Finset.filter_subset _ _
      have hc : ∀ k, k < J + 1 → ∀ i i', p k i = p k i' → c i = c i' := by
        intro k hk i i' hii'
        dsimp [c]
        rw [leafFiber_eq_of_eq S (p 0) (hnest 0 k (Nat.zero_le k) hk i i' hii')]
      refine ⟨S', hS'S.trans hSU, ?_, ?_⟩
      · calc
          (∑ i ∈ U, w i) ≤ (q : ℝ≥0∞) ^ J * ∑ i ∈ S, w i := hmass
          _ ≤ (q : ℝ≥0∞) ^ J * (q * ∑ i ∈ S', w i) := mul_le_mul' le_rfl hb
          _ = (q : ℝ≥0∞) ^ (J + 1) * ∑ i ∈ S', w i := by rw [pow_succ, mul_assoc]
      · intro j hj i hi i' hi'
        dsimp only [S'] at hi hi' ⊢
        rw [leafFiber_filter S (p j) c b (hc j hj) hi,
          leafFiber_filter S (p j) c b (hc j hj) hi']
        cases j with
        | zero =>
            apply hcolor _ _ (leafFiber_pos (p 0) (hS'S hi))
              ((leafFiber_card_le _ _ _).trans ((Finset.card_le_card hSU).trans hU))
              (leafFiber_pos (p 0) (hS'S hi'))
              ((leafFiber_card_le _ _ _).trans ((Finset.card_le_card hSU).trans hU))
            exact (Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hi').2.symm
        | succ j => exact hbal j (by omega) i (hS'S hi) i' (hS'S hi')


/-- A polynomial cardinality bound gives a bounded number of multiplicative size classes. -/
theorem exists_size_color (n q : ℕ) (R : ℝ) (hq : 0 < q) (hR : 1 < R)
    (hn : (n : ℝ) < R ^ q) :
    ∃ color : ℕ → Fin q, ∀ a b : ℕ, 0 < a → a ≤ n → 0 < b → b ≤ n →
      color a = color b → (a : ℝ) ≤ R * b := by
  classical
  have hex (a : ℕ) := exists_nat_pow_near (le_max_right (a : ℝ) 1) hR
  let k : ℕ → ℕ := fun a => Nat.find (hex a)
  have hspec (a : ℕ) (ha : 0 < a) : R ^ k a ≤ (a : ℝ) ∧ (a : ℝ) < R ^ (k a + 1) := by
    have h1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
    simpa only [k, max_eq_left h1] using Nat.find_spec (hex a)
  have hk (a : ℕ) (ha : 0 < a) (han : a ≤ n) : k a < q := by
    apply (pow_lt_pow_iff_right₀ hR).mp
    exact (hspec a ha).1.trans_lt ((Nat.cast_le.mpr han).trans_lt hn)
  let color : ℕ → Fin q := fun a =>
    if h : 0 < a ∧ a ≤ n then ⟨k a, hk a h.1 h.2⟩ else ⟨0, hq⟩
  refine ⟨color, ?_⟩
  intro a b ha han hb hbn heq
  have heq' : k a = k b := by
    have h := congrArg Fin.val heq
    simpa [color, ha, han, hb, hbn] using h
  calc
    (a : ℝ) ≤ R ^ (k a + 1) := (hspec a ha).2.le
    _ = R * R ^ k b := by rw [heq', pow_succ, mul_comm]
    _ ≤ R * b := mul_le_mul_of_nonneg_left (hspec b hb).1 (by linarith)

end

end WangZahlLot.Obl.wz_tower_balanced_refinement
