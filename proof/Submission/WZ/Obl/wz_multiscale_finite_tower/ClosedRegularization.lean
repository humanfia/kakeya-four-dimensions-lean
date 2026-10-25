-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_finite_tower.ClosedRegularization.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_multiscale_finite_tower.BalancedPruning

namespace WangZahlLot.Obl.wz_multiscale_finite_tower

open scoped ENNReal
open WangZahlLot.Obl.wz_tower_balanced_refinement

/-- Regularizing a prefix of nested partitions can preserve every occupied fibre
of a finer partition in full. This keeps newly inserted cover groups intact. -/
theorem regularize_nested_closed {α γ : Type*} [DecidableEq α] {β : ℕ → Type*}
    (p : ∀ j, α → β j) (c : α → γ) (J q n : ℕ) (hq : 0 < q) (R : ℝ)
    (color : ℕ → Fin q)
    (hcolor : ∀ a b : ℕ, 0 < a → a ≤ n → 0 < b → b ≤ n →
      color a = color b → (a : ℝ) ≤ R * b)
    (hnest : ∀ j k, j ≤ k → k < J → ∀ i i', p k i = p k i' → p j i = p j i')
    (hcoarse : ∀ j, j < J → ∀ i i', c i = c i' → p j i = p j i')
    (U : Finset α) (hU : U.card ≤ n) (w : α → ℝ≥0∞) :
    ∃ S : Finset α, S ⊆ U ∧
      (∑ i ∈ U, w i) ≤ (q : ℝ≥0∞) ^ J * ∑ i ∈ S, w i ∧
      (∀ j, j < J → Balanced S (p j) R) ∧
      ∀ i ∈ U, ∀ i' ∈ U, c i = c i' → (i ∈ S ↔ i' ∈ S) := by
  classical
  induction J generalizing β with
  | zero =>
    refine ⟨U, Finset.Subset.refl U, by simp, (fun j hj => by omega), ?_⟩
    intro i hi i' hi' he
    exact iff_of_true hi hi'
  | succ J ih =>
    obtain ⟨V, hVU, hmass, hbal, hclosed⟩ := ih (fun j => p (j + 1))
      (fun j k hjk hk => hnest (j + 1) (k + 1) (by omega) (by omega))
      (fun j hj => hcoarse (j + 1) (by omega))
    let label : α → Fin q := fun i => color (leafFiber V (p 0) i).card
    obtain ⟨b, hb⟩ := weighted_color hq V label w
    let S := V.filter (fun i => label i = b)
    have hSV : S ⊆ V := Finset.filter_subset _ _
    have hlabel (j : ℕ) (hj : j < J + 1) (a b : α)
        (he : p j a = p j b) : label a = label b := by
      dsimp only [label]
      rw [leafFiber_eq_of_eq V (p 0) (hnest 0 j (Nat.zero_le j) hj a b he)]
    refine ⟨S, hSV.trans hVU, ?_, ?_, ?_⟩
    · exact hmass.trans (by
        simpa only [pow_succ, mul_assoc] using mul_le_mul' (le_refl ((q : ℝ≥0∞) ^ J)) hb)
    · intro j hj i hi k hk
      have hi' : i ∈ V.filter (fun a => label a = b) := hi
      have hk' : k ∈ V.filter (fun a => label a = b) := hk
      dsimp only [S]
      rw [leafFiber_filter V (p j) label b (hlabel j hj) hi',
        leafFiber_filter V (p j) label b (hlabel j hj) hk']
      cases j with
      | zero =>
        apply hcolor _ _ (leafFiber_pos _ (hSV hi))
          ((leafFiber_card_le _ _ _).trans ((Finset.card_le_card hVU).trans hU))
          (leafFiber_pos _ (hSV hk))
          ((leafFiber_card_le _ _ _).trans ((Finset.card_le_card hVU).trans hU))
        exact (Finset.mem_filter.mp hi').2.trans (Finset.mem_filter.mp hk').2.symm
      | succ j => exact hbal j (by omega) i (hSV hi) k (hSV hk)
    · intro i hi k hk he
      have hlabel' : label i = label k :=
        hlabel 0 (by omega) i k (hcoarse 0 (by omega) i k he)
      change (i ∈ V.filter (fun a => label a = b)) ↔ (k ∈ V.filter (fun a => label a = b))
      simp only [Finset.mem_filter, hclosed i hi k hk he, hlabel']

end WangZahlLot.Obl.wz_multiscale_finite_tower
