-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse.TSCount.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib

/-!
# Counting fibres of a two-level assignment

Fine elements are assigned to coarse elements (`fc`), and coarse elements to
covers (`g`). Balance of the fine fibres at both levels transfers to balance of
the coarse fibres, and fine counts bound coarse counts.
-/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse

open Finset

/-- Fine fibres over a set of coarse elements add up. -/
theorem card_filter_comp_eq_sum {n k : ℕ} (fc : Fin n → Fin k) (P : Fin k → Prop)
    [DecidablePred P] :
    ((univ.filter (fun i => P (fc i))).card : ℝ) =
      ∑ j ∈ univ.filter P, ((univ.filter (fun i => fc i = j)).card : ℝ) := by
  classical
  rw [← Nat.cast_sum]
  congr 1
  rw [card_eq_sum_card_fiberwise (f := fc) (t := univ.filter P)]
  · apply sum_congr rfl
    intro j hj
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨by rw [h]; exact (mem_filter.mp hj).2, h⟩
  · intro i hi
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hi).2⟩

/-- Lower and upper bounds of all fine fibres by one of them. -/
theorem fibre_bounds {n k : ℕ} (fc : Fin n → Fin k) {c : ℝ}
    (hA : ∀ j j', ((univ.filter (fun i => fc i = j)).card : ℝ) ≤
      c * (univ.filter (fun i => fc i = j')).card) (j0 j : Fin k) :
    ((univ.filter (fun i => fc i = j0)).card : ℝ) ≤
        c * (univ.filter (fun i => fc i = j)).card ∧
      ((univ.filter (fun i => fc i = j)).card : ℝ) ≤
        c * (univ.filter (fun i => fc i = j0)).card :=
  ⟨hA j0 j, hA j j0⟩

/-- Balance of coarse fibres from balance of fine fibres at two levels. -/
theorem coarse_fibre_balance {n k k'' : ℕ} (fc : Fin n → Fin k) (g : Fin k → Fin k'')
    {c : ℝ} (hc : 0 < c)
    (hA : ∀ j j', ((univ.filter (fun i => fc i = j)).card : ℝ) ≤
      c * (univ.filter (fun i => fc i = j')).card)
    (hB : ∀ m m', ((univ.filter (fun i => g (fc i) = m)).card : ℝ) ≤
      c * (univ.filter (fun i => g (fc i) = m')).card)
    (hsurj : ∀ j, ∃ i, fc i = j) (j1 j2 : Fin k) :
    ((univ.filter (fun j => g j = g j1)).card : ℝ) ≤
      c ^ 3 * (univ.filter (fun j => g j = g j2)).card := by
  classical
  set A0 : ℝ := ((univ.filter (fun i => fc i = j1)).card : ℝ)
  have hA0 : 0 < A0 := by
    obtain ⟨i, hi⟩ := hsurj j1
    have hne : (univ.filter (fun i => fc i = j1)).Nonempty :=
      ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
    have := card_pos.mpr hne
    dsimp [A0]
    exact_mod_cast this
  have hsum1 := card_filter_comp_eq_sum fc (fun j => g j = g j1)
  have hsum2 := card_filter_comp_eq_sum fc (fun j => g j = g j2)
  -- lower bound for the first sum, upper bound for the second
  have hlow : ((univ.filter (fun j => g j = g j1)).card : ℝ) * (A0 / c) ≤
      ((univ.filter (fun i => g (fc i) = g j1)).card : ℝ) := by
    rw [hsum1, card_eq_sum_ones, Nat.cast_sum, sum_mul]
    apply sum_le_sum
    intro j _
    rw [Nat.cast_one, one_mul, div_le_iff₀ hc]
    linarith [hA j1 j, mul_comm c ((univ.filter (fun i => fc i = j)).card : ℝ)]
  have hup : ((univ.filter (fun i => g (fc i) = g j2)).card : ℝ) ≤
      ((univ.filter (fun j => g j = g j2)).card : ℝ) * (c * A0) := by
    rw [hsum2, card_eq_sum_ones, Nat.cast_sum, sum_mul]
    apply sum_le_sum
    intro j _
    rw [Nat.cast_one, one_mul]
    exact hA j j1
  have hB' := hB (g j1) (g j2)
  have key : ((univ.filter (fun j => g j = g j1)).card : ℝ) * (A0 / c) ≤
      c * (((univ.filter (fun j => g j = g j2)).card : ℝ) * (c * A0)) := by
    calc _ ≤ _ := hlow
      _ ≤ _ := hB'
      _ ≤ _ := mul_le_mul_of_nonneg_left hup hc.le
  have hpos : 0 < A0 / c := div_pos hA0 hc
  have : ((univ.filter (fun j => g j = g j1)).card : ℝ) ≤
      c * (((univ.filter (fun j => g j = g j2)).card : ℝ) * (c * A0)) / (A0 / c) :=
    (le_div_iff₀ hpos).mpr key
  calc _ ≤ c * (((univ.filter (fun j => g j = g j2)).card : ℝ) * (c * A0)) / (A0 / c) := this
    _ = c ^ 3 * (univ.filter (fun j => g j = g j2)).card := by
      field_simp

/-- Coarse counts with a property are bounded by fine counts with an implied property. -/
theorem coarse_count_le {n k : ℕ} (fc : Fin n → Fin k) {c : ℝ} (hc : 0 < c)
    (hA : ∀ j j', ((univ.filter (fun i => fc i = j)).card : ℝ) ≤
      c * (univ.filter (fun i => fc i = j')).card)
    (j0 : Fin k) (P : Fin k → Prop) [DecidablePred P] (Q : Fin n → Prop) [DecidablePred Q]
    (hPQ : ∀ i, P (fc i) → Q i) :
    ((univ.filter P).card : ℝ) * ((univ.filter (fun i => fc i = j0)).card / c) ≤
      ((univ.filter Q).card : ℝ) := by
  classical
  have hsum := card_filter_comp_eq_sum fc P
  calc ((univ.filter P).card : ℝ) * ((univ.filter (fun i => fc i = j0)).card / c)
      ≤ ∑ j ∈ univ.filter P, ((univ.filter (fun i => fc i = j)).card : ℝ) := by
        rw [card_eq_sum_ones, Nat.cast_sum, sum_mul]
        apply sum_le_sum
        intro j _
        rw [Nat.cast_one, one_mul, div_le_iff₀ hc]
        linarith [hA j0 j, mul_comm c ((univ.filter (fun i => fc i = j)).card : ℝ)]
    _ = ((univ.filter (fun i => P (fc i))).card : ℝ) := hsum.symm
    _ ≤ ((univ.filter Q).card : ℝ) := by
        exact_mod_cast card_le_card (fun i hi => by
          simp only [mem_filter, mem_univ, true_and] at hi ⊢
          exact hPQ i hi)

/-- Fine counts over a set of coarse elements are bounded by the coarse count. -/
theorem fine_count_le {n k : ℕ} (fc : Fin n → Fin k) {c : ℝ}
    (hA : ∀ j j', ((univ.filter (fun i => fc i = j)).card : ℝ) ≤
      c * (univ.filter (fun i => fc i = j')).card)
    (j0 : Fin k) (P : Fin k → Prop) [DecidablePred P] :
    ((univ.filter (fun i => P (fc i))).card : ℝ) ≤
      ((univ.filter P).card : ℝ) * (c * (univ.filter (fun i => fc i = j0)).card) := by
  classical
  rw [card_filter_comp_eq_sum fc P, card_eq_sum_ones, Nat.cast_sum, sum_mul]
  apply sum_le_sum
  intro j _
  rw [Nat.cast_one, one_mul]
  exact hA j j0

end WangZahlLot.Obl.wz_multiscale_c2_extraction.Coarse
