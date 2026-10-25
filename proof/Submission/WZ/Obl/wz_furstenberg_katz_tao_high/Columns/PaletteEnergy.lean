-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns.PaletteEnergy.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
-- Adapted from workspace o222/x0720 Columns/PaletteEnergy.lean (ccadf1f, 8169359).
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.CellEnergy
import Submission.WZ.Obl.wz_furstenberg_katz_tao_high.Columns.CoarsePairs

namespace WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns

open WangZahlLot.Obl.wz_furstenberg_katz_tao_half
open scoped BigOperators Classical

/-- Select the last ball of a finite palette containing a given distance.
The terminal ball includes the diagonal, so no separation is required. -/
theorem exists_distance_palette_shell (ρ : ℕ → ℝ) {h a : ℕ} (hha : h ≤ a)
    {d : ℝ} (hd : d ≤ ρ h) :
    ∃ i ∈ Finset.Icc h a, d ≤ ρ i ∧ (i = a ∨ ρ (i + 1) < d) := by
  let S := (Finset.Icc h a).filter fun i => d ≤ ρ i
  have hS : S.Nonempty := ⟨h, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hha⟩, hd⟩⟩
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image S id hS
  obtain ⟨hiI, hdρ⟩ := Finset.mem_filter.mp hi
  refine ⟨i, hiI, hdρ, ?_⟩
  by_cases hia : i = a
  · exact Or.inl hia
  · right
    by_contra hno
    have hiS : i + 1 ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr (by have := Finset.mem_Icc.mp hiI; omega), le_of_not_gt hno⟩
    have := hmax (i + 1) hiS
    change i + 1 ≤ i at this
    omega

/-- Sum a pair weight using bounds on a finite palette of balls and shells. -/
theorem row_weight_le_palette {X : Type*} [PseudoMetricSpace X]
    (P Q : Finset X) (hQP : Q ⊆ P) (p : X) (ρ M k : ℕ → ℝ) (w : X → ℝ)
    {h a : ℕ} (hha : h ≤ a)
    (hQ : ∀ q ∈ Q, dist p q ≤ ρ h)
    (hk : ∀ i ∈ Finset.Icc h a, 0 ≤ k i)
    (hM : ∀ i ∈ Finset.Icc h a,
      ((P.filter fun q => dist p q ≤ ρ i).card : ℝ) ≤ M i)
    (hw : ∀ q ∈ Q, ∀ i ∈ Finset.Icc h a, dist p q ≤ ρ i →
      (i = a ∨ ρ (i + 1) < dist p q) → w q ≤ k i) :
    ∑ q ∈ Q, w q ≤ ∑ i ∈ Finset.Icc h a, M i * k i := by
  have hpoint : ∀ q ∈ Q,
      w q ≤ ∑ i ∈ Finset.Icc h a, if dist p q ≤ ρ i then k i else 0 := by
    intro q hq
    obtain ⟨i, hi, hdi, hishell⟩ := exists_distance_palette_shell ρ hha (hQ q hq)
    calc
      w q ≤ k i := hw q hq i hi hdi hishell
      _ = (if dist p q ≤ ρ i then k i else 0) := by simp only [hdi, ite_true]
      _ ≤ _ := by
        apply Finset.single_le_sum (f := fun i => if dist p q ≤ ρ i then k i else 0) _ hi
        intro j hj
        split_ifs
        · exact hk j hj
        · exact le_rfl
  calc
    ∑ q ∈ Q, w q ≤ ∑ q ∈ Q, ∑ i ∈ Finset.Icc h a,
        if dist p q ≤ ρ i then k i else 0 := Finset.sum_le_sum hpoint
    _ = ∑ i ∈ Finset.Icc h a, ((Q.filter fun q => dist p q ≤ ρ i).card : ℝ) * k i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right _ (hk i hi)
      exact (Nat.cast_le.mpr (Finset.card_le_card (Finset.monotone_filter_left _ hQP))).trans (hM i hi)

/-- Sum cellwise pair weights by starting at each pin once. -/
theorem cell_pair_sum_eq {X ι : Type*} [DecidableEq ι]
    (P : Finset X) (cell : X → ι) (w : X → X → ℝ) :
    (∑ c ∈ P.image cell, ∑ p ∈ P.filter (fun p => cell p = c),
      ∑ q ∈ P.filter (fun q => cell q = c), w p q) =
      ∑ p ∈ P, ∑ q ∈ P.filter (fun q => cell q = cell p), w p q := by
  calc
    _ = ∑ c ∈ P.image cell, ∑ p ∈ P.filter (fun p => cell p = c),
        ∑ q ∈ P.filter (fun q => cell q = cell p), w p q := by
      apply Finset.sum_congr rfl
      intro c hc
      apply Finset.sum_congr rfl
      intro p hp
      rw [(Finset.mem_filter.mp hp).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun p hp => Finset.mem_image_of_mem cell hp) _

/-- Finite-palette upper bound for the second moment of class/cell degrees.
This accepts any actual common-class shell bounds. -/
theorem cell_energy_le_palette {ι : Type*} [DecidableEq ι]
    (D J : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (P : Finset E2) (cell : E2 → ι) (ρ M k : ℕ → ℝ)
    {h a : ℕ} (hha : h ≤ a)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, cell p = cell q → dist p q ≤ ρ h)
    (hk : ∀ i ∈ Finset.Icc h a, 0 ≤ k i)
    (hM : ∀ p ∈ P, ∀ i ∈ Finset.Icc h a,
      ((P.filter fun q => dist p q ≤ ρ i).card : ℝ) ≤ M i)
    (hpair : ∀ p ∈ P, ∀ q ∈ P, ∀ i ∈ Finset.Icc h a, dist p q ≤ ρ i →
      (i = a ∨ ρ (i + 1) < dist p q) →
      ((J.filter fun j => p ∈ pinsOf D cls j ∧ q ∈ pinsOf D cls j).card : ℝ) ≤ k i) :
    (∑ j ∈ J, ∑ c ∈ P.image cell, ((cellPins D cls P cell j c).card : ℝ) ^ 2) ≤
      P.card * ∑ i ∈ Finset.Icc h a, M i * k i := by
  rw [Finset.sum_comm]
  simp_rw [cell_energy_eq]
  rw [cell_pair_sum_eq]
  calc
    _ ≤ ∑ _p ∈ P, ∑ i ∈ Finset.Icc h a, M i * k i := by
      apply Finset.sum_le_sum
      intro p hp
      apply row_weight_le_palette P _ (Finset.filter_subset _ _) p ρ M k _ hha
      · intro q hq
        exact hdiam p hp q (Finset.mem_filter.mp hq).1 (Finset.mem_filter.mp hq).2.symm
      · exact hk
      · exact hM p hp
      · intro q hq i hi hd hs
        exact hpair p hp q (Finset.mem_filter.mp hq).1 i hi hd hs
    _ = _ := by simp

/-- The complete finite cell-energy inequality after bounding the number of
classes and the cells met by each class. -/
theorem incidence_energy_le_palette {ι : Type*} [DecidableEq ι]
    (D J : Finset (E2 × E2)) (cls : E2 × E2 → E2 × E2)
    (P : Finset E2) (cell : E2 → ι) (ρ M k : ℕ → ℝ)
    {h a : ℕ} (hha : h ≤ a) {L B : ℝ} (hL : (J.card : ℝ) ≤ L) (hB : 0 ≤ B)
    (hclasses : ∀ j ∈ J, ((cellsHit D cls P cell j).card : ℝ) ≤ B)
    (hdiam : ∀ p ∈ P, ∀ q ∈ P, cell p = cell q → dist p q ≤ ρ h)
    (hk : ∀ i ∈ Finset.Icc h a, 0 ≤ k i)
    (hM : ∀ p ∈ P, ∀ i ∈ Finset.Icc h a,
      ((P.filter fun q => dist p q ≤ ρ i).card : ℝ) ≤ M i)
    (hpair : ∀ p ∈ P, ∀ q ∈ P, ∀ i ∈ Finset.Icc h a, dist p q ≤ ρ i →
      (i = a ∨ ρ (i + 1) < dist p q) →
      ((J.filter fun j => p ∈ pinsOf D cls j ∧ q ∈ pinsOf D cls j).card : ℝ) ≤ k i) :
    (∑ j ∈ J, ((pinsOf D cls j ∩ P).card : ℝ)) ^ 2 ≤
      (L * B) * (P.card * ∑ i ∈ Finset.Icc h a, M i * k i) := by
  have hcount : (∑ j ∈ J, ((cellsHit D cls P cell j).card : ℝ)) ≤ L * B := by
    calc
      _ ≤ ∑ _j ∈ J, B := Finset.sum_le_sum hclasses
      _ = (J.card : ℝ) * B := by simp
      _ ≤ L * B := mul_le_mul_of_nonneg_right hL hB
  have henergy := cell_energy_le_palette D J cls P cell ρ M k hha hdiam hk hM hpair
  have hL0 : 0 ≤ L := (Nat.cast_nonneg _).trans hL
  exact (incidences_sq_le D cls J P cell).trans
    (mul_le_mul hcount henergy (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (mul_nonneg hL0 hB))

end WangZahlLot.Obl.wz_furstenberg_katz_tao_high.Columns
