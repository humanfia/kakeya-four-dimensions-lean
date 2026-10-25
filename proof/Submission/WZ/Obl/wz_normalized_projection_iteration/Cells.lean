-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_normalized_projection_iteration.Cells.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_normalized_projection_iteration.CoarseGeometry
import Submission.WZ.Obl.wz_normalized_projection_iteration.Selection

namespace WangZahlLot.Obl.wz_normalized_projection_iteration

open Set Metric MeasureTheory
open scoped ENNReal

/-- Group a finite family by its line cells, regularize occupancy, and retain a separated color. -/
theorem select_cells {η δ r τ : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r)
    (hr1 : r ≤ 1 / 100000) (hτ : 0 < τ)
    {n : ℕ} {x v : Fin n → Space} {Y : Fin n → Set Space}
    (hH : Family η δ n x v Y) (hv2 : ∀ i, (1 / 2 : ℝ) ≤ v i 2) :
    ∃ m M : ℕ, 0 < m ∧ 0 < M ∧
    ∃ (A : Fin m → Finset (Fin n)) (a : Fin m → Fin n),
      Pairwise (fun i j => Disjoint (A i) (A j)) ∧
      (∀ j, M ≤ (A j).card ∧ (A j).card ≤ 2 * M) ∧
      (∀ j, ∀ i ∈ A j, (volume (Y i)).toReal ≤ (volume (Y (a j))).toReal) ∧
      (∀ j, ∀ i ∈ A j, lineCell r (x i) (v i) = lineCell r (x (a j)) (v (a j))) ∧
      (∀ i j, i ≠ j →
        volume (Tube r (inwardStart r (x (a i)) (v (a i))) (v (a i)) ∩
          Tube r (inwardStart r (x (a j)) (v (a j))) (v (a j))) ≤
        (1 / 2 : ENNReal) * volume (Tube r (inwardStart r (x (a i)) (v (a i))) (v (a i)))) ∧
      (∑ i, (volume (Y i)).toReal) * ((1 - (2 : ℝ) ^ (-τ)) / 2) * (n : ℝ) ^ (-τ) ≤
        (linePalette : ℝ) * ∑ j, ∑ i ∈ A j, (volume (Y i)).toReal := by
  classical
  have hr : 0 < r := hδ.trans_le hδr
  obtain ⟨k, g, hg, hgeq⟩ := finite_label_map (fun i => lineCell r (x i) (v i))
  let B : Fin k → Finset (Fin n) := fun j => Finset.univ.filter fun i => g i = j
  have hBmem (i : Fin n) (j : Fin k) : i ∈ B j ↔ g i = j := by simp [B]
  obtain ⟨b, hb, hbmax⟩ := choose_fibre_max g hg (fun i => (volume (Y i)).toReal)
  have hbinj : Function.Injective (fun j => lineCell r (x (b j)) (v (b j))) := by
    intro i j hij
    have hh := (hgeq (b i) (b j)).mpr hij
    simpa only [hb] using hh
  have hx (i : Fin n) : ‖x i‖ ≤ 1 := by
    have hh := hH.2.2.1 i ((self_subset_thickening hδ _) (left_mem_segment ℝ (x i) (x i + v i)))
    exact (by simpa using hh : ‖x i‖ < 1).le
  have hxv (i : Fin n) : ‖x i + v i‖ ≤ 1 := by
    have hh := hH.2.2.1 i ((self_subset_thickening hδ _) (right_mem_segment ℝ (x i) (x i + v i)))
    exact (by simpa using hh : ‖x i + v i‖ < 1).le
  obtain ⟨color, hcolor⟩ := color_line_cells hr hr1 (fun j => x (b j)) (fun j => v (b j))
    (fun j => hH.2.1 (b j)) (fun j => hv2 (b j)) (fun j => hx (b j))
    (fun j => hxv (b j)) hbinj
  let weight : Fin k → ℝ := fun j => ∑ i ∈ B j, (volume (Y i)).toReal
  have hweights : (∑ j, weight j) = ∑ i, (volume (Y i)).toReal := by
    dsimp only [weight, B]
    exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _
  have hYfinite (i : Fin n) : volume (Y i) ≠ ⊤ :=
    ((measure_mono ((hH.2.2.2.2.2.1 i).trans (hH.2.2.1 i))).trans_lt measure_ball_lt_top).ne
  have hsumfinite : (∑ i, volume (Y i)) ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun i _ => hYfinite i)
  have hmassreal : δ ^ η * (n : ℝ) * δ ^ 2 ≤ ∑ i, (volume (Y i)).toReal := by
    have hh := ENNReal.toReal_mono hsumfinite hH.2.2.2.2.2.2
    simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ δ ^ η * (n : ℝ) * δ ^ 2),
      ENNReal.toReal_sum (fun i _ => hYfinite i)] using hh
  have hmass : 0 < ∑ j, weight j := by
    rw [hweights]
    have hn : (0 : ℝ) < n := Nat.cast_pos.mpr hH.1
    exact (by positivity : 0 < δ ^ η * (n : ℝ) * δ ^ 2).trans_le hmassreal
  obtain ⟨M, hM, S, hS, hsize, hsame, hretain⟩ := select_uniform_colored_groups (n := n)
    (show 0 < linePalette by norm_num [linePalette]) (fun j => (B j).card)
    (fun j => ⟨Finset.card_pos.mpr ⟨b j, (hBmem _ _).mpr (hb j)⟩,
      (Finset.card_le_card (Finset.subset_univ _)).trans_eq (by simp)⟩)
    color weight (fun j => Finset.sum_nonneg (fun i _ => ENNReal.toReal_nonneg)) hmass hτ
  let A : Fin S.card → Finset (Fin n) := fun j => B (enumerate S j)
  let a : Fin S.card → Fin n := fun j => b (enumerate S j)
  refine ⟨S.card, M, Finset.card_pos.mpr hS, hM, A, a, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro p hpi hpj
    have hi := (hBmem _ _).mp hpi
    have hj := (hBmem _ _).mp hpj
    exact hij (enumerate_injective S (hi.symm.trans hj))
  · intro j
    exact ⟨(hsize _ (enumerate_mem _ _)).1, (hsize _ (enumerate_mem _ _)).2.le⟩
  · intro j i hi
    have hh := hbmax i
    rw [(hBmem _ _).mp hi] at hh
    exact hh
  · intro j i hi
    apply (hgeq _ _).mp
    exact ((hBmem _ _).mp hi).trans (hb _).symm
  · intro i j hij
    exact hcolor _ _ (fun h => hij (enumerate_injective S h))
      (hsame _ (enumerate_mem _ _) _ (enumerate_mem _ _))
  · rw [hweights] at hretain
    convert hretain using 1
    congr 1
    exact sum_enumerate S weight

end WangZahlLot.Obl.wz_normalized_projection_iteration
