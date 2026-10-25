-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_capped_prism_overlap.CappedCut.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.WeightedNarrow
import Submission.WZ.Obl.wz_move_two_capped_prism_overlap.PrismSelect
import Submission.WZ.Obl.wz_coarse_grains_assembly.DenseWeights

/- Adapted from this workspace: o197/x0567, 3d9d14b72629, CappedCut.lean. -/

noncomputable section

namespace WangZahlLot.Obl.wz_move_two_capped_prism_overlap

open Set MeasureTheory Metric Classical
open WangZahlLot.Obl.wz_clustered_cover_volume_gain (V O P I bodyCount shadingMeasure
  shadingMeasure_apply)
open WangZahlLot.Obl.wz_coarse_grains_assembly (rIdx rIdx_mem rIdx_injective)

/-- A spatial cut retaining half the incidence mass can be pruned to whole
prisms with one quarter of their previous effective density. -/
theorem select_capped_cut {ω ζ δ h h' ρ c τ : ℝ} {n : ℕ}
    (D : PrismData n) {x v : Fin n → V} {Y : Fin n → Set V}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hhh : h ≤ h') (hτ : 0 < τ)
    (hmassbudget : O (δ ^ h') ≤ (1 / 4 : ENNReal) * O (δ ^ h))
    (hdensitybudget : O (δ ^ h') ≤ O (τ / 4))
    (H : D.Valid ω ζ δ h ρ c x v Y 1) (hYI : ∀ i, Y i ⊆ I)
    (m : Fin D.L → ℝ) (hm : ∀ j, 0 < m j)
    (hcount : ∀ j p, bodyCount (fun i => D.W i j) p ≤ m j)
    (haverage : ∀ j, O (τ * m j) * volume (P D.a (ρ * c) c (D.z j) (D.e j)) ≤
      ∑ i, volume (D.W i j))
    (B : Set V) (hB : MeasurableSet B)
    (hretain : (1 / 2 : ENNReal) * (∑ i, ∑ j, volume (D.W i j)) ≤
      ∑ i, ∑ j, volume (D.W i j ∩ B)) :
    ∃ (L : ℕ) (f : Fin L → Fin D.L), Function.Injective f ∧
      let D' := (D.select D.s f id (D.γ ∘ f)).cut (fun _ => B)
      D'.Valid ω ζ δ h' ρ c x v Y 1 ∧
      (∀ j p, bodyCount (fun i => D'.W i j) p ≤ m (f j)) ∧
      (∀ j, O ((τ / 4) * m (f j)) * volume (P D'.a (ρ * c) c (D'.z j) (D'.e j)) ≤
        ∑ i, volume (D'.W i j)) := by
  classical
  let M (j : Fin D.L) := ∑ i, volume (D.W i j)
  let W (j : Fin D.L) := ∑ i, volume (D.W i j ∩ B)
  have hWm := H.2.2.2.2.1
  have hMfin (j : Fin D.L) : M j ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ne_top_of_le_ne_top measure_ball_lt_top.ne
      (measure_mono ((hWm i j).2.1.trans (inter_subset_left.trans (hYI i))))
  have hWle (j : Fin D.L) : W j ≤ M j :=
    Finset.sum_le_sum fun i _ => measure_mono inter_subset_left
  have hsum : O (∑ j, (M j).toReal) = ∑ j, M j := by
    change ENNReal.ofReal (∑ j, (M j).toReal) = _
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
    exact Finset.sum_congr rfl (fun j _ => ENNReal.ofReal_toReal (hMfin j))
  have hhalf : (1 / 2 : ENNReal) * (∑ j, M j) ≤ ∑ j, W j := by
    calc
      _ = (1 / 2 : ENNReal) * (∑ i, ∑ j, volume (D.W i j)) :=
        congrArg (fun t : ENNReal => (1 / 2 : ENNReal) * t) (Finset.sum_comm)
      _ ≤ ∑ i, ∑ j, volume (D.W i j ∩ B) := hretain
      _ = _ := Finset.sum_comm
  have hbudget : O (2 * (1 / 4 : ℝ) * ∑ j, (M j).toReal) ≤ ∑ j, W j := by
    calc
      _ = (1 / 2 : ENNReal) * ∑ j, M j := by
        change ENNReal.ofReal _ = _
        norm_num only [show (2 : ℝ) * (1 / 4) = 1 / 2 by norm_num]
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2), ← hsum]
        norm_num [O, ENNReal.ofReal_div_of_pos]
      _ ≤ _ := hhalf
  obtain ⟨J, _, hkeep, hgood⟩ :=
    WangZahlLot.Obl.wz_coarse_grains_assembly.select_dense_weights
      Finset.univ W (fun j => (M j).toReal) (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (fun j _ => ENNReal.toReal_nonneg)
      (fun j _ => ne_top_of_le_ne_top (hMfin j) (hWle j)) hbudget
  let f := rIdx J
  have hf : Function.Injective f := rIdx_injective J
  have hidx (F : Fin D.L → ENNReal) : ∑ j : Fin J.card, F (f j) = ∑ j ∈ J, F j := by
    calc
      _ = ∑ j : J, F j.val := J.equivFin.symm.sum_comp _
      _ = _ := Finset.sum_coe_sort J F
  have hquarter : (1 / 4 : ENNReal) * (∑ j, M j) ≤ ∑ j : Fin J.card, W (f j) := by
    rw [hidx]
    calc
      _ = (1 / 2 : ENNReal) * ((1 / 2 : ENNReal) * ∑ j, M j) := by
        norm_num [one_div, ← mul_assoc, ← ENNReal.mul_inv]
      _ ≤ (1 / 2 : ENNReal) * ∑ j, W j := mul_le_mul' le_rfl hhalf
      _ ≤ (1 / 2 : ENNReal) * (2 * ∑ j ∈ J, W j) := mul_le_mul' le_rfl hkeep
      _ = _ := by
        rw [← mul_assoc, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
  have hmass : O (δ ^ h') * ∑ i, volume (Y i) ≤
      ∑ i, ∑ j : Fin J.card, volume (D.W i (f j) ∩ B) := by
    calc
      _ ≤ ((1 / 4 : ENNReal) * O (δ ^ h)) * ∑ i, volume (Y i) :=
        mul_le_mul' hmassbudget le_rfl
      _ ≤ (1 / 4 : ENNReal) * (∑ i, ∑ j, volume (D.W i j)) := by
        rw [mul_assoc]
        exact mul_le_mul' le_rfl H.2.2.2.2.2.1
      _ = (1 / 4 : ENNReal) * (∑ j, M j) :=
        congrArg (fun t : ENNReal => (1 / 4 : ENNReal) * t) (Finset.sum_comm)
      _ ≤ ∑ j : Fin J.card, W (f j) := hquarter
      _ = _ := Finset.sum_comm
  have hlocal (j : Fin J.card) : O ((τ / 4) * m (f j)) *
      volume (P D.a (ρ * c) c (D.z (f j)) (D.e (f j))) ≤ W (f j) := by
    calc
      _ = (1 / 4 : ENNReal) * (O (τ * m (f j)) *
          volume (P D.a (ρ * c) c (D.z (f j)) (D.e (f j)))) := by
        change ENNReal.ofReal _ * _ = _
        rw [show τ / 4 * m (f j) = (1 / 4 : ℝ) * (τ * m (f j)) by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        norm_num [O, ENNReal.ofReal_div_of_pos, mul_assoc]
      _ ≤ (1 / 4 : ENNReal) * M (f j) := mul_le_mul' le_rfl (haverage (f j))
      _ = O ((1 / 4 : ℝ) * (M (f j)).toReal) := by
        change _ = ENNReal.ofReal _
        rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
          ENNReal.ofReal_toReal (hMfin (f j))]
        norm_num [O, ENNReal.ofReal_div_of_pos]
      _ ≤ _ := (hgood (f j) (rIdx_mem J j)).2
  let D₀ := D.select D.s f id (D.γ ∘ f)
  have H₀ : D₀.Valid ω ζ δ h' ρ c x v Y 1 := by
    apply valid_select_prisms D hδ hδ1 hhh H f hf
    exact hmass.trans (Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => measure_mono inter_subset_left)
  have hcount' (j : Fin J.card) (p : V) :
      bodyCount (fun i => D.W i (f j) ∩ B) p ≤ m (f j) := by
    by_cases hp : p ∈ B
    · simpa [bodyCount, hp] using hcount (f j) p
    · simp [bodyCount, hp, (hm (f j)).le]
  have hdense (j : Fin J.card) : O (τ / 4) *
      volume (P D.a (ρ * c) c (D.z (f j)) (D.e (f j))) ≤
        volume (⋃ i, D.W i (f j) ∩ B) := by
    let S := ⋃ i, D.W i (f j) ∩ B
    have hSm : MeasurableSet S := MeasurableSet.iUnion fun i => (hWm i (f j)).1.inter hB
    have hdom := incidence_measure_domination (fun i => D.W i (f j) ∩ B)
      (fun i => (hWm i (f j)).1.inter hB) (hm (f j)).le (hcount' j) S hSm
    have heq : shadingMeasure (fun i => D.W i (f j) ∩ B) S = W (f j) := by
      rw [shadingMeasure_apply _ hSm]
      apply Finset.sum_congr rfl
      intro i _
      rw [inter_eq_left.mpr (subset_iUnion (fun i => D.W i (f j) ∩ B) i)]
    rw [heq] at hdom
    have hh := (hlocal j).trans hdom
    change ENNReal.ofReal (τ / 4 * m (f j)) * _ ≤ _ at hh
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ τ / 4)] at hh
    have he : O (τ / 4) * O (m (f j)) *
        volume (P D.a (ρ * c) c (D.z (f j)) (D.e (f j))) =
        O (m (f j)) * (O (τ / 4) *
          volume (P D.a (ρ * c) c (D.z (f j)) (D.e (f j)))) := by ring
    rw [he] at hh
    exact (ENNReal.mul_le_mul_iff_right (ENNReal.ofReal_pos.mpr (hm (f j))).ne'
      ENNReal.ofReal_ne_top).mp hh
  refine ⟨J.card, f, hf, ?_, hcount', hlocal⟩
  apply valid_cut D₀ hδ hδ1 le_rfl H₀ (fun _ => B) (fun _ => hB) hmass
  intro j
  exact (mul_le_mul' hdensitybudget le_rfl).trans (hdense j)

end WangZahlLot.Obl.wz_move_two_capped_prism_overlap
