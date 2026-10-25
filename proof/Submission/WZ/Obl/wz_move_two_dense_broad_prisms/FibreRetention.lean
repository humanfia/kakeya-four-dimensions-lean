-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.FibreRetention.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/- Adapted from session x0449 on o152 in this workspace. -/
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.GrainTransfer
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

/-! Turning a mass refinement into a pointwise incidence refinement. -/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Set LeanEval.Analysis.WangZahlKakeya
open WangZahlLot.Obl.wz_clustered_cover_volume_gain
open scoped ENNReal

/-- A half-mass refinement can be pruned to a quarter-mass refinement whose
surviving fibre points keep a quarter of their original incidences. The pruning
uses a common measurable set in each fibre, so its new fibre counts are exact. -/
theorem retain_fibre_incidence_fraction {n N : ℕ} (f : Fin n → Fin N)
    {Y Z : Fin n → Set Space} (hYm : ∀ i, MeasurableSet (Y i))
    (hZm : ∀ i, MeasurableSet (Z i)) (hYfin : ∀ i, volume (Y i) ≠ ∞)
    (hZY : ∀ i, Z i ⊆ Y i)
    (hmass : (1 / 2 : ℝ≥0∞) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i)) :
    ∃ W : Fin n → Set Space,
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Z i) ∧
      ENNReal.ofReal (1 / 4) * (∑ i, volume (Y i)) ≤ ∑ i, volume (W i) ∧
      ∀ k p, (∃ i, f i = k ∧ p ∈ W i) →
        fiberBodyCount f Y k p ≤ 4 * fiberBodyCount f W k p := by
  classical
  have hmeas : ∀ (U : Fin n → Set Space), (∀ i, MeasurableSet (U i)) →
      ∀ k, Measurable (fiberBodyCount f U k) := by
    intro U hU k
    exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hU i))
  let G : Fin N → Set Space := fun k => {p | fiberBodyCount f Y k p ≤ 4 * fiberBodyCount f Z k p}
  let W : Fin n → Set Space := fun i => Z i ∩ G (f i)
  let B : Fin n → Set Space := fun i => Z i ∩ (G (f i))ᶜ
  have hGm : ∀ k, MeasurableSet (G k) :=
    fun k => measurableSet_le (hmeas Y hYm k) ((hmeas Z hZm k).const_mul 4)
  have hWm : ∀ i, MeasurableSet (W i) := fun i => (hZm i).inter (hGm (f i))
  have hBm : ∀ i, MeasurableSet (B i) := fun i => (hZm i).inter (hGm (f i)).compl
  have hZfin : (∑ i, volume (Z i)) ≠ ∞ := ENNReal.sum_ne_top.mpr
    (fun i _ => measure_ne_top_of_subset (hZY i) (hYfin i))
  have hbadcount : ∀ p, bodyCount B p ≤ (1 / 4) * bodyCount Y p := by
    intro p
    rw [← sum_fiberBodyCount f B p, ← sum_fiberBodyCount f Y p, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    change fiberBodyCount f (fun i => Z i ∩ (G (f i))ᶜ) k p ≤ _
    rw [fiberBodyCount_restrict f Z (fun k => (G k)ᶜ) k p]
    by_cases hp : p ∈ (G k)ᶜ
    · rw [indicator_of_mem hp]
      have hlt : 4 * fiberBodyCount f Z k p < fiberBodyCount f Y k p := lt_of_not_ge hp
      linarith
    · rw [indicator_of_notMem hp]
      have hnon : 0 ≤ fiberBodyCount f Y k p := by rw [fiberBodyCount_eq_ncard]; positivity
      positivity
  have hbadmass : (∑ i, volume (B i)) ≤ ENNReal.ofReal (1 / 4) * ∑ i, volume (Y i) :=
    body_mass_le_mul_of_count hBm hYm (by norm_num) hbadcount
  have hbalance : (∑ i, volume (Z i)) = (∑ i, volume (W i)) + ∑ i, volume (B i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [W, B, Set.sdiff_eq] using (measure_inter_add_sdiff (Z i) (hGm (f i))).symm
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 / 2 : ℝ≥0∞) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hquarter : ENNReal.ofReal (1 / 4 : ℝ) = (1 / 2 : ℝ≥0∞) * (1 / 2 : ℝ≥0∞) := by
    calc ENNReal.ofReal (1 / 4 : ℝ) = ENNReal.ofReal ((1 / 2 : ℝ) * (1 / 2)) := by norm_num
      _ = ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal (1 / 2 : ℝ) :=
        ENNReal.ofReal_mul (by norm_num)
      _ = _ := by rw [hhalf]
  have hbudget : (∑ i, volume (B i)) ≤ (1 / 2 : ℝ≥0∞) * ∑ i, volume (Z i) := by
    refine hbadmass.trans ?_
    rw [hquarter, mul_assoc]
    exact mul_le_mul_right hmass _
  have hWmass := half_mass_after_loss hZfin hbalance.le hbudget
  refine ⟨W, fun i => ⟨hWm i, inter_subset_left⟩, ?_, ?_⟩
  · rw [hquarter, mul_assoc]
    exact (mul_le_mul_right hmass _).trans hWmass
  · intro k p hp
    obtain ⟨i, hik, hpi⟩ := hp
    have hpG : p ∈ G k := hik ▸ hpi.2
    have hcount : fiberBodyCount f W k p = fiberBodyCount f Z k p := by
      exact (fiberBodyCount_restrict f Z G k p).trans (indicator_of_mem hpG _)
    rw [hcount]
    exact hpG

/-- A quantitative mass refinement can be made pointwise on every fibre. -/
theorem retain_fibre_incidence_ratio {n N : ℕ} (f : Fin n → Fin N)
    {Y Z : Fin n → Set Space} (hYm : ∀ i, MeasurableSet (Y i))
    (hZm : ∀ i, MeasurableSet (Z i)) (hYfin : ∀ i, volume (Y i) ≠ ∞)
    (hZY : ∀ i, Z i ⊆ Y i) {q : ℝ} (hq : 0 ≤ q)
    (hmass : ENNReal.ofReal q * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i)) :
    ∃ W : Fin n → Set Space,
      (∀ i, MeasurableSet (W i) ∧ W i ⊆ Z i) ∧
      ENNReal.ofReal (q/2) * (∑ i, volume (Y i)) ≤ ∑ i, volume (W i) ∧
      ∀ k p, (∃ i, f i = k ∧ p ∈ W i) →
        (q/2) * fiberBodyCount f Y k p ≤ fiberBodyCount f W k p := by
  classical
  have hmeas : ∀ (U : Fin n → Set Space), (∀ i, MeasurableSet (U i)) →
      ∀ k, Measurable (fiberBodyCount f U k) := by
    intro U hU k
    exact Finset.measurable_sum _ (fun i _ => measurable_const.indicator (hU i))
  let G : Fin N → Set Space := fun k =>
    {p | (q/2) * fiberBodyCount f Y k p ≤ fiberBodyCount f Z k p}
  let W : Fin n → Set Space := fun i => Z i ∩ G (f i)
  let B : Fin n → Set Space := fun i => Z i ∩ (G (f i))ᶜ
  have hGm : ∀ k, MeasurableSet (G k) := fun k =>
    measurableSet_le ((hmeas Y hYm k).const_mul _) (hmeas Z hZm k)
  have hWm : ∀ i, MeasurableSet (W i) := fun i => (hZm i).inter (hGm (f i))
  have hBm : ∀ i, MeasurableSet (B i) := fun i => (hZm i).inter (hGm (f i)).compl
  have hZfin : (∑ i, volume (Z i)) ≠ ∞ := ENNReal.sum_ne_top.mpr
    (fun i _ => measure_ne_top_of_subset (hZY i) (hYfin i))
  have hbadcount : ∀ p, bodyCount B p ≤ (q/2) * bodyCount Y p := by
    intro p
    rw [← sum_fiberBodyCount f B p, ← sum_fiberBodyCount f Y p, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    change fiberBodyCount f (fun i => Z i ∩ (G (f i))ᶜ) k p ≤ _
    rw [fiberBodyCount_restrict f Z (fun k => (G k)ᶜ) k p]
    by_cases hp : p ∈ (G k)ᶜ
    · rw [indicator_of_mem hp]
      exact (lt_of_not_ge (show ¬ (q/2) * fiberBodyCount f Y k p ≤ fiberBodyCount f Z k p from hp)).le
    · rw [indicator_of_notMem hp]
      have hnon : 0 ≤ fiberBodyCount f Y k p := by rw [fiberBodyCount_eq_ncard]; positivity
      positivity
  have hbadmass : (∑ i, volume (B i)) ≤ ENNReal.ofReal (q/2) * ∑ i, volume (Y i) :=
    body_mass_le_mul_of_count hBm hYm (by positivity) hbadcount
  have hbalance : (∑ i, volume (Z i)) = (∑ i, volume (W i)) + ∑ i, volume (B i) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [W, B, Set.sdiff_eq] using (measure_inter_add_sdiff (Z i) (hGm (f i))).symm
  have hcoeff : ENNReal.ofReal (q/2) = (1/2 : ENNReal) * ENNReal.ofReal q := by
    rw [show q/2 = (1/2)*q by ring, ENNReal.ofReal_mul (by norm_num)]
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    norm_num
  have hbudget : (∑ i, volume (B i)) ≤ (1/2 : ENNReal) * ∑ i, volume (Z i) := by
    refine hbadmass.trans ?_
    rw [hcoeff, mul_assoc]
    exact mul_le_mul_right hmass _
  have hWmass := half_mass_after_loss hZfin hbalance.le hbudget
  refine ⟨W, fun i => ⟨hWm i, inter_subset_left⟩, ?_, ?_⟩
  · rw [hcoeff, mul_assoc]
    exact (mul_le_mul_right hmass _).trans hWmass
  · rintro k p ⟨i, hik, hpi⟩
    have hpG : p ∈ G k := hik ▸ hpi.2
    have hcount : fiberBodyCount f W k p = fiberBodyCount f Z k p :=
      (fiberBodyCount_restrict f Z G k p).trans (indicator_of_mem hpG _)
    rw [hcount]
    exact hpG

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
