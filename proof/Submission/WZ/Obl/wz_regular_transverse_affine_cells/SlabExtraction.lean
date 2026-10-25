-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_regular_transverse_affine_cells.SlabExtraction.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabSelection

namespace WangZahlLot.Obl.wz_regular_transverse_affine_cells

open MeasureTheory Set
open scoped ENNReal

/-- The intrinsic slab estimate delivered by one maximal-density selection. -/
def SlabFamilyGood {ι : Type*} (U : ι → Set E) (I : Finset ι) (W : Set E) : Prop :=
  ∃ S : SlabSpec, W = S.carrier ∧ S.width ≤ 2 ∧
    ∀ T : SlabSpec, T.weight I U (fun i => (volume (U i)).toReal) / T.width ≤
      2 * (∑ i ∈ I, (volume (U i)).toReal) / S.width

/-- The geometric selector required by `greedy_container_extraction`. -/
lemma select_slab_container {ι : Type*} (F : Finset ι) (hF : F.Nonempty)
    (U : ι → Set E) (hUc : ∀ i ∈ F, IsCompact (U i))
    (hUconv : ∀ i ∈ F, Convex ℝ (U i)) (hUpos : ∀ i ∈ F, volume (U i) ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hballs : ∀ i ∈ F, ∃ x, Metric.ball x δ ⊆ U i)
    (hbounded : ∀ i ∈ F, U i ⊆ Metric.closedBall (0 : E) 1)
    (K : ℕ) (w₀ : ℝ)
    (hw₀ : ∀ i ∈ F, w₀ ≤ (volume (U i)).toReal)
    (hbottom : (1 / 2 : ℝ) ^ K * (∑ i ∈ F, (volume (U i)).toReal) ≤ w₀) :
    ∃ (I : Finset ι) (W : Set E), I.Nonempty ∧ I ⊆ F ∧ MeasurableSet W ∧
      SlabFamilyGood U I W ∧ (∀ i ∈ I, U i ⊆ W) ∧
      ∑ i ∈ F, volume (U i ∩ W) ≤
        ENNReal.ofReal (1 + 320 * K : ℝ) * ∑ i ∈ I, volume (U i) := by
  classical
  let w : ι → ℝ := fun i => (volume (U i)).toReal
  have hw : ∀ i ∈ F, 0 < w i :=
    fun i hi => ENNReal.toReal_pos (hUpos i hi) (hUc i hi).measure_ne_top
  obtain ⟨S, hwidth, hSpos, hmax⟩ := exists_near_maximal_slab F hF U w hw hδ hballs hbounded
  let I := F.filter fun i => U i ⊆ S.carrier
  have hIF : I ⊆ F := Finset.filter_subset _ _
  have hweight : S.weight F U w = ∑ i ∈ I, w i := by
    simp only [I, SlabSpec.weight, Finset.sum_filter]
  have hI : I.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hI
    rw [hweight, hI, Finset.sum_empty] at hSpos
    exact (lt_irrefl 0) hSpos
  have hbottom' : (1 / 2 : ℝ) ^ K * (∑ i ∈ F, w i) ≤ S.weight F U w := by
    obtain ⟨i, hi⟩ := hI
    rw [hweight]
    exact hbottom.trans ((hw₀ i (hIF hi)).trans
      (Finset.single_le_sum (f := w) (fun j _ => ENNReal.toReal_nonneg) hi))
  have hover := near_maximal_slab_overlap_bound F U hUc hUconv hUpos S hmax K hbottom'
  refine ⟨I, S.carrier, hI, hIF, (slab_isClosed _ _ _).measurableSet, ?_, ?_, ?_⟩
  · refine ⟨S, rfl, hwidth, fun T => ?_⟩
    have hwT : T.weight I U w ≤ T.weight F U w := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hIF
      intro i hi _
      split_ifs <;> first | exact ENNReal.toReal_nonneg | exact le_rfl
    calc T.weight I U w / T.width ≤ T.weight F U w / T.width :=
          div_le_div_of_nonneg_right hwT T.width_pos.le
      _ ≤ 2 * (S.weight F U w / S.width) := hmax T
      _ = _ := by rw [hweight, mul_div_assoc]
  · intro i hi
    exact (Finset.mem_filter.mp hi).2
  · have hreal := ENNReal.ofReal_le_ofReal hover
    rw [hweight] at hreal
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg),
      ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_sum_of_nonneg (fun _ _ => ENNReal.toReal_nonneg)] at hreal
    have hleft : (∑ i ∈ F, ENNReal.ofReal (volume (U i ∩ S.carrier)).toReal) =
        ∑ i ∈ F, volume (U i ∩ S.carrier) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ENNReal.ofReal_toReal
        (measure_ne_top_of_subset inter_subset_left (hUc i hi).measure_ne_top)
    have hright : (∑ i ∈ I, ENNReal.ofReal (volume (U i)).toReal) = ∑ i ∈ I, volume (U i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact ENNReal.ofReal_toReal (hUc i (hIF hi)).measure_ne_top
    simpa only [hleft, hright] using hreal

/-- A quantitative slab extraction: whole convex sets are retained, selected
shadings have disjoint supports, and only `1 + 320*K` is lost in the mass accounting. -/
lemma greedy_slab_extraction {ι : Type*} [Fintype ι]
    (U Y : ι → Set E) (hUc : ∀ i, IsCompact (U i))
    (hUconv : ∀ i, Convex ℝ (U i)) (hUpos : ∀ i, volume (U i) ≠ 0)
    {δ : ℝ} (hδ : 0 < δ)
    (hballs : ∀ i, ∃ x, Metric.ball x δ ⊆ U i)
    (hbounded : ∀ i, U i ⊆ Metric.closedBall (0 : E) 1)
    (K : ℕ) (w₀ : ℝ) (hw₀ : ∀ i, w₀ ≤ (volume (U i)).toReal)
    (hbottom : (1 / 2 : ℝ) ^ K * (∑ i, (volume (U i)).toReal) ≤ w₀)
    (θ : ℝ≥0∞) (hθfin : θ ≠ ∞)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYU : ∀ i, Y i ⊆ U i)
    (hdense : ∀ i, (2 * θ) * volume (U i) ≤ volume (Y i)) :
    ∃ (m : ℕ) (C : Fin m → ShadedCell ι),
      (∀ j, (C j).Valid Finset.univ U Y θ (SlabFamilyGood U)) ∧
      Pairwise (fun j k => Disjoint (C j).support (C k).support) ∧
      θ * ∑ i, volume (U i) ≤
        ENNReal.ofReal (1 + 320 * K : ℝ) * ∑ j, ∑ i ∈ (C j).indices, volume (U i) := by
  classical
  apply greedy_container_retained_weight U (SlabFamilyGood U)
    (ENNReal.ofReal (1 + 320 * K : ℝ)) θ hθfin
  · intro F hF
    apply select_slab_container F hF U (fun i _ => hUc i) (fun i _ => hUconv i)
      (fun i _ => hUpos i) hδ (fun i _ => hballs i) (fun i _ => hbounded i)
      K w₀ (fun i _ => hw₀ i)
    apply le_trans _ hbottom
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    intro i _ _
    exact ENNReal.toReal_nonneg
  · intro i _
    exact hYm i
  · intro i _
    exact hYU i
  · intro i _
    exact (hUc i).measure_ne_top
  · intro i _
    exact hdense i

end WangZahlLot.Obl.wz_regular_transverse_affine_cells
