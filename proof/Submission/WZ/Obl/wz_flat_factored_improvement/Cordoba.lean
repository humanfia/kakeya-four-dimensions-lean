-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.Cordoba.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabSelection
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.SlabVolume
import Submission.WZ.Obl.wz_regular_transverse_affine_cells.Containers
import Submission.WZ.Obl.wz_finite_shading_second_moment

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open scoped ENNReal
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (slab subset_enlarged_slab_of_mass finite_dyadic_mass_bound
    volume_ball_inter_slab_le slab_convex)

private abbrev V := EuclideanSpace ℝ (Fin 3)

open Classical in
/-- A volume-weighted convex-count hypothesis, applicable to noncongruent bodies. -/
def ConvexVolumeCount {n : ℕ} (U : Fin n → Set V) (m : ℝ) : Prop :=
  ∀ W : Set V, Convex ℝ W →
    (∑ i, if U i ⊆ W then volume (U i) else 0) ≤ ENNReal.ofReal m * volume W

/-- The convex-count bound controls each substantial slab-intersection level.
The only geometric input is the concentration lemma for a compact convex body. -/
theorem convex_slab_level {n : ℕ} (U : Fin n → Set V)
    (hUc : ∀ i, IsCompact (U i)) (hUconv : ∀ i, Convex ℝ (U i))
    (hUpos : ∀ i, volume (U i) ≠ 0)
    (hUb : ∀ i, U i ⊆ closedBall (0 : V) 1)
    {m : ℝ} (hm : 0 ≤ m) (hcount : ConvexVolumeCount U m)
    {u : V} (hu : ‖u‖ = 1) (s : ℝ) {a t : ℝ}
    (ha : 0 ≤ a) (ht : 0 < t) (ht1 : t ≤ 1) :
    t * (∑ i, if t * (volume (U i)).toReal ≤
        (volume (U i ∩ slab (innerSL ℝ u) s a)).toReal
      then (volume (U i)).toReal else 0) ≤ 640 * m * a := by
  classical
  let S := slab (innerSL ℝ u) s a
  let W := closedBall (0 : V) 1 ∩ slab (innerSL ℝ u) s (80 * a / t)
  have hsub (i : Fin n)
      (hi : t * (volume (U i)).toReal ≤ (volume (U i ∩ S)).toReal) : U i ⊆ W := by
    refine subset_inter (hUb i) ?_
    apply subset_enlarged_slab_of_mass (hUc i) (hUconv i) (hUpos i)
      (innerSL ℝ u) s a t ha ht ht1
    calc
      ENNReal.ofReal t * volume (U i) =
          ENNReal.ofReal (t * (volume (U i)).toReal) := by
        rw [ENNReal.ofReal_mul ht.le, ENNReal.ofReal_toReal (hUc i).measure_ne_top]
      _ ≤ ENNReal.ofReal (volume (U i ∩ S)).toReal := ENNReal.ofReal_le_ofReal hi
      _ = _ := ENNReal.ofReal_toReal
        (measure_ne_top_of_subset inter_subset_left (hUc i).measure_ne_top)
  have hWconv : Convex ℝ W :=
    (convex_closedBall (0 : V) 1).inter (slab_convex _ _ _)
  have hWvol : volume W ≤ ENNReal.ofReal (640 * a / t) := by
    have h := volume_ball_inter_slab_le hu s (by positivity : 0 ≤ 80 * a / t)
      (by norm_num : (0 : ℝ) ≤ 1)
    convert h using 1 <;> congr 1 <;> ring
  have hsum : (∑ i, if t * (volume (U i)).toReal ≤ (volume (U i ∩ S)).toReal
      then volume (U i) else 0) ≤ ENNReal.ofReal (640 * m * a / t) := by
    calc
      _ ≤ ∑ i, if U i ⊆ W then volume (U i) else 0 := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs with hi hW hW
        · exact le_rfl
        · exact False.elim (hW (hsub i hi))
        · exact bot_le
        · exact le_rfl
      _ ≤ ENNReal.ofReal m * volume W := hcount W hWconv
      _ ≤ ENNReal.ofReal m * ENNReal.ofReal (640 * a / t) := mul_le_mul' le_rfl hWvol
      _ = _ := by rw [← ENNReal.ofReal_mul hm]; congr 1; ring
  have he : ENNReal.ofReal
      (∑ i, if t * (volume (U i)).toReal ≤ (volume (U i ∩ S)).toReal
        then (volume (U i)).toReal else 0) =
      ∑ i, if t * (volume (U i)).toReal ≤ (volume (U i ∩ S)).toReal
        then volume (U i) else 0 := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp [ENNReal.ofReal_toReal (hUc i).measure_ne_top]
    · intro i _
      split_ifs <;> first | exact ENNReal.toReal_nonneg | exact le_rfl
  rw [← he] at hsum
  have hr := (ENNReal.ofReal_le_ofReal_iff (by positivity : 0 ≤ 640 * m * a / t)).mp hsum
  have hh := (le_div_iff₀ ht).mp hr
  simpa only [mul_comm] using hh

/-- A dyadic Córdoba row bound, retaining an explicit bottom-scale error. -/
theorem convex_slab_overlap {n : ℕ} (U : Fin n → Set V)
    (hUc : ∀ i, IsCompact (U i)) (hUconv : ∀ i, Convex ℝ (U i))
    (hUpos : ∀ i, volume (U i) ≠ 0)
    (hUb : ∀ i, U i ⊆ closedBall (0 : V) 1)
    {m : ℝ} (hm : 0 ≤ m) (hcount : ConvexVolumeCount U m)
    {u : V} (hu : ‖u‖ = 1) (s : ℝ) {a : ℝ} (ha : 0 ≤ a) (K : ℕ) :
    (∑ i, (volume (U i ∩ slab (innerSL ℝ u) s a)).toReal) ≤
      (1 / 2 : ℝ) ^ K * (∑ i, (volume (U i)).toReal) + 1280 * K * m * a := by
  have h := finite_dyadic_mass_bound Finset.univ
    (fun i => (volume (U i)).toReal)
    (fun i => (volume (U i ∩ slab (innerSL ℝ u) s a)).toReal)
    (fun _ _ => ENNReal.toReal_nonneg)
    (fun i _ => ENNReal.toReal_mono (hUc i).measure_ne_top (measure_mono inter_subset_left))
    K (640 * m * a)
    (fun k _ => convex_slab_level U hUc hUconv hUpos hUb hm hcount hu s ha
      (by positivity) (pow_le_one₀ (by norm_num) (by norm_num)))
  nlinarith only [h]

/-- Dense shadings of convex bodies of thickness `a` have a Córdoba lower bound.
For slabs, their common volume is a constant multiple of `a`. -/
theorem cordoba_shading_bound {n : ℕ} (U Y : Fin n → Set V)
    (hUc : ∀ i, IsCompact (U i)) (hUconv : ∀ i, Convex ℝ (U i))
    (hUpos : ∀ i, volume (U i) ≠ 0)
    (hUb : ∀ i, U i ⊆ closedBall (0 : V) 1)
    {m a q : ℝ} (hm : 0 < m) (ha : 0 < a) (hq : 0 ≤ q)
    (hcount : ConvexVolumeCount U m)
    (hslab : ∀ i, ∃ u : V, ‖u‖ = 1 ∧ ∃ s : ℝ, U i ⊆ slab (innerSL ℝ u) s a)
    (hYm : ∀ i, MeasurableSet (Y i)) (hYU : ∀ i, Y i ⊆ U i)
    (hden : ∀ i, q ≤ (volume (Y i)).toReal)
    (K : ℕ) (hbottom : (1 / 2 : ℝ) ^ K * (∑ i, (volume (U i)).toReal) ≤ m * a) :
    q ^ 2 * n ≤ ((1 + 1280 * K) * m * a) * (volume (⋃ i, Y i)).toReal := by
  classical
  have hrow (i : Fin n) : (∑ j, (volume (Y i ∩ Y j)).toReal) ≤
      (1 + 1280 * K) * m * a := by
    obtain ⟨u, hu, s, hs⟩ := hslab i
    have h := convex_slab_overlap U hUc hUconv hUpos hUb hm.le hcount hu s ha.le K
    calc
      _ ≤ ∑ j, (volume (U j ∩ slab (innerSL ℝ u) s a)).toReal := by
        apply Finset.sum_le_sum
        intro j _
        apply ENNReal.toReal_mono
          (measure_ne_top_of_subset inter_subset_left (hUc j).measure_ne_top)
        exact measure_mono (fun p hp => ⟨hYU j hp.2, hs (hYU i hp.1)⟩)
      _ ≤ _ := by nlinarith only [h, hbottom]
  have hfin : volume (⋃ i, Y i) ≠ ⊤ :=
    measure_ne_top_of_subset (iUnion_subset fun i => (hYU i).trans (hUb i))
      (isCompact_closedBall (0 : V) 1).measure_ne_top
  have h := WangZahlLot.wz_finite_shading_second_moment n Finset.univ Y (⋃ i, Y i)
    q ((1 + 1280 * K) * m * a) (MeasurableSet.iUnion hYm) hfin
    (fun i _ => hYm i) (fun i _ => subset_iUnion Y i) hq (by positivity)
    (fun i _ => hden i) (fun i _ => hrow i)
  simpa only [Finset.card_univ, Fintype.card_fin] using h

end WangZahlLot.Obl.wz_flat_factored_improvement
