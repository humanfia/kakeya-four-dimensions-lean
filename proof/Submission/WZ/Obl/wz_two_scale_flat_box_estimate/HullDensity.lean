-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.HullDensity.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.BoxGrid
import Submission.WZ.Obl.wz_flat_factored_improvement.GridHull

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_flat_factored_improvement
  (shortMap shortMap_volume closedTube_isCompact shortMap_thickTube_slab
   gridHull gridHull_density gridHull_subset_thickTube gridHull_subset gridHull_measurable
   ConvexVolumeCount closedTube_convex_count cordoba_shading_bound)
open WangZahlLot.Obl.wz_regular_transverse_affine_cells
  (closedTube closedTube_convex closedTube_volume_bounds tube_subset_closedTube)
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridUnion gridUnion_volume_ne_top)

set_option maxHeartbeats 800000 in
/-- The fine shadings give density in short-scale cubes; convex counting is used
only for their distinct coarse parents. -/
theorem coarse_parent_hull_density {δ ρ a b c lam L : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ) (hδa : δ ≤ a) (hρa : ρ ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hc8 : c ≤ 8) (haSmall : a ≤ 1 / 100)
    (hlam : 0 < lam) (hL : 1 ≤ L)
    (z : Space) (e : Space ≃ₗᵢ[ℝ] Space) {n : ℕ} (hn : 0 < n)
    (x v y w : Fin n → Space) (Y : Fin n → Set Space) (s : Finset (Fin 3 → ℤ))
    (hv : ∀ i, ‖v i‖ = 1) (hw : ∀ i, ‖w i‖ = 1)
    (hT : ∀ i, Tube ρ (y i) (w i) ⊆ Box a b c z e)
    (hYfine : ∀ i, Y i ⊆ Tube δ (x i) (v i))
    (hYcoarse : ∀ i, Y i ⊆ Tube ρ (y i) (w i))
    (hYgrid : ∀ i, Y i ⊆ gridUnion a s)
    (hden : ∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i))
    (hraw : ∀ W : Set Space, Convex ℝ W →
      ENNReal.ofReal (Set.ncard {i | Tube ρ (y i) (w i) ⊆ W} : ℝ) ≤
        ENNReal.ofReal (L * n / (a * b)) * volume W)
    (K : ℕ) (hK : (1 / 2 : ℝ) ^ K ≤ δ) :
    ENNReal.ofReal (lam ^ 2 * a * b / ((10 : ℝ) ^ (15 : ℕ) * L * (K + 1 : ℕ))) ≤
      volume (gridUnion a s) := by
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL' : 0 < L := zero_lt_one.trans_le hL
  let f := shortMap (boxFrame z e) a ha
  let J := 1 / (262144 * a)
  let W := J * (3 * a) ^ 2
  let C := L * n / (a * b)
  let m := 384 * (C * (3 * a) ^ 2)
  let U := fun i => f '' closedTube (3 * a) (y i) (w i)
  let Z := fun i => f '' gridHull a s (Y i)
  have hJ : 0 < J := by dsimp [J]; positivity
  have hW : 0 < W := by dsimp [W]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have h3a : 0 < 3 * a := by positivity
  have h3a1 : 3 * a ≤ 1 := by linarith
  have hvol : ∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q := shortMap_volume _ ha
  have hUc : ∀ i, IsCompact (U i) := fun i =>
    (closedTube_isCompact _ _ _).image f.toContinuousAffineEquiv.continuous
  have hUconv : ∀ i, Convex ℝ (U i) := fun i =>
    (closedTube_convex _ _ _).affine_image f.toAffineMap
  have hUb : ∀ i, U i ⊆ closedBall (0 : Space) 1 := fun i =>
    shortMap_box_tubes_bounded hρ ha haSmall hbc hc8 z e (hT i)
  have hUV (i : Fin n) : ENNReal.ofReal W ≤ volume (U i) ∧
      volume (U i) ≤ ENNReal.ofReal (384 * W) := by
    obtain ⟨hl, hu⟩ := closedTube_volume_bounds h3a h3a1 (y i) (w i) (hw i)
    change ENNReal.ofReal W ≤ volume (f '' _) ∧ _
    rw [hvol]
    constructor
    · rw [show W = J * (3 * a) ^ 2 from rfl, ENNReal.ofReal_mul hJ.le]
      exact mul_le_mul' le_rfl hl
    · calc
        _ ≤ ENNReal.ofReal J * ENNReal.ofReal (384 * (3 * a) ^ 2) := mul_le_mul' le_rfl hu
        _ = _ := by rw [← ENNReal.ofReal_mul hJ.le]; congr 1; dsimp [W]; ring
  have hUpos : ∀ i, volume (U i) ≠ 0 := fun i =>
    ne_of_gt ((ENNReal.ofReal_pos.mpr hW).trans_le (hUV i).1)
  have hraw3 : ∀ Q : Set Space, Convex ℝ Q →
      ENNReal.ofReal (Set.ncard {i | Tube (3 * a) (y i) (w i) ⊆ Q} : ℝ) ≤ ENNReal.ofReal C * volume Q := by
    intro Q hQ
    have hh : Set.ncard {i | Tube (3 * a) (y i) (w i) ⊆ Q} ≤
        Set.ncard {i | Tube ρ (y i) (w i) ⊆ Q} :=
      ncard_mono (fun i hi => (thickening_mono (by linarith : ρ ≤ 3 * a) _).trans hi)
    exact (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hh)).trans (hraw Q hQ)
  have hcount : ConvexVolumeCount U m :=
    ((closedTube_convex_count hC.le y w hraw3).affine_image (sq_nonneg _) hJ f hvol).volume_weighted
      (by norm_num : (0 : ℝ) ≤ 384) (by positivity) (fun i => (hUV i).2)
  have hZsub : ∀ i, Z i ⊆ U i := fun i => image_mono
    ((gridHull_subset_thickTube ha hρa s (hYcoarse i)).trans (tube_subset_closedTube _ _ _))
  have hZd : ∀ i, J * (lam * a ^ 2 / 16) ≤ (volume (Z i)).toReal := by
    intro i
    apply (ENNReal.ofReal_le_iff_le_toReal
      (ne_top_of_le_ne_top (hUc i).measure_ne_top (measure_mono (hZsub i)))).mp
    rw [ENNReal.ofReal_mul hJ.le]
    change _ ≤ volume (f '' _)
    rw [hvol]
    exact mul_le_mul' le_rfl (gridHull_density hδ ha hlam.le s (hv i) (hYfine i) (hYgrid i) (hden i))
  have hbottom : (1 / 2 : ℝ) ^ K * (∑ i, (volume (U i)).toReal) ≤ m * a := by
    have hsum : (∑ i, (volume (U i)).toReal) ≤ n * (384 * W) := by
      calc
        _ ≤ ∑ _i : Fin n, 384 * W := Finset.sum_le_sum (fun i _ =>
          (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hUV i).2).trans_eq (ENNReal.toReal_ofReal (by positivity)))
        _ = _ := by simp
    have hcoeff : a * ((n : ℝ) * (384 * W)) ≤ m * a := by
      dsimp [W, m, C, J]
      field_simp
      have hbn : b ≤ 262144 * L := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hbn (by positivity : 0 ≤ 3456 * (n : ℝ) * a ^ 3)]
    exact (mul_le_mul (hK.trans hδa) hsum (by positivity) ha.le).trans hcoeff
  have hbound := cordoba_shading_bound U Z hUc hUconv hUpos hUb hm ha
    (by positivity : 0 ≤ J * (lam * a ^ 2 / 16)) hcount
    (fun i => shortMap_thickTube_slab ha (boxFrame z e) (y i) (w i))
    (fun i => f.toContinuousAffineEquiv.toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      (gridHull_measurable a s (Y i))) hZsub hZd K hbottom
  have hunion : volume (⋃ i, Z i) ≤ ENNReal.ofReal J * volume (gridUnion a s) := by
    rw [← hvol]
    exact measure_mono (iUnion_subset (fun i => image_mono (gridHull_subset a s (Y i))))
  have hvolreal : (volume (⋃ i, Z i)).toReal ≤ J * volume.real (gridUnion a s) := by
    have hh := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (gridUnion_volume_ne_top ha s)) hunion
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hJ.le, measureReal_def] using hh
  have hmain : (J * (lam * a ^ 2 / 16)) ^ 2 * n ≤
      ((1 + 1280 * K) * m * a) * (J * volume.real (gridUnion a s)) :=
    hbound.trans (mul_le_mul_of_nonneg_left hvolreal (by positivity))
  apply (ENNReal.ofReal_le_iff_le_toReal (gridUnion_volume_ne_top ha s)).mpr
  have hcoef : (1 + 1280 * (K : ℝ)) * (231928233984 : ℝ) ≤
      (10 : ℝ) ^ (15 : ℕ) * (K + 1 : ℕ) := by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) K]
  have hsimple : lam ^ 2 * a * b ≤
      (231928233984 : ℝ) * (1 + 1280 * K) * L * volume.real (gridUnion a s) := by
    dsimp [J, m, C] at hmain
    field_simp at hmain
    nlinarith only [hmain]
  apply (div_le_iff₀ (by positivity)).mpr
  have hh := mul_le_mul_of_nonneg_right hcoef
    (by positivity : 0 ≤ L * volume.real (gridUnion a s))
  change lam ^ 2 * a * b ≤ volume.real (gridUnion a s) * (10 ^ 15 * L * (K + 1 : ℕ))
  nlinarith only [hsimple, hh]

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
