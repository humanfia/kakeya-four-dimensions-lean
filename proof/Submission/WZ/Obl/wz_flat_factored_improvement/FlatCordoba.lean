-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_flat_factored_improvement.FlatCordoba.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_flat_factored_improvement.GridHull

namespace WangZahlLot.Obl.wz_flat_factored_improvement

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (closedTube closedTube_convex closedTube_volume_bounds tube_subset_closedTube)
open WangZahlLot.Obl.wz_nonflat_factored_improvement (gridUnion gridUnion_volume_ne_top)

set_option maxHeartbeats 800000 in
/-- The union of short-scale cubes supporting dense fine shadings occupies a
definite fraction of its containing prism. -/
theorem flat_cordoba_density {δ a b lam L : ℝ} (hδ : 0 < δ) (hδa : δ ≤ a)
    (hab : a ≤ b) (hb2 : b ≤ 2) (haSmall : a ≤ 1 / 100) (hlam : 0 < lam) (hL : 1 ≤ L)
    (e : AffineIsometryEquiv ℝ Space Space) {n : ℕ} (hn : 0 < n)
    (x v : Fin n → Space) (Y : Fin n → Set Space) (s : Finset (Fin 3 → ℤ))
    (hv : ∀ i, ‖v i‖ = 1) (hT : ∀ i, Tube δ (x i) (v i) ⊆ e '' StandardPrism a b)
    (hYT : ∀ i, Y i ⊆ Tube δ (x i) (v i)) (hYgrid : ∀ i, Y i ⊆ gridUnion a s)
    (hden : ∀ i, ENNReal.ofReal (lam * δ ^ 2) ≤ volume (Y i))
    (hraw : ∀ Q : Set Space, Convex ℝ Q →
      ENNReal.ofReal (Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} : ℝ) ≤
        ENNReal.ofReal (L * n / (a * b)) * volume Q)
    (K : ℕ) (hK : (1 / 2 : ℝ) ^ K ≤ δ) :
    ENNReal.ofReal (lam ^ 2 * a * b / ((10 : ℝ) ^ (15 : ℕ) * L * (K + 1 : ℕ))) ≤
      volume (gridUnion a s) := by
  have ha : 0 < a := hδ.trans_le hδa
  have hb : 0 < b := ha.trans_le hab
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hL' : 0 < L := zero_lt_one.trans_le hL
  let f := shortMap e a ha
  let J := 1 / (262144 * a)
  let w := J * (3 * a) ^ 2
  let c := L * n / (a * b)
  let m := 384 * (c * (3 * a) ^ 2)
  let U := fun i => f '' closedTube (3 * a) (x i) (v i)
  let Z := fun i => f '' gridHull a s (Y i)
  have hJ : 0 < J := by dsimp [J]; positivity
  have hw : 0 < w := by dsimp [w]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hm : 0 < m := by dsimp [m]; positivity
  have h3a : 0 < 3 * a := by positivity
  have h3a1 : 3 * a ≤ 1 := by linarith
  have hvol : ∀ Q, volume (f '' Q) = ENNReal.ofReal J * volume Q := shortMap_volume e ha
  have hUc : ∀ i, IsCompact (U i) := fun i =>
    (closedTube_isCompact _ _ _).image f.toContinuousAffineEquiv.continuous
  have hUconv : ∀ i, Convex ℝ (U i) := fun i =>
    (closedTube_convex _ _ _).affine_image f.toAffineMap
  have hUb : ∀ i, U i ⊆ closedBall (0 : Space) 1 := fun i =>
    shortMap_thickTube_bounded hδ ha hab hb2 e (hT i)
  have hUV (i : Fin n) : ENNReal.ofReal w ≤ volume (U i) ∧
      volume (U i) ≤ ENNReal.ofReal (384 * w) := by
    obtain ⟨hl, hu⟩ := closedTube_volume_bounds h3a h3a1 (x i) (v i) (hv i)
    change ENNReal.ofReal w ≤ volume (f '' _) ∧ _
    rw [hvol]
    constructor
    · rw [show w = J * (3 * a) ^ 2 from rfl, ENNReal.ofReal_mul hJ.le]
      exact mul_le_mul' le_rfl hl
    · calc
        _ ≤ ENNReal.ofReal J * ENNReal.ofReal (384 * (3 * a) ^ 2) := mul_le_mul' le_rfl hu
        _ = _ := by rw [← ENNReal.ofReal_mul hJ.le]; congr 1; dsimp [w]; ring
  have hUpos : ∀ i, volume (U i) ≠ 0 := fun i => ne_of_gt ((ENNReal.ofReal_pos.mpr hw).trans_le (hUV i).1)
  have hraw3 : ∀ Q : Set Space, Convex ℝ Q →
      ENNReal.ofReal (Set.ncard {i | Tube (3 * a) (x i) (v i) ⊆ Q} : ℝ) ≤ ENNReal.ofReal c * volume Q := by
    intro Q hQ
    have hh : Set.ncard {i | Tube (3 * a) (x i) (v i) ⊆ Q} ≤
        Set.ncard {i | Tube δ (x i) (v i) ⊆ Q} :=
      ncard_mono (fun i hi => (thickening_mono (by linarith : δ ≤ 3 * a) _).trans hi)
    exact (ENNReal.ofReal_le_ofReal (Nat.cast_le.mpr hh)).trans (hraw Q hQ)
  have hcount : ConvexVolumeCount U m :=
    ((closedTube_convex_count hc.le x v hraw3).affine_image (sq_nonneg _) hJ f hvol).volume_weighted
      (by norm_num : (0 : ℝ) ≤ 384) (by positivity) (fun i => (hUV i).2)
  have hZsub : ∀ i, Z i ⊆ U i := fun i => image_mono
    ((gridHull_subset_thickTube ha hδa s (hYT i)).trans (tube_subset_closedTube _ _ _))
  have hZd : ∀ i, J * (lam * a ^ 2 / 16) ≤ (volume (Z i)).toReal := by
    intro i
    apply (ENNReal.ofReal_le_iff_le_toReal
      (ne_top_of_le_ne_top (hUc i).measure_ne_top (measure_mono (hZsub i)))).mp
    rw [ENNReal.ofReal_mul hJ.le]
    change _ ≤ volume (f '' _)
    rw [hvol]
    exact mul_le_mul' le_rfl (gridHull_density hδ ha hlam.le s (hv i) (hYT i) (hYgrid i) (hden i))
  have hbottom : (1 / 2 : ℝ) ^ K * (∑ i, (volume (U i)).toReal) ≤ m * a := by
    have hsum : (∑ i, (volume (U i)).toReal) ≤ n * (384 * w) := by
      calc
        _ ≤ ∑ _i : Fin n, 384 * w := Finset.sum_le_sum (fun i _ =>
          (ENNReal.toReal_mono ENNReal.ofReal_ne_top (hUV i).2).trans_eq (ENNReal.toReal_ofReal (by positivity)))
        _ = _ := by simp
    have hJa : J * a = 1 / 262144 := by dsimp [J]; field_simp
    have hcoeff : a * ((n : ℝ) * (384 * w)) ≤ m * a := by
      dsimp [w, m, c, J]
      field_simp
      have hbn : b ≤ 262144 * L := by linarith
      nlinarith [mul_le_mul_of_nonneg_left hbn (by positivity : 0 ≤ 3456 * (n : ℝ) * a ^ 3)]
    exact (mul_le_mul (hK.trans hδa) hsum (by positivity) ha.le).trans hcoeff
  have hbound := cordoba_shading_bound U Z hUc hUconv hUpos hUb hm ha
    (by positivity : 0 ≤ J * (lam * a ^ 2 / 16)) hcount
    (fun i => shortMap_thickTube_slab ha e (x i) (v i))
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
    dsimp [J, m, c] at hmain
    field_simp at hmain
    nlinarith only [hmain]
  apply (div_le_iff₀ (by positivity)).mpr
  change lam ^ 2 * a * b ≤ volume.real (gridUnion a s) * ((10 : ℝ) ^ (15 : ℕ) * L * (K + 1 : ℕ))
  have hh := mul_le_mul_of_nonneg_right hcoef
    (by positivity : 0 ≤ L * volume.real (gridUnion a s))
  nlinarith only [hsimple, hh]

end WangZahlLot.Obl.wz_flat_factored_improvement
