-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_two_scale_flat_box_estimate.SlabComposition.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_two_scale_flat_box_estimate.Interfaces
import Submission.WZ.Obl.wz_flat_factored_improvement.Cordoba
import Submission.WZ.Obl.wz_flat_factored_improvement.BodyCounts

namespace WangZahlLot.Obl.wz_two_scale_flat_box_estimate

open MeasureTheory Set Metric
open WangZahlLot.Obl.wz_regular_transverse_affine_cells (slab)
open WangZahlLot.Obl.wz_flat_factored_improvement
  (ConvexVolumeCount BodySlabCount convex_slab_overlap)

lemma count_fibers {n N : ℕ} (f : Fin n → Fin N) (P : Fin n → Prop) :
    ∑ k, Set.ncard {i | f i = k ∧ P i} = Set.ncard {i | P i} := by
  classical
  simpa [Set.ncard_eq_toFinset_card', Finset.filter_filter, and_comm] using
    Finset.sum_card_fiberwise_eq_card_filter (Finset.univ.filter P) Finset.univ f

/-- Summing a local slab estimate through a convex-counted family costs only a
logarithm and an explicit bottom-scale term. -/
theorem slab_count_composition {n N : ℕ} (U : Fin n → Set Space) (D : Fin N → Set Space)
    (f : Fin n → Fin N) {w L F C m : ℝ}
    (hw : 0 < w) (hL : 0 ≤ L) (hF : 0 ≤ F) (hC : 0 ≤ C) (hm : 0 ≤ m)
    (hDc : ∀ k, IsCompact (D k)) (hDconv : ∀ k, Convex ℝ (D k))
    (hDb : ∀ k, D k ⊆ closedBall (0 : Space) 1)
    (hDlo : ∀ k, ENNReal.ofReal w ≤ volume (D k))
    (hDhi : ∀ k, volume (D k) ≤ ENNReal.ofReal (C * w))
    (hcount : ConvexVolumeCount D m)
    {u : Space} (hu : ‖u‖ = 1) (s : ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hlocal : ∀ k,
      ENNReal.ofReal (Set.ncard {i | f i = k ∧ U i ⊆ slab (innerSL ℝ u) s r} : ℝ) *
          volume (D k) ≤ ENNReal.ofReal (L * F) * volume (D k ∩ slab (innerSL ℝ u) s r))
    (K : ℕ) :
    (Set.ncard {i | U i ⊆ slab (innerSL ℝ u) s r} : ℝ) * w ≤
      L * F * ((1 / 2 : ℝ) ^ K * (N : ℝ) * (C * w) + 1280 * K * m * r) := by
  have hDpos (k : Fin N) : volume (D k) ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hw) (hDlo k)).ne'
  have hlocalReal (k : Fin N) :
      (Set.ncard {i | f i = k ∧ U i ⊆ slab (innerSL ℝ u) s r} : ℝ) * w ≤
        L * F * (volume (D k ∩ slab (innerSL ℝ u) s r)).toReal := by
    have hh := ENNReal.toReal_mono
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top_of_subset inter_subset_left (hDc k).measure_ne_top)) (hlocal k)
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Nat.cast_nonneg _),
      ENNReal.toReal_ofReal (mul_nonneg hL hF)] at hh
    have hlo := (ENNReal.ofReal_le_iff_le_toReal (hDc k).measure_ne_top).mp (hDlo k)
    exact (mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg _)).trans hh
  have hsum := convex_slab_overlap D hDc hDconv hDpos hDb hm hcount hu s hr K
  have htotal : ∑ k, (volume (D k)).toReal ≤ (N : ℝ) * (C * w) := by
    calc
      _ ≤ ∑ _k : Fin N, C * w := Finset.sum_le_sum fun k _ => by
        simpa only [ENNReal.toReal_ofReal (mul_nonneg hC hw.le)] using
          ENNReal.toReal_mono ENNReal.ofReal_ne_top (hDhi k)
      _ = _ := by simp
  have hpartition :
      (Set.ncard {i | U i ⊆ slab (innerSL ℝ u) s r} : ℝ) =
        ∑ k, (Set.ncard {i | f i = k ∧ U i ⊆ slab (innerSL ℝ u) s r} : ℝ) := by
    exact_mod_cast (count_fibers f (fun i => U i ⊆ slab (innerSL ℝ u) s r)).symm
  calc
    _ = ∑ k, (Set.ncard {i | f i = k ∧ U i ⊆ slab (innerSL ℝ u) s r} : ℝ) * w := by
      rw [hpartition, Finset.sum_mul]
    _ ≤ ∑ k, L * F * (volume (D k ∩ slab (innerSL ℝ u) s r)).toReal :=
      Finset.sum_le_sum fun k _ => hlocalReal k
    _ = L * F * ∑ k, (volume (D k ∩ slab (innerSL ℝ u) s r)).toReal :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ L * F * ((1 / 2 : ℝ) ^ K * (∑ k, (volume (D k)).toReal) + 1280 * K * m * r) :=
      mul_le_mul_of_nonneg_left hsum (mul_nonneg hL hF)
    _ ≤ L * F * ((1 / 2 : ℝ) ^ K * ((N : ℝ) * (C * w)) + 1280 * K * m * r) := by
      gcongr
    _ = _ := by ring

lemma slab_radius_of_ball {u x : Space} {d s r : ℝ}
    (hu : ‖u‖ = 1) (hd : 0 < d)
    (h : ball x d ⊆ slab (innerSL ℝ u) s r) : d / 2 ≤ r := by
  have hp : x + (d / 2) • u ∈ ball x d := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hu, mul_one,
      abs_of_pos (by positivity : 0 < d / 2)]
    linarith
  have hq : x + (-(d / 2)) • u ∈ ball x d := by
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hu, mul_one,
      abs_neg, abs_of_pos (by positivity : 0 < d / 2)]
    linarith
  have hp' := h hp
  have hq' := h hq
  have hself : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  change |inner ℝ u (x + (d / 2) • u) - s| ≤ r at hp'
  change |inner ℝ u (x + (-(d / 2)) • u) - s| ≤ r at hq'
  rw [inner_add_right, inner_smul_right, hself, mul_one] at hp' hq'
  have hp'' := (abs_le.mp hp').2
  have hq'' := (abs_le.mp hq').1
  linarith

/-- A polynomial interior scale absorbs the dyadic bottom error. Balance then
turns the composition into the slab hypothesis used by the accepted body estimate. -/
theorem bodySlabCount_of_two_scale {n N : ℕ} (U : Fin n → Set Space)
    (x : Fin n → Space) (D : Fin N → Set Space) (f : Fin n → Fin N)
    {d w L F C m M Q : ℝ}
    (hd : 0 < d) (hw : 0 < w) (hL : 0 ≤ L) (hF : 0 ≤ F)
    (hC : 0 ≤ C) (hm : 0 ≤ m) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (hball : ∀ i, ball (x i) d ⊆ U i)
    (hDc : ∀ k, IsCompact (D k)) (hDconv : ∀ k, Convex ℝ (D k))
    (hDb : ∀ k, D k ⊆ closedBall (0 : Space) 1)
    (hDlo : ∀ k, ENNReal.ofReal w ≤ volume (D k))
    (hDhi : ∀ k, volume (D k) ≤ ENNReal.ofReal (C * w))
    (hcount : ConvexVolumeCount D m) (hcoef : m ≤ M * N * w)
    (hbalance : F * N ≤ Q * n)
    (hlocal : ∀ (u : Space) (s r : ℝ), ‖u‖ = 1 → 0 < r → ∀ k,
      ENNReal.ofReal (Set.ncard {i | f i = k ∧ U i ⊆ slab (innerSL ℝ u) s r} : ℝ) *
          volume (D k) ≤ ENNReal.ofReal (L * F) * volume (D k ∩ slab (innerSL ℝ u) s r))
    (K : ℕ) (hK : (1 / 2 : ℝ) ^ K ≤ d / 2) :
    BodySlabCount U (L * Q * (C + 1280 * K * M)) := by
  intro u s r hu hr
  change ENNReal.ofReal (Set.ncard {i | U i ⊆ slab (innerSL ℝ u) s r} : ℝ) ≤ _
  by_cases hz : Set.ncard {i | U i ⊆ slab (innerSL ℝ u) s r} = 0
  · simp [hz]
  have hnonempty : {i | U i ⊆ slab (innerSL ℝ u) s r}.Nonempty :=
    (Set.ncard_pos (Set.toFinite _)).mp (Nat.pos_of_ne_zero hz)
  obtain ⟨i, hi⟩ := hnonempty
  have hbottom : (1 / 2 : ℝ) ^ K ≤ r :=
    hK.trans (slab_radius_of_ball hu hd ((hball i).trans hi))
  have hh := slab_count_composition U D f hw hL hF hC hm hDc hDconv hDb
    hDlo hDhi hcount hu s hr.le (hlocal u s r hu hr) K
  apply ENNReal.ofReal_le_ofReal
  apply (mul_le_mul_iff_right₀ hw).mp
  calc
    w * (Set.ncard {i | U i ⊆ slab (innerSL ℝ u) s r} : ℝ) =
        (Set.ncard {i | U i ⊆ slab (innerSL ℝ u) s r} : ℝ) * w := mul_comm _ _
    _ ≤ L * F * ((1 / 2 : ℝ) ^ K * (N : ℝ) * (C * w) + 1280 * K * m * r) := hh
    _ ≤ L * F * (r * (N : ℝ) * (C * w) + 1280 * K * (M * N * w) * r) := by
      gcongr
    _ = L * (F * N) * (C + 1280 * K * M) * r * w := by ring
    _ ≤ L * (Q * n) * (C + 1280 * K * M) * r * w := by gcongr
    _ = _ := by ring

end WangZahlLot.Obl.wz_two_scale_flat_box_estimate
