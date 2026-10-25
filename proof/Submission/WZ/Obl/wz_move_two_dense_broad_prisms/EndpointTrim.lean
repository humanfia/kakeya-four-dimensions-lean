-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_move_two_dense_broad_prisms.EndpointTrim.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/- Adapted from session x0449 on o152 in this workspace. -/
import Submission.WZ.Obl.wz_move_two_dense_broad_prisms.Defs
import Submission.WZ.Obl.wz_normalized_projection_iteration.Expansion
import Submission.WZ.Obl.wz_clustered_cover_volume_gain.SparsePackets

/-! Removing small endpoint neighborhoods from a dense tube shading. -/

set_option autoImplicit false

namespace WangZahlLot.Obl.wz_move_two_dense_broad_prisms

open MeasureTheory Metric Set LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- Endpoint balls cost at most a constant times their radius in relative
shading mass. The budget permits simultaneous removal on every tube. -/
theorem shading_away_from_endpoints {δ R q : ℝ} (hδ : 0 < δ) (hδR : δ ≤ R)
    (hbudget : 4608 * R ≤ q) {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hv : ∀ i, ‖v i‖ = 1) (hYm : ∀ i, MeasurableSet (Y i))
    (hYT : ∀ i, Y i ⊆ T δ (x i) (v i))
    (hmass : ENNReal.ofReal (q * n * δ ^ 2) ≤ ∑ i, volume (Y i)) :
    ∃ Z : Fin n → Set Space,
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i) ∧
      (∀ i p, p ∈ Z i → R < dist p (x i) ∧ R < dist p (x i + v i)) ∧
      (1 / 2 : ℝ≥0∞) * (∑ i, volume (Y i)) ≤ ∑ i, volume (Z i) := by
  classical
  let E : Fin n → Set Space := fun i => closedBall (x i) R ∪ closedBall (x i + v i) R
  let Z : Fin n → Set Space := fun i => Y i \ E i
  have hEm : ∀ i, MeasurableSet (E i) :=
    fun _ => measurableSet_closedBall.union measurableSet_closedBall
  have hfin : ∀ i, volume (Y i) ≠ ∞ := fun i =>
    measure_ne_top_of_subset (hYT i)
      ((isBounded_closedBall.subset
        (segment_subset_closedBall_left (x i) (x i + v i))).thickening.measure_lt_top).ne
  have hR : 0 < R := hδ.trans_le hδR
  have hball : ∀ i z, volume (Y i ∩ closedBall z R) ≤ ENNReal.ofReal (1152 * R * δ ^ 2) := by
    intro i z
    exact (measure_mono (inter_subset_inter_left _ (hYT i))).trans
      (WangZahlLot.Obl.wz_normalized_projection_iteration.tube_inter_ball_volume_le
        hδ hδR (x i) (v i) z (hv i))
  have hlost : ∀ i, volume (Y i ∩ E i) ≤ ENNReal.ofReal (2304 * R * δ ^ 2) := by
    intro i
    calc volume (Y i ∩ E i)
        = volume ((Y i ∩ closedBall (x i) R) ∪ (Y i ∩ closedBall (x i + v i) R)) := by
          change volume (Y i ∩ (closedBall (x i) R ∪ closedBall (x i + v i) R)) = _
          rw [inter_union_distrib_left]
      _ ≤ volume (Y i ∩ closedBall (x i) R) + volume (Y i ∩ closedBall (x i + v i) R) :=
        measure_union_le _ _
      _ ≤ ENNReal.ofReal (1152 * R * δ ^ 2) + ENNReal.ofReal (1152 * R * δ ^ 2) :=
        add_le_add (hball i _) (hball i _)
      _ = ENNReal.ofReal (2304 * R * δ ^ 2) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
  have hsumlost : (∑ i, volume (Y i ∩ E i)) ≤ ENNReal.ofReal (2304 * R * n * δ ^ 2) := by
    calc (∑ i, volume (Y i ∩ E i)) ≤ ∑ _i : Fin n, ENNReal.ofReal (2304 * R * δ ^ 2) :=
        Finset.sum_le_sum (fun i _ => hlost i)
      _ = ENNReal.ofReal (2304 * R * n * δ ^ 2) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [show 2304 * R * n * δ ^ 2 = (n : ℝ) * (2304 * R * δ ^ 2) by ring,
          ENNReal.ofReal_mul (Nat.cast_nonneg n)]
        simp
  have hhalf : (∑ i, volume (Y i ∩ E i)) ≤ (1 / 2 : ℝ≥0∞) * ∑ i, volume (Y i) := by
    refine hsumlost.trans ?_
    calc ENNReal.ofReal (2304 * R * n * δ ^ 2)
        ≤ ENNReal.ofReal ((1 / 2) * (q * n * δ ^ 2)) := by
          apply ENNReal.ofReal_le_ofReal
          have hm := mul_le_mul_of_nonneg_right hbudget
            (show 0 ≤ (n : ℝ) * δ ^ 2 by positivity)
          nlinarith
      _ = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal (q * n * δ ^ 2) := by
        rw [ENNReal.ofReal_mul (by norm_num)]
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        norm_num
      _ ≤ _ := mul_le_mul_right hmass _
  refine ⟨Z, fun i => ⟨(hYm i).diff (hEm i), sdiff_subset⟩, ?_, ?_⟩
  · intro i p hp
    exact ⟨lt_of_not_ge (fun h => hp.2 (Or.inl h)),
      lt_of_not_ge (fun h => hp.2 (Or.inr h))⟩
  · apply WangZahlLot.Obl.wz_clustered_cover_volume_gain.half_mass_after_loss
      (ENNReal.sum_ne_top.mpr (fun i _ => hfin i)) _ hhalf
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ =>
      (measure_sdiff_add_inter (Y i) (hEm i)).ge)

end WangZahlLot.Obl.wz_move_two_dense_broad_prisms
