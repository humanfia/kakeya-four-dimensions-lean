-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_initialization.EndpointTrim.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_broad_grains_initialization.PointwiseRefinement

namespace WangZahlLot.Obl.wz_broad_grains_initialization

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open wz_clustered_cover_volume_gain (bodyCount)

/-- A simple volume budget for the endpoint balls removed from a tube. -/
lemma endpoint_ball_volume {r : ℝ} (hr : 0 ≤ r) (x : Space) :
    volume (closedBall x r) ≤ ENNReal.ofReal (8 * r ^ 3) := by
  rw [EuclideanSpace.volume_closedBall_fin_three, ← ENNReal.ofReal_pow hr,
    ← ENNReal.ofReal_mul (pow_nonneg hr _)]
  apply ENNReal.ofReal_le_ofReal
  have hpi : Real.pi * 4 / 3 ≤ 8 := by linarith [Real.pi_lt_four]
  nlinarith [mul_le_mul_of_nonneg_right hpi (pow_nonneg hr 3)]

/-- Endpoint trimming with a pointwise incidence guarantee. Its mass cost is
cubic in the grain length, hence negligible for grains of size a fixed
multiple of the fine radius. -/
theorem trim_tube_endpoints {n : ℕ} (x v : Fin n → Space) (Y : Fin n → Set Space)
    (hY : ∀ i, MeasurableSet (Y i)) {c : ℝ} (hc : 0 ≤ c) :
    ∃ Z : Fin n → Set Space,
      (∀ i, MeasurableSet (Z i) ∧ Z i ⊆ Y i ∧ ∀ p ∈ Z i,
        100 * c ≤ dist p (x i) ∧ 100 * c ≤ dist p (x i + v i)) ∧
      (∑ i, volume (Y i)) ≤ (∑ i, volume (Z i)) +
        ENNReal.ofReal (32000000 * n * c ^ 3) ∧
      ∀ p ∈ ⋃ i, Z i, bodyCount Y p ≤ 2 * bodyCount Z p := by
  classical
  let B : Fin n → Set Space := fun i => closedBall (x i) (100 * c) ∪
    closedBall (x i + v i) (100 * c)
  let U : Fin n → Set Space := fun i => Y i \ B i
  have hB (i : Fin n) : MeasurableSet (B i) :=
    measurableSet_closedBall.union measurableSet_closedBall
  have hU (i : Fin n) : MeasurableSet (U i) := (hY i).diff (hB i)
  obtain ⟨G, hG, hmass, hcount⟩ := pointwise_half_refinement Y U hY hU (fun _ => sdiff_subset)
  refine ⟨fun i => U i ∩ G, ?_, ?_, hcount⟩
  · intro i
    refine ⟨(hU i).inter hG, inter_subset_left.trans sdiff_subset, ?_⟩
    intro p hp
    have hnone : p ∉ B i := hp.1.2
    have hl : p ∉ closedBall (x i) (100 * c) := fun h => hnone (Or.inl h)
    have hr : p ∉ closedBall (x i + v i) (100 * c) := fun h => hnone (Or.inr h)
    exact ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hr).le⟩
  · apply hmass.trans
    refine add_le_add le_rfl ?_
    have hvol (i : Fin n) : volume (Y i \ U i) ≤ ENNReal.ofReal (16000000 * c ^ 3) := by
      have hsub : Y i \ U i ⊆ B i := by
        intro p hp
        by_contra h
        exact hp.2 ⟨hp.1, h⟩
      calc
        _ ≤ volume (B i) := measure_mono hsub
        _ ≤ volume (closedBall (x i) (100 * c)) +
            volume (closedBall (x i + v i) (100 * c)) := measure_union_le _ _
        _ ≤ ENNReal.ofReal (8 * (100 * c) ^ 3) + ENNReal.ofReal (8 * (100 * c) ^ 3) :=
          add_le_add (endpoint_ball_volume (by positivity) _) (endpoint_ball_volume (by positivity) _)
        _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    calc
      2 * ∑ i, volume (Y i \ U i) ≤ 2 * ∑ _i : Fin n, ENNReal.ofReal (16000000 * c ^ 3) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hvol i)
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast n, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end WangZahlLot.Obl.wz_broad_grains_initialization
