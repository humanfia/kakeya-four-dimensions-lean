-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.Packing.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
open Set Metric MeasureTheory
open scoped ENNReal NNReal

namespace WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate

/-- A bounded set admits a finite separated net, with its centres in the set. -/
theorem exists_finset_separated_cover {X : Type*} [MetricSpace X] {A : Set X}
    (hA : TotallyBounded A) {r : ℝ} (hr : 0 < r) :
    ∃ F : Finset X, (↑F : Set X) ⊆ A ∧
      (∀ x ∈ F, ∀ y ∈ F, x ≠ y → r < dist x y) ∧
      A ⊆ ⋃ x ∈ F, closedBall x r := by
  classical
  let ε : ℝ≥0 := ⟨r / 2, by positivity⟩
  obtain ⟨N, hNA, hNfin, hN⟩ := exists_finite_isCover_of_totallyBounded
    (ε := ε) (ne_of_gt (show 0 < ε from half_pos hr)) hA
  have htw : ((2 * ε : ℝ≥0) : ℝ) = r := by
    change 2 * (r / 2) = r
    ring
  have hpack : packingNumber (2 * ε) A ≠ ⊤ := by
    apply ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hNfin)
    exact (packingNumber_two_mul_le_externalCoveringNumber ε A).trans
      hN.externalCoveringNumber_le_encard
  let M := maximalSeparatedSet (2 * ε) A
  have hMfin : M.Finite := Set.encard_ne_top_iff.mp
    ((encard_maximalSeparatedSet hpack).trans_ne hpack)
  refine ⟨hMfin.toFinset, ?_, ?_, ?_⟩
  · simpa [M] using (maximalSeparatedSet_subset (ε := 2 * ε) (A := A))
  · intro x hx y hy hxy
    have hs := isSeparated_maximalSeparatedSet
      (ε := 2 * ε) (A := A) (hMfin.mem_toFinset.mp hx) (hMfin.mem_toFinset.mp hy) hxy
    change (↑(2 * ε : ℝ≥0) : ℝ≥0∞) < edist x y at hs
    rw [edist_nndist, ENNReal.coe_lt_coe] at hs
    have hs' : ((2 * ε : ℝ≥0) : ℝ) < dist x y := by
      exact_mod_cast hs
    rwa [htw] at hs'
  · have hc := (isCover_maximalSeparatedSet hpack).subset_iUnion_closedBall
    simpa only [Set.Finite.mem_toFinset, M, htw] using hc


/-- The area of a set is bounded by the size of any finite radius-`r` net. -/
theorem plane_volume_le_card_of_cover {A : Set (EuclideanSpace ℝ (Fin 2))}
    (F : Finset (EuclideanSpace ℝ (Fin 2))) {r : ℝ} (hr : 0 ≤ r)
    (hF : A ⊆ ⋃ x ∈ F, closedBall x r) :
    volume A ≤ ENNReal.ofReal ((F.card : ℝ) * 4 * r ^ 2) := by
  calc
    volume A ≤ ∑ x ∈ F, volume (closedBall x r) :=
      (measure_mono hF).trans (measure_biUnion_finset_le _ _)
    _ = ENNReal.ofReal ((F.card : ℝ) * (r ^ 2 * Real.pi)) := by
      simp only [EuclideanSpace.volume_closedBall_fin_two]
      rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (sq_nonneg r)]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      simp
    _ ≤ ENNReal.ofReal ((F.card : ℝ) * 4 * r ^ 2) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        (F.card : ℝ) * (r ^ 2 * Real.pi) ≤ (F.card : ℝ) * (r ^ 2 * 4) := by
          gcongr; exact Real.pi_lt_four.le
        _ = _ := by ring

/-- A segment parametrized by a unit vector is an isometry. -/
theorem dist_segment_param (x v : LeanEval.Analysis.WangZahlKakeya.Space)
    (hv : ‖v‖ = 1) (s t : ℝ) :
    dist (x + s • v) (x + t • v) = dist s t := by
  rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, hv, mul_one, dist_eq_norm]

/-- A thickened part of a unit segment has volume at least a constant times its
one-dimensional outer measure times the square of the thickness. -/
theorem segment_shading_volume_lower
    (x v : LeanEval.Analysis.WangZahlKakeya.Space) (hv : ‖v‖ = 1)
    {T : Set ℝ} (hT : T ⊆ Icc 0 1) {r a : ℝ} (hr : 0 < r)
    (ha : ENNReal.ofReal a ≤ volume T) :
    ENNReal.ofReal (a * r ^ 2 / 4) ≤
      volume (thickening (r / 2) ((fun t : ℝ => x + t • v) '' T)) := by
  classical
  obtain ⟨F, hFT, hsep, hcover⟩ :=
    exists_finset_separated_cover ((totallyBounded_Icc 0 1).subset hT) hr
  have hlength : a ≤ (F.card : ℝ) * (2 * r) := by
    apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    calc
      ENNReal.ofReal a ≤ volume T := ha
      _ ≤ ∑ t ∈ F, volume (closedBall t r) :=
        (measure_mono hcover).trans (measure_biUnion_finset_le _ _)
      _ = ENNReal.ofReal ((F.card : ℝ) * (2 * r)) := by
        simp only [Real.volume_closedBall]
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        simp
  have hdisj : (↑F : Set ℝ).PairwiseDisjoint
      (fun t => ball (x + t • v) (r / 2)) := by
    intro s hs t ht hst
    apply ball_disjoint_ball
    rw [dist_segment_param x v hv]
    have := hsep s hs t ht hst
    linarith
  have hsub : (⋃ t ∈ F, ball (x + t • v) (r / 2)) ⊆
      thickening (r / 2) ((fun t : ℝ => x + t • v) '' T) := by
    intro y hy
    obtain ⟨t, ht⟩ := mem_iUnion.mp hy
    obtain ⟨htF, hyt⟩ := mem_iUnion.mp ht
    apply mem_thickening_iff.mpr
    exact ⟨x + t • v, ⟨t, hFT htF, rfl⟩, hyt⟩
  calc
    ENNReal.ofReal (a * r ^ 2 / 4) ≤
        ENNReal.ofReal ((F.card : ℝ) * ((r / 2) ^ 3 * (Real.pi * 4 / 3))) := by
      apply ENNReal.ofReal_le_ofReal
      calc
        a * r ^ 2 / 4 ≤ ((F.card : ℝ) * (2 * r)) * r ^ 2 / 4 := by gcongr
        _ = (F.card : ℝ) * ((r / 2) ^ 3 * 4) := by ring
        _ ≤ _ := by
          gcongr
          linarith [Real.pi_gt_three]
    _ = volume (⋃ t ∈ F, ball (x + t • v) (r / 2)) := by
      rw [measure_biUnion_finset hdisj (fun _ _ => isOpen_ball.measurableSet)]
      simp only [EuclideanSpace.volume_ball_fin_three]
      rw [← ENNReal.ofReal_pow (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
      simp
    _ ≤ _ := measure_mono hsub

end WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate
