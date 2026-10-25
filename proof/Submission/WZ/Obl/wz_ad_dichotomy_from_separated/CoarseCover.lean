-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_ad_dichotomy_from_separated.CoarseCover.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_ad_dichotomy_from_separated.Counting

namespace WangZahlLot.Obl.wz_ad_dichotomy_from_separated

open Set Metric MeasureTheory
open scoped BigOperators ENNReal NNReal

/-- The elementary disjoint-ball packing bound in the plane, with both radii
left explicit for later coarse-scale localization. -/
theorem separated_card_mul_radius_sq_le {δ R : ℝ} (hδ : 0 < δ) (hR : 0 ≤ R)
    (S : Finset Plane) (c : Plane) (hball : ∀ x ∈ S, dist x c ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) :
    (S.card : ℝ) * δ ^ 2 ≤ (2 * R + δ) ^ 2 := by
  classical
  let μ : Measure Plane := Measure.addHaar
  have hh : 0 < δ / 2 := half_pos hδ
  have hbig : 0 < R + δ / 2 := add_pos_of_nonneg_of_pos hR hh
  have hd : Set.Pairwise (S : Set Plane)
      (fun x y => Disjoint (Metric.ball x (δ / 2)) (Metric.ball y (δ / 2))) := by
    intro x hx y hy hxy
    apply Metric.ball_disjoint_ball
    linarith [hsep x hx y hy hxy]
  have hsub : (⋃ x ∈ S, Metric.ball x (δ / 2)) ⊆ Metric.ball c (R + δ / 2) := by
    refine Set.iUnion₂_subset fun x hx => ?_
    apply Metric.ball_subset_ball'
    linarith [hball x hx]
  have hm : (S.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ 2) * μ (Metric.ball 0 1) ≤
      ENNReal.ofReal ((R + δ / 2) ^ 2) * μ (Metric.ball 0 1) := by
    calc
      (S.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ 2) * μ (Metric.ball 0 1) =
          μ (⋃ x ∈ S, Metric.ball x (δ / 2)) := by
        rw [measure_biUnion_finset hd (fun _ _ => measurableSet_ball)]
        simp only [μ.addHaar_ball_of_pos _ hh, Plane, finrank_euclideanSpace_fin,
          Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (Metric.ball c (R + δ / 2)) := measure_mono hsub
      _ = ENNReal.ofReal ((R + δ / 2) ^ 2) * μ (Metric.ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ hbig, Plane, finrank_euclideanSpace_fin]
  have hm' : (S.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ 2) ≤
      ENNReal.ofReal ((R + δ / 2) ^ 2) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne'
      measure_ball_lt_top.ne).mp hm
  have hr := ENNReal.toReal_le_of_le_ofReal (sq_nonneg (R + δ / 2)) hm'
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (sq_nonneg (δ / 2))] at hr
  nlinarith

theorem InUnitSquare.separated_card_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (S : Finset Plane) (hS : InUnitSquare (↑S : Set Plane))
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) :
    (S.card : ℝ) ≤ 25 / δ ^ 2 := by
  have h := separated_card_mul_radius_sq_le hδ (by norm_num : (0 : ℝ) ≤ 2) S 0
    (fun x hx => by simpa using hS.norm_le_two hx) hsep
  apply (le_div_iff₀ (sq_pos_of_pos hδ)).mpr
  nlinarith

/-- Every subset of the unit square has an internal radius-`δ` cover with at
most `25 / δ^2` centers. -/
theorem InUnitSquare.exists_coarse_cover {F : Set Plane} (hF : InUnitSquare F)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ (m : ℕ) (c : Fin m → Plane), (∀ i, c i ∈ F) ∧
      Covers δ F c ∧ (m : ℝ) ≤ 25 / δ ^ 2 := by
  classical
  obtain ⟨m, c, hcF, hsep, hc⟩ := exists_separated_cover
    (hF.isBounded.isCompact_closure.totallyBounded.subset subset_closure) hδ
  have hinj : Function.Injective c := by
    intro i j hij
    by_contra hne
    have hd := hsep i j hne
    rw [hij, dist_self] at hd
    exact (not_lt_of_ge hδ.le) hd
  let S := Finset.univ.image c
  have hS : InUnitSquare (↑S : Set Plane) := by
    rintro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact hF _ (hcF i)
  have hSsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y := by
    rintro x hx y hy hxy
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact (hsep i j (fun hij => hxy (congrArg c hij))).le
  have hcard := hS.separated_card_le hδ hδ1 S hSsep
  have hSm : S.card = m := by simp only [S, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin]
  exact ⟨m, c, hcF, hc, by simpa only [hSm] using hcard⟩

end WangZahlLot.Obl.wz_ad_dichotomy_from_separated
