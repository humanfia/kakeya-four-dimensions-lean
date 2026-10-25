-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_extremal_lipschitz_grains.GrainFan.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.RobustTransversality
import Submission.WZ.Obl.wz_extremal_lipschitz_grains.TwoScaleUse
import Submission.WZ.Obl.wz_direction_density_transfer.Geometry
import Submission.WZ.Obl.kakeya_three_le_dimH_of_tube_estimate.Packing

namespace WangZahlLot.Obl.wz_extremal_lipschitz_grains

open MeasureTheory Set Metric
open scoped ENNReal Pointwise

/-- Two points farther than `D ≥ 4 r` apart lying in two `r`-tubes force the tube directions to
agree up to sign within `16 r / D`. -/
theorem dir_close_of_two_points {r D : ℝ} {z w z' w' p q : Space} (hw : ‖w‖ = 1)
    (hw' : ‖w'‖ = 1) (hp : p ∈ tube r z w) (hq : q ∈ tube r z w) (hp' : p ∈ tube r z' w')
    (hq' : q ∈ tube r z' w') (hD : D < dist p q) (hrD : 4 * r ≤ D) :
    min ‖w - w'‖ ‖w + w'‖ ≤ 16 * r / D := by
  obtain ⟨t1, -, ht1⟩ := tube_param hp
  obtain ⟨t2, -, ht2⟩ := tube_param hq
  obtain ⟨s1, -, hs1⟩ := tube_param hp'
  obtain ⟨s2, -, hs2⟩ := tube_param hq'
  have hr : 0 < r := by
    have := norm_nonneg (p - (z + t1 • w)); linarith
  have hD0 : 0 < D := by linarith
  set a := t1 - t2 with ha
  set b := s1 - s2 with hb
  set d := p - q with hd
  have hda : ‖d - a • w‖ < 2 * r := by
    have e : d - a • w = (p - (z + t1 • w)) - (q - (z + t2 • w)) := by
      rw [hd, ha, sub_smul]; abel
    rw [e]; exact (norm_sub_le _ _).trans_lt (by linarith)
  have hdb : ‖d - b • w'‖ < 2 * r := by
    have e : d - b • w' = (p - (z' + s1 • w')) - (q - (z' + s2 • w')) := by
      rw [hd, hb, sub_smul]; abel
    rw [e]; exact (norm_sub_le _ _).trans_lt (by linarith)
  have hdn : D < ‖d‖ := by rw [hd, ← dist_eq_norm]; exact hD
  have han : D / 2 < |a| := by
    have h1 : ‖d‖ ≤ ‖a • w‖ + ‖d - a • w‖ := by
      calc ‖d‖ = ‖a • w + (d - a • w)‖ := by abel_nf
        _ ≤ _ := norm_add_le _ _
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs] at h1
    linarith
  have ha0 : 0 < |a| := by linarith
  have hab : ‖a • w - b • w'‖ < 4 * r := by
    have e : a • w - b • w' = (d - b • w') - (d - a • w) := by abel
    rw [e]; exact (norm_sub_le _ _).trans_lt (by linarith)
  set c := b / a with hc
  have hane : a ≠ 0 := abs_pos.mp ha0
  have hwc : ‖w - c • w'‖ < 4 * r / |a| := by
    have e : w - c • w' = a⁻¹ • (a • w - b • w') := by
      rw [hc, smul_sub, smul_smul, smul_smul, inv_mul_cancel₀ hane, one_smul, div_eq_inv_mul]
    rw [e, norm_smul, norm_inv, Real.norm_eq_abs, lt_div_iff₀ ha0]
    calc |a|⁻¹ * ‖a • w - b • w'‖ * |a| = ‖a • w - b • w'‖ := by field_simp
      _ < 4 * r := hab
  have hcabs : |(|c| - 1)| < 4 * r / |a| := by
    have h1 : |‖c • w'‖ - ‖w‖| ≤ ‖c • w' - w‖ := abs_norm_sub_norm_le _ _
    rw [norm_smul, hw', mul_one, hw, Real.norm_eq_abs, norm_sub_rev] at h1
    linarith
  have hfinal : min ‖w - w'‖ ‖w + w'‖ < 8 * r / |a| := by
    rcases le_or_gt 0 c with hc0 | hc0
    · apply (min_le_left _ _).trans_lt
      have h1 : ‖w - w'‖ ≤ ‖w - c • w'‖ + ‖c • w' - w'‖ := by
        calc ‖w - w'‖ = ‖(w - c • w') + (c • w' - w')‖ := by abel_nf
          _ ≤ _ := norm_add_le _ _
      have h2 : ‖c • w' - w'‖ = |c - 1| := by
        rw [show c • w' - w' = (c - 1) • w' by rw [sub_smul, one_smul], norm_smul, hw', mul_one,
          Real.norm_eq_abs]
      rw [abs_of_nonneg hc0] at hcabs
      have : 8 * r / |a| = 4 * r / |a| + 4 * r / |a| := by ring
      linarith
    · apply (min_le_right _ _).trans_lt
      have h1 : ‖w + w'‖ ≤ ‖w - c • w'‖ + ‖c • w' + w'‖ := by
        calc ‖w + w'‖ = ‖(w - c • w') + (c • w' + w')‖ := by abel_nf
          _ ≤ _ := norm_add_le _ _
      have h2 : ‖c • w' + w'‖ = |c + 1| := by
        rw [show c • w' + w' = (c + 1) • w' by rw [add_smul, one_smul], norm_smul, hw', mul_one,
          Real.norm_eq_abs]
      rw [abs_of_neg hc0] at hcabs
      have h3 : |c + 1| = |(-c) - 1| := by rw [← abs_neg]; ring_nf
      have : 8 * r / |a| = 4 * r / |a| + 4 * r / |a| := by ring
      rw [h3] at h2
      linarith
  have h8 : 8 * r / |a| ≤ 16 * r / D := by
    rw [div_le_div_iff₀ ha0 hD0]; nlinarith
  linarith

/-- The part of an `r`-tube inside a closed ball of radius `D` has volume `O((D + r) r²)`. -/
theorem volume_tube_inter_closedBall_le {r D : ℝ} (hr : 0 < r) (hD : 0 ≤ D) {z w : Space}
    (hw : ‖w‖ = 1) (c : Space) :
    volume (tube r z w ∩ closedBall c D) ≤ ENNReal.ofReal (128 * (4 * (D + r) + r) * r ^ 2) := by
  set T : Set ℝ := {t | t ∈ Icc (0 : ℝ) 1 ∧ dist (z + t • w) c < D + r} with hT
  have hsub : tube r z w ∩ closedBall c D ⊆ thickening r ((fun t : ℝ => z + t • w) '' T) := by
    rintro y ⟨hy, hyc⟩
    obtain ⟨t, ht, hyt⟩ := tube_param hy
    rw [mem_thickening_iff]
    refine ⟨z + t • w, ⟨t, ⟨ht, ?_⟩, rfl⟩, ?_⟩
    · have h1 : dist (z + t • w) y < r := by rw [dist_comm, dist_eq_norm]; exact hyt
      have h2 : dist y c ≤ D := mem_closedBall.1 hyc
      calc dist (z + t • w) c ≤ dist (z + t • w) y + dist y c := dist_triangle _ _ _
        _ < r + D := by linarith
        _ = D + r := by ring
    · rw [dist_eq_norm]; exact hyt
  refine (measure_mono hsub).trans ?_
  have hA : 0 ≤ 2 * (D + r) := by linarith
  have := WangZahlLot.Obl.wz_direction_density_transfer.segment_piece_volume_upper z w hw
    (T := T) (fun t ht => ht.1) (r := r) (A := 2 * (D + r)) hr hA (by
      intro s hs t ht
      have h1 : dist s t = dist (z + s • w) (z + t • w) := by
        rw [Real.dist_eq, dist_eq_norm, show z + s • w - (z + t • w) = (s - t) • w by
          rw [sub_smul]; abel, norm_smul, hw, mul_one, Real.norm_eq_abs]
      rw [h1]
      calc dist (z + s • w) (z + t • w) ≤ dist (z + s • w) c + dist c (z + t • w) :=
            dist_triangle _ _ _
        _ ≤ (D + r) + (D + r) := by
            rw [dist_comm c]; linarith [hs.2, ht.2]
        _ = 2 * (D + r) := by ring)
  convert this using 3
  ring

/-- A bounded set of volume at least `a` inside an `r`-tube contains a `D`-separated finite set of
at least `a / (128 (4 (D + r) + r) r²)` points. -/
theorem exists_separated_in_tube {r D a : ℝ} (hr : 0 < r) (hD : 0 < D) {z w : Space}
    (hw : ‖w‖ = 1) {A : Set Space} (hA : Bornology.IsBounded A) (hAT : A ⊆ tube r z w)
    (ha : ENNReal.ofReal a ≤ volume A) :
    ∃ F : Finset Space, (↑F : Set Space) ⊆ A ∧ (∀ x ∈ F, ∀ y ∈ F, x ≠ y → D < dist x y) ∧
      a ≤ (F.card : ℝ) * (128 * (4 * (D + r) + r) * r ^ 2) := by
  have htb : TotallyBounded A := hA.isCompact_closure.totallyBounded.subset subset_closure
  obtain ⟨F, hFA, hsep, hcov⟩ :=
    WangZahlLot.Obl.kakeya_three_le_dimH_of_tube_estimate.exists_finset_separated_cover htb hD
  refine ⟨F, hFA, hsep, ?_⟩
  set b := 128 * (4 * (D + r) + r) * r ^ 2 with hb
  have hb0 : 0 ≤ b := by positivity
  have h1 : volume A ≤ ∑ x ∈ F, volume (tube r z w ∩ closedBall x D) := by
    calc volume A ≤ volume (⋃ x ∈ F, tube r z w ∩ closedBall x D) := by
          apply measure_mono
          intro y hy
          obtain ⟨x, hx, hyx⟩ := mem_iUnion₂.1 (hcov hy)
          exact mem_iUnion₂.2 ⟨x, hx, hAT hy, hyx⟩
      _ ≤ _ := measure_biUnion_finset_le _ _
  have h2 : ∑ x ∈ F, volume (tube r z w ∩ closedBall x D) ≤ ∑ _x ∈ F, ENNReal.ofReal b :=
    Finset.sum_le_sum fun x _ => volume_tube_inter_closedBall_le hr hD.le hw x
  rw [Finset.sum_const, nsmul_eq_mul] at h2
  have h3 := ha.trans (h1.trans h2)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at h3
  rcases le_or_gt a 0 with ha0 | ha0
  · exact ha0.trans (by positivity)
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

/-- Two points of an `r`-tube whose direction is nearly orthogonal to `u` differ little in the
`u`-coordinate. -/
theorem abs_inner_sub_le_of_tube {r d π : ℝ} {z w u x y : Space} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hx : x ∈ tube r z w) (hy : y ∈ tube r z w) (hxy : dist y x ≤ d)
    (hwu : |inner ℝ w u| ≤ π) :
    |inner ℝ u (y - x)| ≤ (d + 2 * r) * π + 2 * r := by
  obtain ⟨t, -, ht⟩ := tube_param hy
  obtain ⟨t', -, ht'⟩ := tube_param hx
  set e := y - (z + t • w)
  set e' := x - (z + t' • w)
  have hyx : y - x = (t - t') • w + (e - e') := by simp only [e, e', sub_smul]; abel
  have hee : ‖e - e'‖ < 2 * r := (norm_sub_le _ _).trans_lt (by linarith)
  have htt : |t - t'| ≤ d + 2 * r := by
    have h1 : ‖(t - t') • w‖ ≤ ‖y - x‖ + ‖e - e'‖ := by
      calc ‖(t - t') • w‖ = ‖(y - x) - (e - e')‖ := by rw [hyx]; abel_nf
        _ ≤ _ := norm_sub_le _ _
    rw [norm_smul, hw, mul_one, Real.norm_eq_abs, ← dist_eq_norm] at h1
    linarith
  have hπ : 0 ≤ π := (abs_nonneg _).trans hwu
  rw [hyx, inner_add_right, inner_smul_right, real_inner_comm]
  calc |(t - t') * inner ℝ w u + inner ℝ u (e - e')|
      ≤ |t - t'| * |inner ℝ w u| + ‖e - e'‖ := by
        refine (abs_add_le _ _).trans (add_le_add (by rw [abs_mul]) ?_)
        calc |inner ℝ u (e - e')| ≤ ‖u‖ * ‖e - e'‖ := abs_real_inner_le_norm _ _
          _ = ‖e - e'‖ := by rw [hu, one_mul]
    _ ≤ (d + 2 * r) * π + 2 * r := by
        have hd0 : 0 ≤ d := dist_nonneg.trans hxy
        have hr0 : 0 ≤ r := by have := norm_nonneg e; linarith
        have := mul_le_mul htt hwu (abs_nonneg _) (by linarith)
        linarith

/-- The mass measure is at most the maximal multiplicity times the volume of the shaded part. -/
theorem massMeasure_le_mul {n : ℕ} {Y : Fin n → Set Space} (hY : ∀ i, MeasurableSet (Y i))
    {μmax : ℝ} (hmax : ∀ y, (fineMult Y y : ℝ) ≤ μmax) {S : Set Space} (hS : MeasurableSet S) :
    massMeasure Y S ≤ ENNReal.ofReal μmax * volume ((⋃ i, Y i) ∩ S) := by
  rw [massMeasure, withDensity_apply _ hS]
  have hU : MeasurableSet (⋃ i, Y i) := MeasurableSet.iUnion hY
  calc ∫⁻ y in S, (fineMult Y y : ℝ≥0∞)
      ≤ ∫⁻ y in S, (⋃ i, Y i).indicator (fun _ => ENNReal.ofReal μmax) y := by
        apply lintegral_mono
        intro y
        by_cases hy : y ∈ ⋃ i, Y i
        · rw [indicator_of_mem hy]
          have := hmax y
          show (fineMult Y y : ℝ≥0∞) ≤ _
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal this
        · rw [indicator_of_notMem hy]
          have : fineMult Y y = 0 := by
            rw [fineMult, Set.ncard_eq_zero]
            ext i; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
            intro hi; exact hy (mem_iUnion.2 ⟨i, hi⟩)
          show (fineMult Y y : ℝ≥0∞) ≤ _
          simp [this]
    _ = ENNReal.ofReal μmax * volume ((⋃ i, Y i) ∩ S) := by
        rw [lintegral_indicator hU, setLIntegral_const, Measure.restrict_apply hU, inter_comm]

/-- **Fan lemma** (the grain-filling step of sticky Lemma 4.9).  Inside a bounded region `W`, a
tube `j0` whose shading carries `θP` there contains many `D`-separated points; through each of
them pass at least `μlo / 2` tubes transverse to `j0`, all distinct, each carrying `θP` in `W` and
lying in the `u`-slab through `x0` because their directions are nearly orthogonal to `u`.
Dividing by the maximal multiplicity gives a lower bound for the volume of the shaded union in
the slab. -/
theorem fan_volume_lower {k : ℕ} {z w : Fin k → Space} {Y1 Y2 Y3 : Fin k → Set Space}
    {r D β π dW μmax μlo θP : ℝ} {u : Space} {W : Set Space} {j0 : Fin k} {x0 : Space}
    (hr : 0 < r) (hD : 0 < D) (h4rD : 4 * r ≤ D) (hβ : 16 * r / D < β)
    (hw : ∀ j, ‖w j‖ = 1) (hu : ‖u‖ = 1)
    (hY1m : ∀ j, MeasurableSet (Y1 j)) (hY1T : ∀ j, Y1 j ⊆ tube r (z j) (w j))
    (hY21 : ∀ j, Y2 j ⊆ Y1 j) (hY32 : ∀ j, Y3 j ⊆ Y2 j)
    (hWb : Bornology.IsBounded W) (hWm : MeasurableSet W)
    (hWd : ∀ y ∈ W, ∀ y' ∈ W, dist y y' ≤ dW)
    (hmax : ∀ y, (fineMult Y1 y : ℝ) ≤ μmax)
    (hlo : ∀ y ∈ W, y ∈ Y3 j0 → μlo ≤ (fineMult Y2 y : ℝ))
    (hcone : ∀ y ∈ W, y ∈ Y3 j0 →
      (({j | y ∈ Y2 j ∧ min ‖w j - w j0‖ ‖w j + w j0‖ ≤ β}.ncard : ℕ) : ℝ) ≤ μlo / 2)
    (hP1 : ∀ j, (Y1 j ∩ W).Nonempty → ENNReal.ofReal θP ≤ volume (Y1 j ∩ W))
    (hP3 : ENNReal.ofReal θP ≤ volume (Y3 j0 ∩ W))
    (hplane : ∀ j, (Y1 j ∩ W).Nonempty → |inner ℝ (w j) u| ≤ π)
    (hx0 : x0 ∈ Y3 j0 ∩ W) (hμ : 0 < μmax) (hθ : 0 ≤ θP) :
    ENNReal.ofReal (θP ^ 2 * μlo / (256 * (4 * (D + r) + r) * r ^ 2 * μmax)) ≤
      volume ((⋃ j, Y1 j) ∩ (W ∩ {y | |inner ℝ u (y - x0)| ≤ 2 * ((dW + 2 * r) * π + 2 * r)})) := by
  classical
  set h := 2 * ((dW + 2 * r) * π + 2 * r) with hh
  set S' := W ∩ {y | |inner ℝ u (y - x0)| ≤ h} with hS'
  have hS'm : MeasurableSet S' := by
    apply hWm.inter
    exact (isClosed_le (continuous_abs.comp ((continuous_const.inner (continuous_id.sub
      continuous_const)))) continuous_const).measurableSet
  set b := 128 * (4 * (D + r) + r) * r ^ 2 with hb
  have hb0 : 0 < b := by positivity
  -- separated points in the shading of `j0`
  obtain ⟨F, hFA, hsep, hFcard⟩ := exists_separated_in_tube hr hD (hw j0)
    (hWb.subset inter_subset_right) ((inter_subset_left.trans (hY32 j0)).trans
      ((hY21 j0).trans (hY1T j0))) hP3
  -- transverse tubes through each point
  let S : Space → Finset (Fin k) := fun x =>
    Finset.univ.filter fun j => x ∈ Y2 j ∧ ¬ (min ‖w j - w j0‖ ‖w j + w j0‖ ≤ β)
  have hScard : ∀ x ∈ F, μlo / 2 ≤ ((S x).card : ℝ) := by
    intro x hx
    obtain ⟨hx3, hxW⟩ := hFA hx
    have h1 := hlo x hxW hx3
    have h2 := hcone x hxW hx3
    have hsplit : fineMult Y2 x ≤ (S x).card +
        ({j | x ∈ Y2 j ∧ min ‖w j - w j0‖ ‖w j + w j0‖ ≤ β}.ncard) := by
      rw [fineMult, ← Set.ncard_coe_finset]
      calc ({i | x ∈ Y2 i}.ncard) ≤ ((↑(S x) : Set (Fin k)) ∪
            {j | x ∈ Y2 j ∧ min ‖w j - w j0‖ ‖w j + w j0‖ ≤ β}).ncard := by
            apply Set.ncard_le_ncard _ (Set.toFinite _)
            intro j hj
            by_cases hc : min ‖w j - w j0‖ ‖w j + w j0‖ ≤ β
            · exact Or.inr ⟨hj, hc⟩
            · left; simp only [S, Finset.coe_filter, Finset.mem_univ, true_and]; exact ⟨hj, hc⟩
        _ ≤ _ := Set.ncard_union_le _ _
    have : (fineMult Y2 x : ℝ) ≤ (S x).card +
        (({j | x ∈ Y2 j ∧ min ‖w j - w j0‖ ‖w j + w j0‖ ≤ β}.ncard : ℕ) : ℝ) := by
      exact_mod_cast hsplit
    linarith
  -- disjointness
  have hdisj : (F : Set Space).PairwiseDisjoint S := by
    intro x hx x' hx' hne
    rw [Function.onFun, Finset.disjoint_left]
    intro j hj hj'
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hj hj'
    have hxx' := hsep x hx x' hx' hne
    have h1 := dir_close_of_two_points (hw j) (hw j0) ((hY21 j) hj.1 |> hY1T j)
      ((hY21 j) hj'.1 |> hY1T j) ((hY32 j0 (hFA hx).1) |> hY21 j0 |> hY1T j0)
      ((hY32 j0 (hFA hx').1) |> hY21 j0 |> hY1T j0) hxx' h4rD
    exact hj.2 (h1.trans hβ.le)
  set U := F.biUnion S with hU
  have hUcard : (F.card : ℝ) * (μlo / 2) ≤ (U.card : ℝ) := by
    rw [hU, Finset.card_biUnion hdisj]
    push_cast
    calc (F.card : ℝ) * (μlo / 2) = ∑ _x ∈ F, μlo / 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ x ∈ F, ((S x).card : ℝ) := Finset.sum_le_sum hScard
  -- each transverse tube carries `θP` inside the slab
  have hslab : ∀ j ∈ U, Y1 j ∩ S' = Y1 j ∩ W := by
    intro j hj
    obtain ⟨x, hxF, hjx⟩ := Finset.mem_biUnion.1 hj
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjx
    obtain ⟨hx3, hxW⟩ := hFA hxF
    have hne : (Y1 j ∩ W).Nonempty := ⟨x, hY21 j hjx.1, hxW⟩
    have hne0 : (Y1 j0 ∩ W).Nonempty := ⟨x, hY21 j0 (hY32 j0 hx3), hxW⟩
    apply subset_antisymm (inter_subset_inter_right _ inter_subset_left)
    rintro y ⟨hy1, hyW⟩
    refine ⟨hy1, hyW, ?_⟩
    show |inner ℝ u (y - x0)| ≤ h
    have e1 := abs_inner_sub_le_of_tube (hw j) hu (hY1T j (hY21 j hjx.1)) (hY1T j hy1)
      (hWd y hyW x hxW) (hplane j hne)
    have e2 := abs_inner_sub_le_of_tube (hw j0) hu (hY1T j0 (hY21 j0 (hY32 j0 hx0.1)))
      (hY1T j0 (hY21 j0 (hY32 j0 hx3))) (hWd x hxW x0 hx0.2) (hplane j0 hne0)
    have e3 : y - x0 = (y - x) + (x - x0) := by abel
    rw [e3, inner_add_right]
    calc |inner ℝ u (y - x) + inner ℝ u (x - x0)| ≤ |inner ℝ u (y - x)| + |inner ℝ u (x - x0)| :=
          abs_add_le _ _
      _ ≤ h := by rw [hh]; linarith
  have hmassU : ENNReal.ofReal ((U.card : ℝ) * θP) ≤ massMeasure Y1 S' := by
    rw [massMeasure_apply hY1m hS'm]
    calc ENNReal.ofReal ((U.card : ℝ) * θP) = ∑ _j ∈ U, ENNReal.ofReal θP := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
            ENNReal.ofReal_natCast]
      _ ≤ ∑ j ∈ U, volume (Y1 j ∩ S') := by
          apply Finset.sum_le_sum
          intro j hj
          rw [hslab j hj]
          obtain ⟨x, hxF, hjx⟩ := Finset.mem_biUnion.1 hj
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hjx
          exact hP1 j ⟨x, hY21 j hjx.1, (hFA hxF).2⟩
      _ ≤ ∑ j, volume (Y1 j ∩ S') :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => zero_le)
  have hup := massMeasure_le_mul hY1m hmax hS'm
  -- arithmetic
  have hfin : volume ((⋃ j, Y1 j) ∩ S') ≠ ∞ := by
    refine ne_top_of_le_ne_top (hWb.measure_lt_top).ne (measure_mono ?_)
    exact inter_subset_right.trans inter_subset_left
  have key : (U.card : ℝ) * θP ≤ μmax * (volume ((⋃ j, Y1 j) ∩ S')).toReal := by
    have h1 := hmassU.trans hup
    rw [← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_mul hμ.le] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  rcases le_or_gt μlo 0 with hlo0 | hlo0
  · have : θP ^ 2 * μlo / (256 * (4 * (D + r) + r) * r ^ 2 * μmax) ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hlo0
    exact this.trans ENNReal.toReal_nonneg
  rw [div_le_iff₀ (by positivity)]
  have hF2 : θP * (μlo / 2) * θP ≤ (F.card : ℝ) * b * (μlo / 2) * θP := by
    have := mul_le_mul_of_nonneg_right hFcard (by positivity : 0 ≤ μlo / 2 * θP)
    nlinarith
  have hU2 : (F.card : ℝ) * (μlo / 2) * θP ≤ (U.card : ℝ) * θP :=
    mul_le_mul_of_nonneg_right hUcard hθ
  have e : 256 * (4 * (D + r) + r) * r ^ 2 = 2 * b := by rw [hb]; ring
  rw [e]
  nlinarith [ENNReal.toReal_nonneg (a := volume ((⋃ j, Y1 j) ∩ S'))]

end WangZahlLot.Obl.wz_extremal_lipschitz_grains
