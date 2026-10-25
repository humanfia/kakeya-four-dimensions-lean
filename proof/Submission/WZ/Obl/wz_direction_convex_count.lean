-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_direction_convex_count.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Mathlib
import Submission.WZ.ChallengeDeps
set_option linter.unusedVariables false

/-!
# `WangZahlLot.wz_direction_convex_count`

The convex Katz–Tao count for tubes with `δ`-separated directions, proved by an elementary
difference-body argument (no John ellipsoid).

Let `U = interior W`; tubes are open, so `T_i ⊆ W ↔ T_i ⊆ U`. With
`F y = vol {p ∈ U | p + y ∈ U}`:

* `vol_slice_ge`: if `2 y = w₁ - w₂` with `w₁ w₂ ∈ U`, the homothety of ratio `1/2` about `w₂`
  maps `U` into `{p ∈ U | p + y ∈ U}`, so `F y ≥ vol U / 8`;
* `lintegral_vol_slice`: Tonelli, `∫⁻ y, F y = vol U * vol U`;
* `exists_diff_of_mem_ball`: every ball `ball (t • v_i) (δ/2)`, `0 ≤ t ≤ 1/2`, lies in `½ (U - U)`;
* `quarter_le_norm_sub`: `‖t • u - s • w‖² = (t - s)² + t s ‖u - w‖²`, so for `t, s ≥ 1/4` the
  points on different rays are `δ/4` apart;
* `card_mul_sq_le`: the `N ⌊1/δ⌋` balls `ball ((1/4 + k δ/4) • v_i) (δ/8)` are disjoint and lie
  in `½ (U - U)`, whence `vol U / 8 * N ⌊1/δ⌋ (δ/8)³ vol (ball 0 1) ≤ vol U²`, i.e.
  `N δ² ≤ 8192 / vol (ball 0 1) * vol U`.

Only `δ ≤ ‖v i - v j‖` is used from the separation hypothesis.
-/

namespace WangZahlLot.Obl.wz_direction_convex_count

open MeasureTheory Set Metric LeanEval.Analysis.WangZahlKakeya
open scoped ENNReal

/-- The slice volume `F y = vol {p ∈ U | p + y ∈ U}` is at least `vol U / 8` when `2 y ∈ U - U`. -/
theorem vol_slice_ge {U : Set Space} (hU : Convex ℝ U) {w₁ w₂ y : Space} (h₁ : w₁ ∈ U)
    (h₂ : w₂ ∈ U) (hy : (2 : ℝ) • y = w₁ - w₂) :
    ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume U ≤ volume {p | p ∈ U ∧ p + y ∈ U} := by
  have hsub : AffineMap.homothety w₂ (1 / 2 : ℝ) '' U ⊆ {p | p ∈ U ∧ p + y ∈ U} := by
    rintro _ ⟨a, ha, rfl⟩
    have hy' : y = (1 / 2 : ℝ) • (w₁ - w₂) := by
      rw [← hy, smul_smul]; norm_num
    have e1 : AffineMap.homothety w₂ (1 / 2 : ℝ) a = (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • w₂ := by
      rw [AffineMap.homothety_apply]
      simp only [vsub_eq_sub, vadd_eq_add, smul_sub]
      module
    refine ⟨?_, ?_⟩
    · rw [e1]; exact hU ha h₂ (by norm_num) (by norm_num) (by norm_num)
    · rw [e1, hy']
      have : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • w₂ + (1 / 2 : ℝ) • (w₁ - w₂)
          = (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • w₁ := by module
      rw [this]; exact hU ha h₁ (by norm_num) (by norm_num) (by norm_num)
  calc ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume U
      = volume (AffineMap.homothety w₂ (1 / 2 : ℝ) '' U) := by
        rw [Measure.addHaar_image_homothety, finrank_euclideanSpace_fin]
        congr 2
        rw [abs_of_pos (by norm_num)]
    _ ≤ _ := measure_mono hsub

/-- Tonelli: `∫⁻ y, vol {p ∈ U | p + y ∈ U} = vol U * vol U`. -/
theorem lintegral_vol_slice {U : Set Space} (hU : MeasurableSet U) :
    ∫⁻ y, volume {p | p ∈ U ∧ p + y ∈ U} = volume U * volume U := by
  set S : Set (Space × Space) := {z | z.2 ∈ U ∧ z.2 + z.1 ∈ U} with hS
  have hSm : MeasurableSet S :=
    (measurable_snd hU).inter ((measurable_snd.add measurable_fst) hU)
  have h1 : (volume.prod volume) S = ∫⁻ y, volume {p | p ∈ U ∧ p + y ∈ U} := by
    rw [Measure.prod_apply hSm]
    rfl
  have h2 : (volume.prod volume) S = ∫⁻ p, U.indicator (fun _ => volume U) p := by
    rw [Measure.prod_apply_symm hSm]
    congr 1
    funext p
    by_cases hp : p ∈ U
    · rw [indicator_of_mem hp]
      have : (fun x => (x, p)) ⁻¹' S = (fun x => p + x) ⁻¹' U := by
        ext x; simp [hS, hp]
      rw [this, measure_preimage_add]
    · rw [indicator_of_notMem hp]
      have : (fun x => (x, p)) ⁻¹' S = ∅ := by
        ext x; simp [hS, hp]
      rw [this, measure_empty]
  rw [← h1, h2, lintegral_indicator_const hU, mul_comm]

/-- A point `q` near `t • v` (`0 ≤ t ≤ 1/2`) has `2 q` in the difference set of a tube. -/
theorem exists_diff_of_mem_ball {δ : ℝ} (hδ : 0 < δ) {x v q : Space} {U : Set Space}
    (hT : thickening δ (segment ℝ x (x + v)) ⊆ U) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1 / 2)
    (hq : q ∈ ball (t • v) (δ / 2)) :
    ∃ w₁ ∈ U, ∃ w₂ ∈ U, (2 : ℝ) • q = w₁ - w₂ := by
  refine ⟨x + (2 : ℝ) • q, hT ?_, x, hT (self_subset_thickening hδ _ (left_mem_segment ℝ x (x + v))),
    by abel⟩
  rw [mem_thickening_iff]
  refine ⟨x + (2 * t) • v, ?_, ?_⟩
  · rw [segment_eq_image']
    exact ⟨2 * t, ⟨by linarith, by linarith⟩, by simp⟩
  · rw [mem_ball, dist_eq_norm] at hq
    rw [dist_eq_norm]
    have : x + (2 : ℝ) • q - (x + (2 * t) • v) = (2 : ℝ) • (q - t • v) := by
      rw [smul_sub, smul_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith

/-- Points `t • u`, `s • w` on two unit rays with `t, s ≥ 1/4` are `δ/4` apart when
`δ ≤ ‖u - w‖`. -/
theorem quarter_le_norm_sub {u w : Space} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) {δ t s : ℝ}
    (hδ : 0 ≤ δ) (huw : δ ≤ ‖u - w‖) (ht : 1 / 4 ≤ t) (hs : 1 / 4 ≤ s) :
    δ / 4 ≤ ‖t • u - s • w‖ := by
  have h1 : ‖t • u - s • w‖ ^ 2 = t ^ 2 - 2 * t * s * inner ℝ u w + s ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right, hu,
      hw, Real.norm_eq_abs, Real.norm_eq_abs, mul_one, mul_one, sq_abs, sq_abs]
    ring
  have h2 : ‖u - w‖ ^ 2 = 2 - 2 * inner ℝ u w := by
    rw [norm_sub_sq_real, hu, hw]; ring
  have h3 : δ ^ 2 ≤ ‖u - w‖ ^ 2 := pow_le_pow_left₀ hδ huw 2
  have h4 : (δ / 4) ^ 2 ≤ ‖t • u - s • w‖ ^ 2 := by
    rw [h1]
    have hts : 1 / 16 ≤ t * s := by nlinarith
    nlinarith [sq_nonneg (t - s)]
  exact (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) (by norm_num)).1 h4

/-- Volume of a disjoint finite union of balls of the same radius. -/
theorem volume_biUnion_ball {ι : Type*} (s : Finset ι) (c : ι → Space) {r : ℝ} (hr : 0 < r)
    (hd : (s : Set ι).PairwiseDisjoint (fun j => ball (c j) r)) :
    volume (⋃ j ∈ s, ball (c j) r) =
      s.card * (ENNReal.ofReal (r ^ 3) * volume (ball (0 : Space) 1)) := by
  rw [measure_biUnion_finset hd (fun _ _ => measurableSet_ball)]
  simp_rw [Measure.addHaar_ball_of_pos volume _ hr, finrank_euclideanSpace_fin]
  rw [Finset.sum_const, nsmul_eq_mul]

/-- The main estimate, for an open convex `U` of finite volume containing the tubes of `s`. -/
theorem card_mul_sq_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 100) {n : ℕ} {x v : Fin n → Space}
    (hv : ∀ i, ‖v i‖ = 1) (hsep : ∀ i j, i ≠ j → δ ≤ ‖v i - v j‖)
    {U : Set Space} (hUc : Convex ℝ U) (hUo : IsOpen U) (s : Finset (Fin n))
    (hs : ∀ i ∈ s, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ U) (hfin : volume U ≠ ⊤)
    (hne : s.Nonempty) :
    (s.card : ℝ) * δ ^ 2 ≤ 8192 / (volume (ball (0 : Space) 1)).toReal * (volume U).toReal := by
  classical
  set K : ℕ := ⌊1 / δ⌋₊ with hK
  set t : ℕ → ℝ := fun k => 1 / 4 + k * δ / 4 with ht
  have hK1 : 1 / δ < K + 1 := Nat.lt_floor_add_one _
  have hK2 : (K : ℝ) ≤ 1 / δ := Nat.floor_le (by positivity)
  have hKδ : 1 < ((K : ℝ) + 1) * δ := (div_lt_iff₀ hδ).1 hK1
  have hKδ' : (K : ℝ) * δ ≤ 1 := by
    have := mul_le_mul_of_nonneg_right hK2 hδ.le
    rwa [one_div, inv_mul_cancel₀ hδ.ne'] at this
  have ht_lo : ∀ k, 1 / 4 ≤ t k := fun k => by
    have : 0 ≤ (k : ℝ) * δ / 4 := by positivity
    simp only [ht]; linarith
  have ht_hi : ∀ k < K, t k ≤ 1 / 2 := by
    intro k hk
    have hk' : (k : ℝ) + 1 ≤ K := by exact_mod_cast hk
    have : (k : ℝ) * δ ≤ 1 := by nlinarith
    simp only [ht]; linarith
  set I : Finset (Fin n × ℕ) := s ×ˢ Finset.range K with hI
  set c : Fin n × ℕ → Space := fun p => t p.2 • v p.1 with hc
  set r : ℝ := δ / 8 with hr
  have hr0 : 0 < r := by positivity
  -- the balls are pairwise disjoint
  have hdisj : (I : Set (Fin n × ℕ)).PairwiseDisjoint (fun j => ball (c j) r) := by
    intro p _ q _ hpq
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    simp only [hc, hr]
    rcases eq_or_ne p.1 q.1 with h | h
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h h2)
      rw [h, ← sub_smul, norm_smul, hv, mul_one, Real.norm_eq_abs]
      simp only [ht]
      have h1 : (1 : ℝ) ≤ |(p.2 : ℝ) - q.2| := by
        rcases lt_or_gt_of_ne h2 with h3 | h3
        · have : (p.2 : ℝ) + 1 ≤ q.2 := by exact_mod_cast h3
          rw [abs_of_neg (by linarith)]; linarith
        · have : (q.2 : ℝ) + 1 ≤ p.2 := by exact_mod_cast h3
          rw [abs_of_pos (by linarith)]; linarith
      have e : 1 / 4 + (p.2 : ℝ) * δ / 4 - (1 / 4 + (q.2 : ℝ) * δ / 4) =
          ((p.2 : ℝ) - q.2) * (δ / 4) := by ring
      rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < δ / 4)]
      nlinarith
    · have := quarter_le_norm_sub (hv p.1) (hv q.1) hδ.le (hsep _ _ h) (ht_lo p.2) (ht_lo q.2)
      linarith
  -- the balls lie in `½ (U - U)`, where the slice volume is at least `vol U / 8`
  set A : Set Space := ⋃ j ∈ I, ball (c j) r with hA
  have hAm : MeasurableSet A := Finset.measurableSet_biUnion I (fun _ _ => measurableSet_ball)
  have hAF : ∀ y ∈ A, ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume U ≤
      volume {p | p ∈ U ∧ p + y ∈ U} := by
    intro y hy
    simp only [hA, mem_iUnion] at hy
    obtain ⟨j, hj, hyj⟩ := hy
    rw [hI, Finset.mem_product, Finset.mem_range] at hj
    obtain ⟨w₁, hw₁, w₂, hw₂, hw⟩ := exists_diff_of_mem_ball hδ (hs j.1 hj.1)
      (by linarith [ht_lo j.2]) (ht_hi j.2 hj.2)
      (ball_subset_ball (by simp only [hr]; linarith) hyj)
    exact vol_slice_ge hUc hw₁ hw₂ hw
  have hint : ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume U * volume A ≤
      volume U * volume U := by
    rw [← lintegral_vol_slice hUo.measurableSet, ← lintegral_indicator_const hAm]
    apply lintegral_mono
    intro y
    by_cases hy : y ∈ A
    · rw [indicator_of_mem hy]; exact hAF y hy
    · rw [indicator_of_notMem hy]; exact zero_le
  -- `vol U > 0`
  obtain ⟨i₀, hi₀⟩ := hne
  have hU0 : volume U ≠ 0 := by
    have h1 : ball (x i₀) δ ⊆ U :=
      (ball_subset_thickening (left_mem_segment ℝ (x i₀) (x i₀ + v i₀)) δ).trans (hs i₀ hi₀)
    exact ((measure_ball_pos volume (x i₀) hδ).trans_le (measure_mono h1)).ne'
  have h5 : ENNReal.ofReal ((1 / 2 : ℝ) ^ 3) * volume A ≤ volume U := by
    rw [mul_right_comm] at hint
    exact (ENNReal.mul_le_mul_iff_left hU0 hfin).1 hint
  rw [hA, volume_biUnion_ball I c hr0 hdisj, hI, Finset.card_product, Finset.card_range] at h5
  have hc₀ : volume (ball (0 : Space) 1) ≠ ⊤ := measure_ball_lt_top.ne
  have hc₀pos : 0 < (volume (ball (0 : Space) 1)).toReal :=
    ENNReal.toReal_pos (measure_ball_pos volume _ one_pos).ne' hc₀
  have h6 := ENNReal.toReal_mono hfin h5
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (1 / 2) ^ 3),
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ r ^ 3), ENNReal.toReal_natCast,
    Nat.cast_mul] at h6
  set c₀ := (volume (ball (0 : Space) 1)).toReal
  set V := (volume U).toReal
  rw [div_mul_eq_mul_div, le_div_iff₀ hc₀pos]
  simp only [hr] at h6
  have hcard : (0 : ℝ) ≤ s.card := Nat.cast_nonneg _
  have hX : 0 ≤ (s.card : ℝ) * δ ^ 2 * c₀ := by positivity
  nlinarith [mul_nonneg hX (by nlinarith : (0 : ℝ) ≤ 2 * K * δ - 1)]

/-- The theorem, stated in full inside the namespace. -/
theorem main : ∃ M : ℝ, 1 ≤ M ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space), (∀ i : Fin n, ‖v i‖ = 1) → (∀ i j : Fin n, i ≠ j → δ ≤ ‖v i - v j‖ ∧ δ ≤ ‖v i + v j‖) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (M) * MeasureTheory.volume W) := by
  classical
  set c₀ := (volume (ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1)).toReal with hc₀
  refine ⟨max 1 (8192 / c₀), le_max_left _ _, ?_⟩
  intro δ hδ hδ1 n x v hv hsep _ W hW
  set s : Finset (Fin n) :=
    Finset.univ.filter (fun i => thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W) with hs_def
  have hcard : Set.ncard {i : Fin n | thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} =
      s.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext i
    simp [hs_def]
  rw [hcard]
  have hs : ∀ i ∈ s, thickening δ (segment ℝ (x i) (x i + v i)) ⊆ interior W := by
    intro i hi
    simp only [hs_def, Finset.mem_filter] at hi
    exact (isOpen_thickening.subset_interior_iff).2 hi.2
  rcases s.eq_empty_or_nonempty with hse | hne
  · simp [hse]
  have hM : 0 < max 1 (8192 / c₀) := lt_of_lt_of_le one_pos (le_max_left _ _)
  by_cases hWtop : volume W = ⊤
  · rw [hWtop, ENNReal.mul_top (by simp)]
    exact le_top
  have hfin : volume (interior W) ≠ ⊤ :=
    ne_top_of_le_ne_top hWtop (measure_mono interior_subset)
  have key := card_mul_sq_le hδ hδ1 hv
    (fun i j h => (hsep i j h).1) hW.interior isOpen_interior s hs hfin hne
  calc ENNReal.ofReal ((s.card : ℝ) * δ ^ 2)
      ≤ ENNReal.ofReal (8192 / c₀ * (volume (interior W)).toReal) := ENNReal.ofReal_le_ofReal key
    _ ≤ ENNReal.ofReal (max 1 (8192 / c₀) * (volume (interior W)).toReal) :=
        ENNReal.ofReal_le_ofReal (by gcongr; exact le_max_right _ _)
    _ = ENNReal.ofReal (max 1 (8192 / c₀)) * volume (interior W) := by
        rw [ENNReal.ofReal_mul hM.le, ENNReal.ofReal_toReal hfin]
    _ ≤ ENNReal.ofReal (max 1 (8192 / c₀)) * volume W := by
        gcongr
        exact interior_subset

end WangZahlLot.Obl.wz_direction_convex_count

theorem WangZahlLot.wz_direction_convex_count : ∃ M : ℝ, 1 ≤ M ∧ ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 100 : ℝ) → ∀ (n : ℕ) (x v : Fin n → LeanEval.Analysis.WangZahlKakeya.Space), (∀ i : Fin n, ‖v i‖ = 1) → (∀ i j : Fin n, i ≠ j → δ ≤ ‖v i - v j‖ ∧ δ ≤ ‖v i + v j‖) → (∀ i : Fin n, Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ Metric.ball (0 : LeanEval.Analysis.WangZahlKakeya.Space) 1) → (∀ W : Set LeanEval.Analysis.WangZahlKakeya.Space, Convex ℝ W → ENNReal.ofReal (((Set.ncard {i : Fin n | Metric.thickening δ (segment ℝ (x i) (x i + v i)) ⊆ W} : ℕ) : ℝ) * δ ^ 2) ≤ ENNReal.ofReal (M) * MeasureTheory.volume W) :=
  WangZahlLot.Obl.wz_direction_convex_count.main
