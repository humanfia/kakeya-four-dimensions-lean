-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_close_pair_moment.ClosePairs.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_close_pair_moment.SecondMoment
import Submission.WZ.Obl.wz_jet_close_pair_moment.LocalizedEnergy

namespace WangZahlLot.Obl.wz_jet_close_pair_moment

open MeasureTheory

/-- Ordered strip pairs with coefficient distance less than `R`, including
the diagonal when `R` is positive. -/
noncomputable def closePairMultiplicity {n : ℕ} (δ R : ℝ)
    (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ)
    (p : ℝ × ℝ) : ENNReal :=
  ∑ i, ∑ j, if dist (q i) (q j) < R then
    (strip δ (g i) ∩ strip δ (g j)).indicator (fun _ => 1) p else 0

theorem measurable_closePairMultiplicity {n : ℕ} {δ R : ℝ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i)) : Measurable (closePairMultiplicity δ R q g) := by
  classical
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro j hj
  by_cases hd : dist (q i) (q j) < R
  · simpa only [ite_eq_left hd] using measurable_const.indicator
      ((measurableSet_strip (hg i)).inter (measurableSet_strip (hg j)))
  · simpa only [ite_eq_right hd] using (measurable_const (a := (0 : ENNReal)))

theorem lintegral_closePairMultiplicity {n : ℕ} {δ R : ℝ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i)) :
    ∫⁻ p, closePairMultiplicity δ R q g p =
      ∑ i, ∑ j, if dist (q i) (q j) < R then
        volume (strip δ (g i) ∩ strip δ (g j)) else 0 := by
  classical
  have hm : ∀ i j : Fin n, Measurable (fun p : ℝ × ℝ =>
      if dist (q i) (q j) < R then
        (strip δ (g i) ∩ strip δ (g j)).indicator (fun _ => (1 : ENNReal)) p else 0) := by
    intro i j
    by_cases hd : dist (q i) (q j) < R
    · simpa only [ite_eq_left hd] using measurable_const.indicator
        ((measurableSet_strip (hg i)).inter (measurableSet_strip (hg j)))
    · simpa only [ite_eq_right hd] using (measurable_const (a := (0 : ENNReal)))
  unfold closePairMultiplicity
  rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ (fun j _ => hm i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_finsetSum _ (fun j _ => hm i j)]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hd : dist (q i) (q j) < R
  · simp only [ite_eq_left hd]
    rw [lintegral_indicator ((measurableSet_strip (hg i)).inter (measurableSet_strip (hg j))),
      lintegral_const, Measure.restrict_apply_univ, one_mul]
  · simp only [ite_eq_right hd, lintegral_zero]

/-- Close coefficient pairs satisfy a scale-sensitive second moment. Unlike
the full second moment, this retains the factor `sqrt (R / δ)`. -/
theorem close_pair_moment_bound : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
      {δ η R : ℝ}, 0 < δ → δ ≤ 1 → 0 ≤ η → δ ≤ R →
      (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → JetControlled q g →
      (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) →
      (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
        (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ^(-η)*(r/δ)) →
      ∫⁻ p, closePairMultiplicity δ R q g p ≤
        ENNReal.ofReal (C*δ^(-2*η)*Real.sqrt (R/δ)) := by
  classical
  obtain ⟨B, hB, hpair⟩ := exists_pairwise_overlap_constant
  obtain ⟨E, hE, henergy⟩ := coefficient_local_inverse_sqrt_energy
  obtain ⟨N, hN, hcard⟩ := coefficient_card_bound
  refine ⟨N*(4+B*E), by positivity, ?_⟩
  intro n q g δ η R hδ hδ1 hη hδR hq hg hjet hsep hcount
  have hR : 0 < R := hδ.trans_le hδR
  have hp : 0 ≤ δ^(-η) := Real.rpow_nonneg hδ.le _
  have hp1 : 1 ≤ δ^(-η) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hroots : δ ≤ Real.sqrt δ*Real.sqrt R := by
    have h := Real.sqrt_le_sqrt hδR
    nlinarith [Real.sq_sqrt hδ.le, Real.sqrt_nonneg δ]
  have hdiag : δ ≤ δ^(-η)*Real.sqrt δ*Real.sqrt R := by
    calc
      δ ≤ Real.sqrt δ*Real.sqrt R := hroots
      _ ≤ δ^(-η)*(Real.sqrt δ*Real.sqrt R) := by
        nlinarith [mul_nonneg (Real.sqrt_nonneg δ) (Real.sqrt_nonneg R)]
      _ = _ := by ring
  have hrow : ∀ i : Fin n,
      (∑ j, if dist (q i) (q j) < R then
        volume (strip δ (g i) ∩ strip δ (g j)) else 0) ≤
      ENNReal.ofReal ((4+B*E)*δ^(-η)*Real.sqrt δ*Real.sqrt R) := by
    intro i
    let e : Fin n → ℝ := fun j => if j ≠ i ∧ dist (q i) (q j) < R then
      (Real.sqrt (dist (q i) (q j)))⁻¹ else 0
    let f : Fin n → ℝ := fun j => (if j=i then 4*δ else 0) +
      B*δ*Real.sqrt δ*e j
    have he : ∀ j, 0 ≤ e j := by intro j; dsimp [e]; split_ifs <;> positivity
    have hf : ∀ j, 0 ≤ f j := by
      intro j
      dsimp [f]
      split_ifs <;> positivity
    have hsum : (∑ j, if dist (q i) (q j) < R then
        volume (strip δ (g i) ∩ strip δ (g j)) else 0) ≤ ENNReal.ofReal (∑ j, f j) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hf j)]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hji : j=i
      · subst j
        simp [f, e, hR, volume_strip (hg i).continuous]
      · by_cases hdR : dist (q i) (q j) < R
        · rw [ite_eq_left hdR]
          have hd : 0 < dist (q i) (q j) := hδ.trans_le (hsep i j (Ne.symm hji))
          convert hpair hjet hg i j δ hδ hd using 2
          simp only [f, e, ite_eq_right hji, ite_eq_left (And.intro hji hdR), zero_add]
          rw [Real.sqrt_div hδ.le]
          ring
        · simp only [ite_eq_right hdR]
          exact zero_le
    apply hsum.trans (ENNReal.ofReal_le_ofReal ?_)
    have heSum : ∑ j, e j ≤ E*(δ^(-η)/δ)*Real.sqrt R :=
      henergy hδ hδ1 hR hq hsep hcount i
    have hsumf : ∑ j, f j = 4*δ+B*δ*Real.sqrt δ*∑ j, e j := by
      simp only [f, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    rw [hsumf]
    calc
      4*δ+B*δ*Real.sqrt δ*∑ j, e j ≤
          4*δ+B*δ*Real.sqrt δ*(E*(δ^(-η)/δ)*Real.sqrt R) := by gcongr
      _ = 4*δ+B*E*δ^(-η)*Real.sqrt δ*Real.sqrt R := by field_simp
      _ ≤ (4+B*E)*δ^(-η)*Real.sqrt δ*Real.sqrt R := by nlinarith
  rw [lintegral_closePairMultiplicity (fun i => (hg i).continuous)]
  apply (Finset.sum_le_sum (fun i _ => hrow i)).trans
  have hsum : (∑ _i : Fin n, ENNReal.ofReal ((4+B*E)*δ^(-η)*Real.sqrt δ*Real.sqrt R)) =
      ENNReal.ofReal ((n : ℝ)*((4+B*E)*δ^(-η)*Real.sqrt δ*Real.sqrt R)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  rw [hsum]
  apply ENNReal.ofReal_le_ofReal
  have hn := hcard hδ hδ1 hq hcount
  have hpowers : δ^(-η)*δ^(-η) = δ^(-2*η) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hsqrt : Real.sqrt δ*Real.sqrt R/δ = Real.sqrt (R/δ) := by
    rw [Real.sqrt_div hR.le]
    have hnz : Real.sqrt δ ≠ 0 := (Real.sqrt_pos.mpr hδ).ne'
    field_simp
    nlinarith [Real.sq_sqrt hδ.le]
  calc
    (n : ℝ)*((4+B*E)*δ^(-η)*Real.sqrt δ*Real.sqrt R) ≤
        (N*(δ^(-η)/δ))*((4+B*E)*δ^(-η)*Real.sqrt δ*Real.sqrt R) := by gcongr
    _ = (N*(4+B*E))*(δ^(-η)*δ^(-η))*(Real.sqrt δ*Real.sqrt R/δ) := by ring
    _ = (N*(4+B*E))*δ^(-2*η)*Real.sqrt (R/δ) := by rw [hpowers, hsqrt]

/-- A coefficient-close subfamily through a point contributes the square of
its cardinality to the ordered close-pair count. -/
theorem card_sq_le_closePairMultiplicity {n : ℕ} {δ R : ℝ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (F : Finset (Fin n)) {p : ℝ × ℝ}
    (hp : ∀ i ∈ F, p ∈ strip δ (g i))
    (hclose : ∀ i ∈ F, ∀ j ∈ F, dist (q i) (q j) < R) :
    (F.card : ENNReal)^2 ≤ closePairMultiplicity δ R q g p := by
  classical
  let a : Fin n → Fin n → ENNReal := fun i j => if dist (q i) (q j) < R then
    (strip δ (g i) ∩ strip δ (g j)).indicator (fun _ => 1) p else 0
  have hpair : ∀ i ∈ F, ∀ j ∈ F, a i j = 1 := by
    intro i hi j hj
    simp [a, hclose i hi j hj, hp i hi, hp j hj]
  have hs : (F.card : ENNReal)^2 = ∑ i ∈ F, ∑ j ∈ F, a i j := by
    symm
    calc
      (∑ i ∈ F, ∑ j ∈ F, a i j) = ∑ i ∈ F, ∑ _j ∈ F, (1 : ENNReal) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact Finset.sum_congr rfl (fun j hj => hpair i hi j hj)
      _ = (F.card : ENNReal)^2 := by simp [pow_two, nsmul_eq_mul]
  rw [hs]
  change (∑ i ∈ F, ∑ j ∈ F, a i j) ≤ ∑ i, ∑ j, a i j
  calc
    (∑ i ∈ F, ∑ j ∈ F, a i j) ≤ ∑ i ∈ F, ∑ j, a i j :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum_of_subset (Finset.subset_univ F))
    _ ≤ ∑ i, ∑ j, a i j := Finset.sum_le_sum_of_subset (Finset.subset_univ F)

/-- An incident subfamily in one coefficient ball gives many close pairs.
There is no need to select a global partition of the coefficient space. -/
theorem coefficient_ball_sq_le_closePairMultiplicity {n : ℕ} {δ r : ℝ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (c : EuclideanSpace ℝ (Fin 3)) (p : ℝ × ℝ) :
    (Set.ncard {i | q i ∈ Metric.ball c r ∧ p ∈ strip δ (g i)} : ENNReal)^2 ≤
      closePairMultiplicity δ (2*r) q g p := by
  classical
  let F : Finset (Fin n) := Finset.univ.filter
    (fun i => q i ∈ Metric.ball c r ∧ p ∈ strip δ (g i))
  have he : (↑F : Set (Fin n)) = {i | q i ∈ Metric.ball c r ∧ p ∈ strip δ (g i)} := by
    ext i
    simp [F]
  rw [← he, Set.ncard_coe_finset]
  apply card_sq_le_closePairMultiplicity F
  · intro i hi
    exact (Finset.mem_filter.mp hi).2.2
  · intro i hi j hj
    have hi' := Metric.mem_ball.mp (Finset.mem_filter.mp hi).2.1
    have hj' := Metric.mem_ball.mp (Finset.mem_filter.mp hj).2.1
    have ht := dist_triangle (q i) c (q j)
    rw [dist_comm c (q j)] at ht
    linarith

/-- The desired decay holds for points having many coefficient-close pairs.
The distance cutoff allows a small power enlargement of `δ * lam`. -/
theorem rich_point_bound_close_pairs (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ 1 →
    ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ),
      (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → JetControlled q g →
      (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) →
      (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
        (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ^(-η)*(r/δ)) →
    ∀ lam : ℝ, 1 ≤ lam →
      volume {p | ENNReal.ofReal (lam^2/4) ≤
        closePairMultiplicity δ (2*δ*lam*δ^(-ε/2)) q g p} ≤
        ENNReal.ofReal (δ^(-ε)*lam^(-(3/2 : ℝ))) := by
  obtain ⟨C, hC, hmoment⟩ := close_pair_moment_bound
  obtain ⟨d0, hd0, habsorb⟩ := exists_small_scale_absorption
    (4*C*Real.sqrt 2) (ε/2) (by positivity)
  refine ⟨ε/8, by positivity, d0, hd0, ?_⟩
  intro δ hδ hδ0 hδ1 n q g hq hg hjet hsep hcount lam hlam
  have hlam0 : 0 < lam := lt_of_lt_of_le (by norm_num) hlam
  have hδpow : 1 ≤ δ^(-ε/2) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hδR : δ ≤ 2*δ*lam*δ^(-ε/2) := by
    have h := mul_le_mul_of_nonneg_right hlam (by positivity : 0 ≤ 2*δ)
    have h' := mul_le_mul_of_nonneg_left hδpow (by positivity : 0 ≤ 2*δ*lam)
    nlinarith
  have hlevel : 0 < lam^2/4 := by positivity
  have h := meas_ge_le_lintegral_div (μ := volume)
    (measurable_closePairMultiplicity (δ := δ) (R := 2*δ*lam*δ^(-ε/2))
      (q := q) (fun i => (hg i).continuous)).aemeasurable
    (ENNReal.ofReal_ne_zero_iff.mpr hlevel) ENNReal.ofReal_ne_top
  have hm := hmoment hδ hδ1 (by positivity : 0 ≤ ε/8) hδR hq hg hjet hsep hcount
  apply h.trans
  calc
    (∫⁻ p, closePairMultiplicity δ (2*δ*lam*δ^(-ε/2)) q g p) /
        ENNReal.ofReal (lam^2/4) ≤
        ENNReal.ofReal (C*δ^(-2*(ε/8))*Real.sqrt ((2*δ*lam*δ^(-ε/2))/δ)) /
          ENNReal.ofReal (lam^2/4) := by gcongr
    _ = ENNReal.ofReal ((4*C*Real.sqrt 2)*δ^(-ε/2)*lam^(-(3/2 : ℝ))) := by
      rw [← ENNReal.ofReal_div_of_pos hlevel]
      congr 1
      have hdiv : (2*δ*lam*δ^(-ε/2))/δ = 2*lam*δ^(-ε/2) := by field_simp
      have hroot : Real.sqrt (δ^(-ε/2)) = δ^(-ε/4) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hδ.le]
        congr 1
        ring
      have hpowers : δ^(-2*(ε/8))*δ^(-ε/4) = δ^(-ε/2) := by
        rw [← Real.rpow_add hδ]
        congr 1
        ring
      have hlamPow : Real.sqrt lam / lam^2 = lam^(-(3/2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast lam 2, div_eq_mul_inv,
          ← Real.rpow_neg hlam0.le, ← Real.rpow_add hlam0]
        norm_num
      rw [hdiv, Real.sqrt_mul (by positivity : 0 ≤ 2*lam),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), hroot]
      calc
        C*δ^(-2*(ε/8))*(Real.sqrt 2*Real.sqrt lam*δ^(-ε/4))/(lam^2/4) =
            (4*C*Real.sqrt 2)*(δ^(-2*(ε/8))*δ^(-ε/4))*(Real.sqrt lam/lam^2) := by ring
        _ = _ := by rw [hpowers, hlamPow]
    _ ≤ ENNReal.ofReal (δ^(-ε)*lam^(-(3/2 : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hlam0.le _)
      calc
        (4*C*Real.sqrt 2)*δ^(-ε/2) = ((4*C*Real.sqrt 2)*δ^(ε/2))*δ^(-ε) := by
          rw [mul_assoc (4*C*Real.sqrt 2), ← Real.rpow_add hδ]
          congr 1
          congr 1
          ring
        _ ≤ 1*δ^(-ε) := mul_le_mul_of_nonneg_right (habsorb δ hδ hδ0)
          (Real.rpow_nonneg hδ.le _)
        _ = δ^(-ε) := one_mul _

/-- The frozen numerical bound holds for coefficient-narrow points, with a
power-enlarged radius. The center of the coefficient ball may depend on the
point; the conclusion is an outer-volume bound and needs no selection. -/
theorem rich_point_bound_coefficient_narrow (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ 1 →
    ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ),
      (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → JetControlled q g →
      (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) →
      (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
        (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ^(-η)*(r/δ)) →
    ∀ lam : ℝ, 1 ≤ lam →
      volume {p | ∃ c : EuclideanSpace ℝ (Fin 3), lam/2 ≤
        (Set.ncard {i | q i ∈ Metric.ball c (δ*lam*δ^(-ε/2)) ∧
          p ∈ strip δ (g i)} : ℝ)} ≤
        ENNReal.ofReal (δ^(-ε)*lam^(-(3/2 : ℝ))) := by
  obtain ⟨η, hη, d0, hd0, hbound⟩ := rich_point_bound_close_pairs ε hε
  refine ⟨η, hη, d0, hd0, ?_⟩
  intro δ hδ hδ0 hδ1 n q g hq hg hjet hsep hcount lam hlam
  apply le_trans (measure_mono ?_) (hbound δ hδ hδ0 hδ1 n q g hq hg hjet hsep hcount lam hlam)
  rintro p ⟨c, hc⟩
  have hsq : lam^2/4 ≤
      (Set.ncard {i | q i ∈ Metric.ball c (δ*lam*δ^(-ε/2)) ∧ p ∈ strip δ (g i)} : ℝ)^2 := by
    have h := mul_self_le_mul_self (by linarith : 0 ≤ lam/2) hc
    nlinarith
  have hENN := ENNReal.ofReal_le_ofReal hsq
  rw [ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast] at hENN
  have hball := coefficient_ball_sq_le_closePairMultiplicity
    (δ := δ) (r := δ*lam*δ^(-ε/2)) (q := q) (g := g) c p
  have he : 2*(δ*lam*δ^(-ε/2)) = 2*δ*lam*δ^(-ε/2) := by ring
  rw [he] at hball
  exact hENN.trans hball

end WangZahlLot.Obl.wz_jet_close_pair_moment
