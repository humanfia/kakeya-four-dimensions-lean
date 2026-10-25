-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_close_pair_moment.SecondMoment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_close_pair_moment.Pairwise
import Submission.WZ.Obl.wz_jet_close_pair_moment.Energy

namespace WangZahlLot.Obl.wz_jet_close_pair_moment

open MeasureTheory

/-- Expanding the square counts all ordered pairs of strips. -/
theorem lintegral_multiplicity_sq {n : ℕ} {δ : ℝ} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i)) :
    ∫⁻ p, multiplicity δ g p ^ 2 =
      ∑ i, ∑ j, volume (strip δ (g i) ∩ strip δ (g j)) := by
  have he : (fun p => multiplicity δ g p ^ 2) = fun p =>
      ∑ i, ∑ j, (strip δ (g i) ∩ strip δ (g j)).indicator (fun _ => (1 : ENNReal)) p := by
    funext p
    simp only [pow_two, multiplicity, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hi' : p ∈ strip δ (g i) <;> by_cases hj' : p ∈ strip δ (g j) <;>
      simp [hi', hj']
  rw [he]
  have hm : ∀ i j : Fin n, Measurable
      ((strip δ (g i) ∩ strip δ (g j)).indicator (fun _ => (1 : ENNReal))) :=
    fun i j => measurable_const.indicator
      ((measurableSet_strip (hg i)).inter (measurableSet_strip (hg j)))
  rw [lintegral_finsetSum _ (fun i hi => Finset.measurable_sum _ (fun j hj => hm i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_finsetSum _ (fun j hj => hm i j)]
  apply Finset.sum_congr rfl
  intro j hj
  rw [lintegral_indicator ((measurableSet_strip (hg i)).inter (measurableSet_strip (hg j))),
    lintegral_const, Measure.restrict_apply_univ, one_mul]

/-- A uniform second-moment estimate obtained by summing the pairwise overlap
bound with the one-dimensional coefficient energy estimate. -/
theorem second_moment_bound : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
      {δ η : ℝ}, 0 < δ → δ ≤ 1 → 0 ≤ η → (∀ i, ‖q i‖ ≤ 10) →
      (∀ i, ContDiff ℝ 2 (g i)) → JetControlled q g →
      (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) →
      (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
        (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ^(-η)*(r/δ)) →
      ∫⁻ p, multiplicity δ g p ^ 2 ≤ ENNReal.ofReal (C * δ^(-(1/2 : ℝ)-2*η)) := by
  classical
  obtain ⟨B, hB, hpair⟩ := exists_pairwise_overlap_constant
  obtain ⟨E, hE, henergy⟩ := coefficient_inverse_sqrt_energy
  obtain ⟨N, hN, hcard⟩ := coefficient_card_bound
  refine ⟨N*(4+B*E), by positivity, ?_⟩
  intro n q g δ η hδ hδ1 hη hq hg hjet hsep hcount
  have hsqrt : 0 ≤ Real.sqrt δ := Real.sqrt_nonneg _
  have hp : 0 ≤ δ^(-η) := Real.rpow_nonneg hδ.le _
  have hp1 : 1 ≤ δ^(-η) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hδsqrt : δ ≤ Real.sqrt δ :=
    (Real.le_sqrt hδ.le hδ.le).mpr (by nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hδ1)])
  have hdiag : δ ≤ Real.sqrt δ * δ^(-η) :=
    hδsqrt.trans (by nlinarith)
  have hrow : ∀ i : Fin n, ∑ j, volume (strip δ (g i) ∩ strip δ (g j)) ≤
      ENNReal.ofReal ((4+B*E)*Real.sqrt δ*δ^(-η)) := by
    intro i
    let f : Fin n → ℝ := fun j => (if j=i then 4*δ else 0) +
      B*δ*Real.sqrt δ*(Real.sqrt (dist (q i) (q j)))⁻¹
    have hf : ∀ j, 0 ≤ f j := by intro j; dsimp [f]; split_ifs <;> positivity
    have hsum : ∑ j, volume (strip δ (g i) ∩ strip δ (g j)) ≤ ENNReal.ofReal (∑ j, f j) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => hf j)]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hji : j=i
      · subst j
        simp [f, volume_strip (hg i).continuous]
      · have hd : 0 < dist (q i) (q j) := hδ.trans_le (hsep i j (Ne.symm hji))
        have h := hpair hjet hg i j δ hδ hd
        convert h using 2
        simp only [f, ite_eq_right hji, zero_add]
        rw [Real.sqrt_div hδ.le]
        simp only [div_eq_mul_inv]
        ring
    have hsumf : ∑ j, f j = 4*δ + B*δ*Real.sqrt δ*∑ j, (Real.sqrt (dist (q i) (q j)))⁻¹ := by
      simp only [f, Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    apply hsum.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hsumf]
    calc
      4*δ + B*δ*Real.sqrt δ*∑ j, (Real.sqrt (dist (q i) (q j)))⁻¹ ≤
          4*δ + B*δ*Real.sqrt δ*(E*(δ^(-η)/δ)) := by
        gcongr
        exact henergy hδ hδ1 hq hsep hcount i
      _ = 4*δ + (B*E)*Real.sqrt δ*δ^(-η) := by field_simp
      _ ≤ (4+B*E)*Real.sqrt δ*δ^(-η) := by nlinarith
  rw [lintegral_multiplicity_sq (fun i => (hg i).continuous)]
  apply (Finset.sum_le_sum (fun i _ => hrow i)).trans
  have hsum : (∑ _i : Fin n, ENNReal.ofReal ((4+B*E)*Real.sqrt δ*δ^(-η))) =
      ENNReal.ofReal ((n : ℝ)*((4+B*E)*Real.sqrt δ*δ^(-η))) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  rw [hsum]
  apply ENNReal.ofReal_le_ofReal
  have hn := hcard hδ hδ1 hq hcount
  calc
    (n : ℝ)*((4+B*E)*Real.sqrt δ*δ^(-η)) ≤
        (N*(δ^(-η)/δ))*((4+B*E)*Real.sqrt δ*δ^(-η)) := by gcongr
    _ = (N*(4+B*E)) * ((δ^(-η)/δ)*Real.sqrt δ*δ^(-η)) := by ring
    _ = (N*(4+B*E)) * δ^(-(1/2 : ℝ)-2*η) := by
      congr 1
      rw [div_eq_mul_inv, ← Real.rpow_neg_one δ, Real.sqrt_eq_rpow,
        ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      congr 1
      ring

/-- Chebyshev's inequality for the finite multiplicity, in the exact rich-set
form used by the frozen theorem. -/
theorem rich_volume_le_of_second_moment {n : ℕ} {δ lam A : ℝ}
    {g : Fin n → ℝ → ℝ} (hg : ∀ i, Continuous (g i)) (hlam : 0 < lam)
    (hsecond : ∫⁻ p, multiplicity δ g p ^ 2 ≤ ENNReal.ofReal A) :
    volume {p | ENNReal.ofReal lam ≤ multiplicity δ g p} ≤ ENNReal.ofReal (A/lam^2) := by
  have hlam2 : 0 < lam^2 := sq_pos_of_pos hlam
  have hmeas := ((measurable_multiplicity (δ := δ) hg).pow_const 2).aemeasurable (μ := volume)
  have h := meas_ge_le_lintegral_div (μ := volume) hmeas
    (ENNReal.ofReal_ne_zero_iff.mpr hlam2) ENNReal.ofReal_ne_top
  have hsub : {p | ENNReal.ofReal lam ≤ multiplicity δ g p} ⊆
      {p | ENNReal.ofReal (lam^2) ≤ multiplicity δ g p ^ 2} := by
    intro p hp
    rw [ENNReal.ofReal_pow hlam.le]
    exact pow_le_pow_left' (show ENNReal.ofReal lam ≤ multiplicity δ g p from hp) 2
  apply (measure_mono hsub).trans (h.trans ?_)
  calc
    (∫⁻ p, multiplicity δ g p ^ 2) / ENNReal.ofReal (lam^2) ≤
        ENNReal.ofReal A / ENNReal.ofReal (lam^2) := by gcongr
    _ = ENNReal.ofReal (A/lam^2) := (ENNReal.ofReal_div_of_pos hlam2).symm

/-- The exact target bound at the largest multiplicities. This leaves a
middle range for the genuinely multi-curve incidence argument. -/
theorem rich_point_bound_high_multiplicity (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ d0 : ℝ, 0 < d0 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ d0 → δ ≤ 1 →
    ∀ (n : ℕ) (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ),
      (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → JetControlled q g →
      (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) →
      (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
        (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ^(-η)*(r/δ)) →
    ∀ lam : ℝ, 1 ≤ lam → δ^(-1+ε) ≤ lam →
      volume {p | ENNReal.ofReal lam ≤ multiplicity δ g p} ≤
        ENNReal.ofReal (δ^(-ε)*lam^(-(3/2 : ℝ))) := by
  obtain ⟨C, hC, hsecond⟩ := second_moment_bound
  obtain ⟨d0, hd0, habsorb⟩ := exists_small_scale_absorption C (ε/4) (by positivity)
  refine ⟨ε/8, by positivity, d0, hd0, ?_⟩
  intro δ hδ hδ0 hδ1 n q g hq hg hjet hsep hcount lam hlam hlarge
  have hlam0 : 0 < lam := lt_of_lt_of_le (by norm_num) hlam
  have hmoment := hsecond hδ hδ1 (by positivity : 0 ≤ ε/8) hq hg hjet hsep hcount
  apply (rich_volume_le_of_second_moment (fun i => (hg i).continuous) hlam0 hmoment).trans
  apply ENNReal.ofReal_le_ofReal
  have hroot : δ^((-1+ε)*(1/2 : ℝ)) ≤ lam^(1/2 : ℝ) := by
    rw [Real.rpow_mul hδ.le]
    gcongr
  have hbudget : C*δ^(-(1/2 : ℝ)-2*(ε/8)) ≤ δ^(-ε)*lam^(1/2 : ℝ) := by
    calc
      C*δ^(-(1/2 : ℝ)-2*(ε/8)) =
          (C*δ^(ε/4)) * (δ^(-ε)*δ^((-1+ε)*(1/2 : ℝ))) := by
        rw [mul_assoc C, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
        congr 2
        ring
      _ ≤ 1 * (δ^(-ε)*δ^((-1+ε)*(1/2 : ℝ))) := by
        gcongr
        exact habsorb δ hδ hδ0
      _ ≤ δ^(-ε)*lam^(1/2 : ℝ) := by
        rw [one_mul]
        gcongr
  calc
    C*δ^(-(1/2 : ℝ)-2*(ε/8))/lam^2 ≤ (δ^(-ε)*lam^(1/2 : ℝ))/lam^2 := by
      gcongr
    _ = δ^(-ε)*lam^(-(3/2 : ℝ)) := by
      rw [← Real.rpow_natCast lam 2, div_eq_mul_inv, ← Real.rpow_neg hlam0.le,
        mul_assoc, ← Real.rpow_add hlam0]
      norm_num

end WangZahlLot.Obl.wz_jet_close_pair_moment
