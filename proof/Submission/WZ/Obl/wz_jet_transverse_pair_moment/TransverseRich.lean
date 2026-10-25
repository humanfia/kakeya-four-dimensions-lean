-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_transverse_pair_moment.TransverseRich.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_transverse_pair_moment.Transverse
import Submission.WZ.Obl.wz_jet_transverse_pair_moment.CriticalEnergy

namespace WangZahlLot.Obl.wz_jet_transverse_pair_moment

open MeasureTheory

/-- Number of ordered, distinct transverse pairs through a point. -/
noncomputable def transverseMultiplicity {n : ℕ} (δ κ : ℝ)
    (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ)
    (p : ℝ × ℝ) : ENNReal :=
  ∑ i, ∑ j, if i=j then 0 else
    (transverseIntersection δ κ (q i) (q j) (g i) (g j)).indicator (fun _ => 1) p

theorem measurable_transverseMultiplicity {n : ℕ} {δ κ : ℝ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) : Measurable (transverseMultiplicity δ κ q g) := by
  classical
  apply Finset.measurable_sum
  intro i hi
  apply Finset.measurable_sum
  intro j hj
  by_cases hij : i=j
  · simpa only [ite_eq_left hij] using (measurable_const (a := (0 : ENNReal)))
  · simpa only [ite_eq_right hij] using measurable_const.indicator
      (measurableSet_transverseIntersection (hg i) (hg j))

theorem lintegral_transverseMultiplicity {n : ℕ} {δ κ : ℝ}
    {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) :
    ∫⁻ p, transverseMultiplicity δ κ q g p =
      ∑ i, ∑ j, if i=j then 0 else
        volume (transverseIntersection δ κ (q i) (q j) (g i) (g j)) := by
  classical
  have hm : ∀ i j : Fin n, Measurable (fun p : ℝ × ℝ => if i=j then (0 : ENNReal) else
      (transverseIntersection δ κ (q i) (q j) (g i) (g j)).indicator (fun _ => 1) p) := by
    intro i j
    by_cases hij : i=j
    · simpa only [ite_eq_left hij] using (measurable_const (a := (0 : ENNReal)))
    · simpa only [ite_eq_right hij] using measurable_const.indicator
        (measurableSet_transverseIntersection (hg i) (hg j))
  unfold transverseMultiplicity
  rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ (fun j _ => hm i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_finsetSum _ (fun j _ => hm i j)]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hij : i=j
  · simp only [ite_eq_left hij, lintegral_zero]
  · simp only [ite_eq_right hij]
    rw [lintegral_indicator (measurableSet_transverseIntersection (hg i) (hg j)),
      lintegral_const, Measure.restrict_apply_univ, one_mul]

/-- Summing transverse pair overlaps uses critical, rather than square-root,
coefficient energy. Its power loss can be as small as desired. -/
theorem transverse_moment_bound (τ : ℝ) (hτ : 0 < τ) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ}
      {δ η κ : ℝ}, 0 < δ → δ ≤ 1 → 0 < κ → κ ≤ 1 →
      (∀ i, ‖q i‖ ≤ 10) → (∀ i, ContDiff ℝ 2 (g i)) → JetControlled q g →
      (∀ i j, i ≠ j → δ ≤ dist (q i) (q j)) →
      (∀ (q0 : EuclideanSpace ℝ (Fin 3)) (r : ℝ), δ ≤ r → r ≤ 1 →
        (Set.ncard {i | q i ∈ Metric.ball q0 r} : ℝ) ≤ δ^(-η)*(r/δ)) →
      ∫⁻ p, transverseMultiplicity δ κ q g p ≤ ENNReal.ofReal (C*δ^(-2*η-τ)/κ) := by
  classical
  obtain ⟨B, hB, hpair⟩ := exists_uniform_transverse_overlap_constant
  obtain ⟨E, hE, henergy⟩ := coefficient_inverse_energy τ hτ
  obtain ⟨N, hN, hcard⟩ := coefficient_card_bound
  refine ⟨N*B*E, by positivity, ?_⟩
  intro n q g δ η κ hδ hδ1 hκ hκ1 hq hg hjet hsep hcount
  have hrow : ∀ i : Fin n, (∑ j, if i=j then 0 else
      volume (transverseIntersection δ κ (q i) (q j) (g i) (g j))) ≤
        ENNReal.ofReal (B*δ^2/κ*(E*δ^(-η-1-τ))) := by
    intro i
    let f : Fin n → ℝ := fun j => B*δ^2/κ*(dist (q i) (q j))⁻¹
    have hf : ∀ j, 0 ≤ f j := by intro j; dsimp [f]; positivity
    have hsum : (∑ j, if i=j then 0 else
        volume (transverseIntersection δ κ (q i) (q j) (g i) (g j))) ≤
          ENNReal.ofReal (∑ j, f j) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => hf j)]
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i=j
      · simp only [ite_eq_left hij]
        exact zero_le
      · rw [ite_eq_right hij]
        have hd : 0 < dist (q i) (q j) := hδ.trans_le (hsep i j hij)
        convert hpair hjet hg i j δ κ hδ hκ hκ1 hd using 2
        dsimp [f]
        ring
    apply hsum.trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [f, ← Finset.mul_sum]
    gcongr
    exact henergy hδ hδ1 hq hsep hcount i
  rw [lintegral_transverseMultiplicity hg]
  apply (Finset.sum_le_sum (fun i _ => hrow i)).trans
  have he : (∑ _i : Fin n, ENNReal.ofReal (B*δ^2/κ*(E*δ^(-η-1-τ)))) =
      ENNReal.ofReal ((n : ℝ)*(B*δ^2/κ*(E*δ^(-η-1-τ)))) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n)]
  rw [he]
  apply ENNReal.ofReal_le_ofReal
  calc
    (n : ℝ)*(B*δ^2/κ*(E*δ^(-η-1-τ))) ≤
        (N*(δ^(-η)/δ))*(B*δ^2/κ*(E*δ^(-η-1-τ))) := by
      gcongr
      exact hcard hδ hδ1 hq hcount
    _ = (N*B*E)/κ*((δ^(-η)*δ⁻¹)*δ^2*δ^(-η-1-τ)) := by ring
    _ = (N*B*E)*δ^(-2*η-τ)/κ := by
      rw [← Real.rpow_neg_one δ, ← Real.rpow_natCast δ 2,
        ← Real.rpow_add hδ, ← Real.rpow_add hδ, ← Real.rpow_add hδ]
      have he : -η + -1 + (2 : ℕ) + (-η-1-τ) = -2*η-τ := by push_cast; ring
      rw [he]
      ring

end WangZahlLot.Obl.wz_jet_transverse_pair_moment
