-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.BipartiteMoment.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.FirstMoment
import Submission.WZ.Obl.wz_jet_close_pair_moment.Pairwise

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_jet_close_pair_moment (strip measurableSet_strip JetControlled)

/-- The mixed first moment counts the overlap areas of the two specified colors. -/
theorem lintegral_finiteMultiplicity_mul {ι : Type*} (A B : Finset ι) (δ : ℝ)
    {g : ι → ℝ → ℝ} (hgA : ∀ i ∈ A, Continuous (g i))
    (hgB : ∀ i ∈ B, Continuous (g i)) :
    (∫⁻ p, finiteMultiplicity A δ g p * finiteMultiplicity B δ g p) =
      ∑ i ∈ A, ∑ j ∈ B, volume (strip δ (g i) ∩ strip δ (g j)) := by
  classical
  have he : (fun p => finiteMultiplicity A δ g p * finiteMultiplicity B δ g p) =
      fun p => ∑ i ∈ A, ∑ j ∈ B,
        (strip δ (g i) ∩ strip δ (g j)).indicator (fun _ => (1 : ℝ≥0∞)) p := by
    funext p
    unfold finiteMultiplicity
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hi' : p ∈ strip δ (g i) <;> by_cases hj' : p ∈ strip δ (g j) <;>
      simp [hi', hj']
  rw [he]
  rw [lintegral_finsetSum A (fun i hi => Finset.measurable_sum B (fun j hj =>
    measurable_const.indicator
      ((measurableSet_strip (hgA i hi)).inter (measurableSet_strip (hgB j hj)))))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_finsetSum B (fun j hj => measurable_const.indicator
    ((measurableSet_strip (hgA i hi)).inter (measurableSet_strip (hgB j hj))))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [lintegral_indicator
    ((measurableSet_strip (hgA i hi)).inter (measurableSet_strip (hgB j hj))),
    lintegral_const, Measure.restrict_apply_univ, one_mul]

/-- The unrestricted bipartite estimate supplied by pairwise jet geometry.
The actual product of the two cardinalities is retained. -/
theorem exists_bipartite_pair_area_constant : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
      JetControlled q g → (∀ i, ContDiff ℝ 2 (g i)) →
    ∀ (A B : Finset (Fin n)) (δ D μ : ℝ), 0 < δ → 0 < D → 0 < μ →
      (∀ i ∈ A, ∀ j ∈ B, D ≤ dist (q i) (q j)) →
      volume {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p ∧
        ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p} ≤
      ENNReal.ofReal
        (C * δ * Real.sqrt (δ / D) * (A.card : ℝ) * (B.card : ℝ) / μ ^ 2) := by
  obtain ⟨C, hC, hpair⟩ :=
    WangZahlLot.Obl.wz_jet_close_pair_moment.exists_pairwise_overlap_constant
  refine ⟨C, hC, ?_⟩
  intro n q g hjet hg A B δ D μ hδ hD hμ hfar
  have hm : (∫⁻ p, finiteMultiplicity A δ g p * finiteMultiplicity B δ g p) ≤
      ENNReal.ofReal (C * δ * Real.sqrt (δ / D) * (A.card : ℝ) * (B.card : ℝ)) := by
    rw [lintegral_finiteMultiplicity_mul A B δ (fun i _ => (hg i).continuous)
      (fun i _ => (hg i).continuous)]
    calc
      _ ≤ ∑ _i ∈ A, ∑ _j ∈ B, ENNReal.ofReal (C * δ * Real.sqrt (δ / D)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        apply (hpair hjet hg i j δ hδ (hD.trans_le (hfar i hi j hj))).trans
        apply ENNReal.ofReal_le_ofReal
        gcongr
        exact hfar i hi j hj
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul' (Nat.cast_nonneg B.card),
          ENNReal.ofReal_mul' (Nat.cast_nonneg A.card), ENNReal.ofReal_natCast,
          ENNReal.ofReal_natCast]
        ring
  calc
    _ ≤ volume {p | ENNReal.ofReal (μ ^ 2) ≤
        finiteMultiplicity A δ g p * finiteMultiplicity B δ g p} := by
      apply measure_mono
      intro p hp
      simpa only [Set.mem_ofPred_eq, pow_two, ENNReal.ofReal_mul hμ.le] using
        mul_le_mul' hp.1 hp.2
    _ ≤ (∫⁻ p, finiteMultiplicity A δ g p * finiteMultiplicity B δ g p) /
        ENNReal.ofReal (μ ^ 2) :=
      meas_ge_le_lintegral_div
        ((measurable_finiteMultiplicity A δ (fun i _ => (hg i).continuous)).mul
          (measurable_finiteMultiplicity B δ (fun i _ => (hg i).continuous))).aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (sq_pos_of_pos hμ)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal
        (C * δ * Real.sqrt (δ / D) * (A.card : ℝ) * (B.card : ℝ)) /
        ENNReal.ofReal (μ ^ 2) := by gcongr
    _ = _ := (ENNReal.ofReal_div_of_pos (sq_pos_of_pos hμ)).symm

/-- An explicit sufficient cardinality condition for the desired linear-mass
bound. This applies to the full simultaneous rich set, without a slope condition. -/
theorem exists_area_constant_of_sqrt_card_product : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
      JetControlled q g → (∀ i, ContDiff ℝ 2 (g i)) →
    ∀ (A B : Finset (Fin n)) (δ D τ a K μ : ℝ), 0 < δ → 0 < D → 0 < μ →
      (∀ i ∈ A, ∀ j ∈ B, D ≤ dist (q i) (q j)) →
      Real.sqrt (δ / D) * (A.card : ℝ) * (B.card : ℝ) ≤
        δ ^ (-τ) * K ^ a * μ ^ (1 / 2 : ℝ) * ((A.card : ℝ) + (B.card : ℝ)) →
      volume {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p ∧
        ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p} ≤
        ENNReal.ofReal (C * δ ^ (-τ) * K ^ a * δ *
          ((A.card : ℝ) + (B.card : ℝ)) * μ ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_bipartite_pair_area_constant
  refine ⟨C, hC, ?_⟩
  intro n q g hjet hg A B δ D τ a K μ hδ hD hμ hfar hcard
  apply (hbound hjet hg A B δ D μ hδ hD hμ hfar).trans
  apply ENNReal.ofReal_le_ofReal
  have hpow : μ ^ (1 / 2 : ℝ) / μ ^ 2 = μ ^ (-(3 / 2 : ℝ)) := by
    rw [← Real.rpow_two, ← Real.rpow_sub hμ]
    norm_num
  calc
    _ = (C * δ / μ ^ 2) *
        (Real.sqrt (δ / D) * (A.card : ℝ) * (B.card : ℝ)) := by ring
    _ ≤ (C * δ / μ ^ 2) *
        (δ ^ (-τ) * K ^ a * μ ^ (1 / 2 : ℝ) * ((A.card : ℝ) + (B.card : ℝ))) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = C * δ ^ (-τ) * K ^ a * δ * ((A.card : ℝ) + (B.card : ℝ)) *
        (μ ^ (1 / 2 : ℝ) / μ ^ 2) := by ring
    _ = _ := by rw [hpow]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
