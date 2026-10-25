-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_jet_bipartite_rich_area.Restricted.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.FirstMoment
import Submission.WZ.Obl.wz_jet_bipartite_rich_area.NearPairs

noncomputable section

namespace WangZahlLot.Obl.wz_jet_bipartite_rich_area

open MeasureTheory Set
open scoped ENNReal
open WangZahlLot.Obl.wz_jet_close_pair_moment (strip JetControlled)

def transverseMultiplicity {n : ℕ} (A B : Finset (Fin n)) (δ κ : ℝ)
    (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ≥0∞ :=
  ∑ i ∈ A, ∑ j ∈ B,
    (strip δ (g i) ∩ strip δ (g j) ∩
      {p | κ * dist (q i) (q j) ≤ |deriv (g i) p.2 - deriv (g j) p.2|}).indicator
      (fun _ => 1) p

def narrowMultiplicity {n : ℕ} (A B : Finset (Fin n)) (δ κ : ℝ)
    (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ)
    (p : ℝ × ℝ) : ℝ≥0∞ :=
  ∑ i ∈ A, ∑ j ∈ B,
    (narrowIntersection δ κ (q i) (q j) (g i) (g j)).indicator (fun _ => 1) p

/-- The two types of pairs partition the ordered bipartite incidences exactly. -/
theorem multiplicity_product_eq {n : ℕ} (A B : Finset (Fin n)) (δ κ : ℝ)
    (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ) (p : ℝ × ℝ) :
    finiteMultiplicity A δ g p * finiteMultiplicity B δ g p =
      transverseMultiplicity A B δ κ q g p + narrowMultiplicity A B δ κ q g p := by
  classical
  unfold finiteMultiplicity transverseMultiplicity narrowMultiplicity
  rw [← Finset.sum_add_distrib, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hi : p ∈ strip δ (g i)
  · by_cases hj : p ∈ strip δ (g j)
    · by_cases hs : κ * dist (q i) (q j) ≤ |deriv (g i) p.2 - deriv (g j) p.2|
      · simp [narrowIntersection, hi, hj, hs, not_lt.mpr hs]
      · simp [narrowIntersection, hi, hj, hs, lt_of_not_ge hs]
    · simp [narrowIntersection, hi, hj]
  · simp [narrowIntersection, hi]

theorem measurable_narrowMultiplicity {n : ℕ} (A B : Finset (Fin n)) (δ κ : ℝ)
    (q : Fin n → EuclideanSpace ℝ (Fin 3)) {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) : Measurable (narrowMultiplicity A B δ κ q g) := by
  exact Finset.measurable_sum A fun i _ => Finset.measurable_sum B fun j _ =>
    measurable_const.indicator (measurableSet_narrowIntersection (hg i) (hg j))

/-- Fewer than one percent transverse pairs leaves at least half of `μ²`
strictly narrow ordered pairs. -/
theorem half_sq_le_narrowMultiplicity {n : ℕ} (A B : Finset (Fin n)) {δ κ μ : ℝ}
    (q : Fin n → EuclideanSpace ℝ (Fin 3)) (g : Fin n → ℝ → ℝ)
    (hμ : 0 < μ) {p : ℝ × ℝ}
    (hA : ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p)
    (hB : ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p)
    (hT : transverseMultiplicity A B δ κ q g p < ENNReal.ofReal (μ ^ 2 / 100)) :
    ENNReal.ofReal (μ ^ 2 / 2) ≤ narrowMultiplicity A B δ κ q g p := by
  by_contra hN
  have hN' := (lt_of_not_ge hN).le
  have hprod : ENNReal.ofReal (μ ^ 2) ≤
      transverseMultiplicity A B δ κ q g p + narrowMultiplicity A B δ κ q g p := by
    rw [← multiplicity_product_eq]
    simpa only [pow_two, ENNReal.ofReal_mul hμ.le] using mul_le_mul' hA hB
  have htotal : ENNReal.ofReal (μ ^ 2) ≤ ENNReal.ofReal (μ ^ 2 / 100 + μ ^ 2 / 2) := by
    calc
      _ ≤ _ := hprod
      _ ≤ ENNReal.ofReal (μ ^ 2 / 100) + ENNReal.ofReal (μ ^ 2 / 2) :=
        add_le_add hT.le hN'
      _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  have hlt : ENNReal.ofReal (μ ^ 2 / 100 + μ ^ 2 / 2) < ENNReal.ofReal (μ ^ 2) :=
    (ENNReal.ofReal_lt_ofReal_iff (sq_pos_of_pos hμ)).mpr (by nlinarith [sq_pos_of_pos hμ])
  exact (not_le_of_gt hlt) htotal

/-- The integral of the narrow pair count is the sum of the pair overlap areas. -/
theorem lintegral_narrowMultiplicity {n : ℕ} (A B : Finset (Fin n)) (δ κ : ℝ)
    (q : Fin n → EuclideanSpace ℝ (Fin 3)) {g : Fin n → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) :
    (∫⁻ p, narrowMultiplicity A B δ κ q g p) =
      ∑ i ∈ A, ∑ j ∈ B, volume (narrowIntersection δ κ (q i) (q j) (g i) (g j)) := by
  unfold narrowMultiplicity
  rw [lintegral_finsetSum A (fun i _ => Finset.measurable_sum B (fun j _ =>
    measurable_const.indicator (measurableSet_narrowIntersection (hg i) (hg j))))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_finsetSum B (fun j _ =>
    measurable_const.indicator (measurableSet_narrowIntersection (hg i) (hg j)))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [lintegral_indicator (measurableSet_narrowIntersection (hg i) (hg j)),
    lintegral_const, Measure.restrict_apply_univ, one_mul]

/-- The elementary bipartite area bound supplied by the small-slope pair
estimate. The cardinality product, rather than its desired linear replacement,
is explicit. -/
theorem exists_restricted_pair_area_constant : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
      JetControlled q g → (∀ i, ContDiff ℝ 2 (g i)) →
    ∀ (A B : Finset (Fin n)) (δ κ μ : ℝ), 0 < δ → 0 ≤ κ → 0 < μ →
      (∀ i ∈ A, ∀ j ∈ B, 1000 * δ < dist (q i) (q j)) →
      volume {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p ∧
        ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p ∧
        transverseMultiplicity A B δ κ q g p < ENNReal.ofReal (μ ^ 2 / 100)} ≤
        ENNReal.ofReal (C * δ * κ * (A.card : ℝ) * (B.card : ℝ) / μ ^ 2) := by
  obtain ⟨C, hC, hpair⟩ := exists_narrow_overlap_constant
  refine ⟨2 * C, by positivity, ?_⟩
  intro n q g hjet hg A B δ κ μ hδ hκ hμ hfar
  have hm : (∫⁻ p, narrowMultiplicity A B δ κ q g p) ≤
      ENNReal.ofReal (C * δ * κ * (A.card : ℝ) * (B.card : ℝ)) := by
    rw [lintegral_narrowMultiplicity A B δ κ q hg]
    calc
      _ ≤ ∑ _i ∈ A, ∑ _j ∈ B, ENNReal.ofReal (C * δ * κ) :=
        Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
          hpair hjet hg i j δ κ hδ hκ (hfar i hi j hj)
      _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        rw [ENNReal.ofReal_mul' (Nat.cast_nonneg B.card),
          ENNReal.ofReal_mul' (Nat.cast_nonneg A.card), ENNReal.ofReal_natCast,
          ENNReal.ofReal_natCast]
        ring
  calc
    _ ≤ volume {p | ENNReal.ofReal (μ ^ 2 / 2) ≤ narrowMultiplicity A B δ κ q g p} := by
      apply measure_mono
      intro p hp
      exact half_sq_le_narrowMultiplicity A B q g hμ hp.1 hp.2.1 hp.2.2
    _ ≤ (∫⁻ p, narrowMultiplicity A B δ κ q g p) / ENNReal.ofReal (μ ^ 2 / 2) :=
      meas_ge_le_lintegral_div (measurable_narrowMultiplicity A B δ κ q hg).aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr (by positivity)) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (C * δ * κ * (A.card : ℝ) * (B.card : ℝ)) /
        ENNReal.ofReal (μ ^ 2 / 2) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_div_of_pos (by positivity : 0 < μ ^ 2 / 2)]
      congr 1
      field_simp

/-- The requested linear-mass expression follows from the elementary pair
bound whenever the product of the two cardinalities is small enough. -/
theorem exists_area_constant_of_card_product : ∃ C : ℝ, 0 < C ∧
    ∀ {n : ℕ} {q : Fin n → EuclideanSpace ℝ (Fin 3)} {g : Fin n → ℝ → ℝ},
      JetControlled q g → (∀ i, ContDiff ℝ 2 (g i)) →
    ∀ (A B : Finset (Fin n)) (δ τ a K μ : ℝ), 0 < δ → 0 ≤ K → 0 < μ →
      (∀ i ∈ A, ∀ j ∈ B, 1000 * δ < dist (q i) (q j)) →
      (A.card : ℝ) * (B.card : ℝ) ≤
        δ ^ (-5 * τ) * K ^ a * μ * ((A.card : ℝ) + (B.card : ℝ)) →
      volume {p | ENNReal.ofReal μ ≤ finiteMultiplicity A δ g p ∧
        ENNReal.ofReal μ ≤ finiteMultiplicity B δ g p ∧
        transverseMultiplicity A B δ (δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ))) q g p <
          ENNReal.ofReal (μ ^ 2 / 100)} ≤
        ENNReal.ofReal (C * δ ^ (-τ) * K ^ a * δ *
          ((A.card : ℝ) + (B.card : ℝ)) * μ ^ (-(3 / 2 : ℝ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_restricted_pair_area_constant
  refine ⟨C, hC, ?_⟩
  intro n q g hjet hg A B δ τ a K μ hδ hK hμ hfar hcard
  apply (hbound hjet hg A B δ (δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ))) μ
    hδ (by positivity) hμ hfar).trans
  apply ENNReal.ofReal_le_ofReal
  have hd : δ ^ (4 * τ) * δ ^ (-5 * τ) = δ ^ (-τ) := by
    rw [← Real.rpow_add hδ]
    congr 1
    ring
  have hm : μ ^ (-(1 / 2 : ℝ)) * μ / μ ^ 2 = μ ^ (-(3 / 2 : ℝ)) := by
    calc
      μ ^ (-(1 / 2 : ℝ)) * μ / μ ^ 2 =
          μ ^ (-(1 / 2 : ℝ)) * μ ^ (1 : ℝ) / μ ^ (2 : ℝ) := by
            rw [Real.rpow_one, Real.rpow_two]
      _ = μ ^ (-(1 / 2 : ℝ) + 1 - 2) := by
        rw [Real.rpow_sub hμ, Real.rpow_add hμ]
      _ = _ := by norm_num
  calc
    C * δ * (δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ))) * (A.card : ℝ) * (B.card : ℝ) / μ ^ 2 =
        (C * δ * (δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ))) / μ ^ 2) *
          ((A.card : ℝ) * (B.card : ℝ)) := by ring
    _ ≤ (C * δ * (δ ^ (4 * τ) * μ ^ (-(1 / 2 : ℝ))) / μ ^ 2) *
        (δ ^ (-5 * τ) * K ^ a * μ * ((A.card : ℝ) + (B.card : ℝ))) :=
      mul_le_mul_of_nonneg_left hcard (by positivity)
    _ = C * (δ ^ (4 * τ) * δ ^ (-5 * τ)) * K ^ a * δ *
        ((A.card : ℝ) + (B.card : ℝ)) * (μ ^ (-(1 / 2 : ℝ)) * μ / μ ^ 2) := by ring
    _ = _ := by rw [hd, hm]

/-- A bound on the smaller color is enough for the preceding product condition. -/
theorem card_product_le_of_min_le {ι : Type*} (A B : Finset ι) {H : ℝ}
    (h : min (A.card : ℝ) (B.card : ℝ) ≤ H) :
    (A.card : ℝ) * (B.card : ℝ) ≤ H * ((A.card : ℝ) + (B.card : ℝ)) := by
  rcases le_total (A.card : ℝ) (B.card : ℝ) with hAB | hBA
  · rw [min_eq_left hAB] at h
    have hH : 0 ≤ H := (Nat.cast_nonneg A.card).trans h
    nlinarith [mul_le_mul_of_nonneg_right h (Nat.cast_nonneg B.card),
      mul_nonneg hH (Nat.cast_nonneg A.card)]
  · rw [min_eq_right hBA] at h
    have hH : 0 ≤ H := (Nat.cast_nonneg B.card).trans h
    nlinarith [mul_le_mul_of_nonneg_left h (Nat.cast_nonneg A.card),
      mul_nonneg hH (Nat.cast_nonneg B.card)]

end WangZahlLot.Obl.wz_jet_bipartite_rich_area
