/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, ScalarBandPreparation.lean.
   Original source attributions below are retained. -/

import Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof.HeavyCoefficientCover
import Submission.Obl.k4_initial_horizon_bound.Duration

/-! Adapted from our LOT tree o107 (`k4_finite_narrowness_path_improvement`), session x0353,
`ScalarBandPreparation.lean` (commit 96bcaa7b); namespace and import paths renamed. -/

/-! Integrated scalar bands give coefficient caps for a retained part of the
original trajectory prior. This closes the duration input of scalar clustering. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set
open scoped ENNReal Classical
open Submission.Obl.k4_scalar_coefficient_clustering

/-- A coefficient ball lies in the corresponding polynomial band throughout
the active unit-time window. Division uses an original-prior duration floor. -/
theorem retained_coefficient_ball_cap_from_active_band
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (a : α → EuclideanSpace ℝ (Fin 3)) (ha : Measurable a)
    (E : Set (α × ℝ)) (hE : MeasurableSet E)
    (hunit : E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1)
    (τ : ℝ≥0∞) (hτ0 : τ ≠ 0) (hτtop : τ ≠ ∞)
    (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ) (B : ℝ≥0∞)
    (hband : ((ν.prod volume).restrict E)
      {p | |quadratic (a p.1) p.2 - quadratic b p.2| ≤ 3 * r} ≤ B) :
    (ν.restrict {l | τ ≤ volume {t : ℝ | (l, t) ∈ E}})
      {l | a l ∈ Metric.ball b r} ≤ B / τ := by
  let S : Set α := {l | τ ≤ volume {t : ℝ | (l, t) ∈ E}}
  let C : Set α := {l | a l ∈ Metric.ball b r}
  let Band : Set (α × ℝ) :=
    {p | |quadratic (a p.1) p.2 - quadratic b p.2| ≤ 3 * r}
  have hS : MeasurableSet S := measurableSet_le measurable_const
    (measurable_measure_prodMk_left hE)
  have hC : MeasurableSet C := ha measurableSet_ball
  have hBand : MeasurableSet Band := by
    dsimp [Band, quadratic]
    measurability
  have hprior := Submission.Obl.k4_initial_horizon_bound.retained_duration_prior_bound
    ν hE hC hS τ (fun l hl => hl.2)
  have hinc : (ν.withDensity
      (Submission.Obl.k4_initial_horizon_bound.incidenceDuration E)) C ≤ B := by
    rw [Submission.Obl.k4_initial_horizon_bound.duration_withDensity_apply ν hE hC]
    calc
      _ ≤ (ν.prod volume) (Band ∩ E) := measure_mono (by
        rintro ⟨l, t⟩ ⟨hlt, hl, _⟩
        refine ⟨?_, hlt⟩
        have hdiff := quadratic_difference_le (a := a l) (b := b) ((hunit hlt).2)
        have hnorm : ‖a l - b‖ < r := by
          simpa only [C, Set.mem_ofPred_eq, Metric.mem_ball, dist_eq_norm] using hl
        exact hdiff.trans (by linarith))
      _ = ((ν.prod volume).restrict E) Band := (Measure.restrict_apply hBand).symm
      _ ≤ B := hband
  exact (ENNReal.le_div_iff_mul_le (Or.inl hτ0) (Or.inl hτtop)).mpr
    (by simpa only [mul_comm] using hprior.trans hinc)

/-- The omitted mass is charged to the unchanged prior, and is valid before
any scalar clustering or normalization. -/
theorem short_active_duration_omission
    {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    (E : Set (α × ℝ)) (hE : MeasurableSet E) (τ : ℝ≥0∞) :
    ((ν.prod volume).restrict E)
      ({l | τ ≤ volume {t : ℝ | (l, t) ∈ E}}ᶜ ×ˢ Set.univ) ≤ τ * ν Set.univ := by
  have hshort : MeasurableSet {l | volume {t : ℝ | (l, t) ∈ E} < τ} :=
    measurableSet_lt (measurable_measure_prodMk_left hE) measurable_const
  have hcompl : {l | τ ≤ volume {t : ℝ | (l, t) ∈ E}}ᶜ =
      {l | volume {t : ℝ | (l, t) ∈ E} < τ} := by
    ext l
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
  rw [hcompl, Measure.restrict_apply (hshort.prod MeasurableSet.univ), Set.inter_comm]
  rw [← Submission.Obl.k4_initial_horizon_bound.duration_withDensity_apply ν hE hshort]
  exact Submission.Obl.k4_initial_horizon_bound.short_duration_mass_le ν hE τ

/-- Active polynomial-band caps suffice for a heavy full-time coefficient
cover. The duration cutoff is internal, and both the heavy-bin floors and
the excluded mass refer to the original unnormalized product law. -/
theorem scalar_heavy_coefficient_cover_of_active_bands (d c ε : ℝ)
    (hd : 0 ≤ d) (hd1 : d < 1) (hc : 0 < c) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (α : Type) [MeasurableSpace α] (ν : Measure α)
        (a : α → EuclideanSpace ℝ (Fin 3)) (E : Set (α × ℝ)) (F : Finset (ℤ × ℤ)),
      Measurable a → MeasurableSet E → E ⊆ Set.univ ×ˢ Set.Icc (0 : ℝ) 1 →
      (∀ l, ‖a l‖ ≤ N ^ η) → ν Set.univ ≤ ENNReal.ofReal (N ^ η) →
      (F.card : ℝ) ≤ N ^ η * (N ^ (-c)) ^ (-1 - d) →
      (∀ l t, (l, t) ∈ E →
        (⌊t / (N ^ (-c))⌋, ⌊quadratic (a l) t / (N ^ (-c))⌋) ∈ F) →
      (∀ (b : EuclideanSpace ℝ (Fin 3)) (r : ℝ), N ^ (-c) ≤ r →
        (∃ l, a l ∈ Metric.ball b r) →
        ((ν.prod volume).restrict E)
          {p | |quadratic (a p.1) p.2 - quadratic b p.2| ≤ 3 * r} ≤
            ENNReal.ofReal (N ^ η * r ^ d)) →
      ∃ G : Finset (Fin 3 → ℤ),
        (∀ q ∈ G, ENNReal.ofReal (N ^ (-c * d - ε)) ≤
          ((ν.prod volume).restrict E) {p | coefficientCode (N ^ (-c)) (a p.1) = q}) ∧
        (G.card : ℝ) ≤ (ν.prod volume).real E / N ^ (-c * d - ε) ∧
        ((ν.prod volume).restrict E) {p | coefficientCode (N ^ (-c)) (a p.1) ∉ G} <
          ENNReal.ofReal (N ^ (-η)) := by
  obtain ⟨η₀, hη₀, M, hM, hcover⟩ := scalar_heavy_coefficient_cover d c ε hd hd1 hc hε
  let η := η₀ / 16
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨R, hR⟩ := Filter.eventually_atTop.mp
    ((Filter.tendsto_atTop.mp (tendsto_rpow_atTop (by positivity : 0 < 2 * η))) (3 : ℝ))
  refine ⟨η, hη, max M R, hM.trans (le_max_left _ _), ?_⟩
  intro N hN α _ ν a E F ha hE hunit hnorm hν hcard hsupport hband
  have hNM : M ≤ N := (le_max_left _ _).trans hN
  have hNR : R ≤ N := (le_max_right _ _).trans hN
  have hNpos : 0 < N := by linarith [hM.trans hNM]
  have hN1 : 1 ≤ N := by linarith [hM.trans hNM]
  have hηle : η ≤ η₀ := by dsimp [η]; linarith
  have hη5 : 5 * η ≤ η₀ := by dsimp [η]; linarith
  have hη3 : 3 * η ≤ η₀ := by dsimp [η]; linarith
  have hpow (u v : ℝ) (huv : u ≤ v) : N ^ u ≤ N ^ v :=
    Real.rpow_le_rpow_of_exponent_le hN1 huv
  have hνfinite : ν Set.univ < ∞ := lt_of_le_of_lt hν ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure ν := ⟨hνfinite⟩
  let τ := N ^ (-4 * η)
  have hτ : 0 < τ := Real.rpow_pos_of_pos hNpos _
  let S : Set α := {l | ENNReal.ofReal τ ≤ volume {t : ℝ | (l, t) ∈ E}}
  have hS : MeasurableSet S := measurableSet_le measurable_const
    (measurable_measure_prodMk_left hE)
  let ν' := ν.restrict S
  let μ := (ν.prod volume).restrict E
  let μ' := (ν'.prod volume).restrict E
  have hμ' : μ' = μ.restrict (S ×ˢ Set.univ) := by
    dsimp [μ', μ, ν']
    rw [Measure.restrict_prod_eq_prod_univ, Measure.restrict_restrict hE,
      Measure.restrict_restrict (hS.prod MeasurableSet.univ), Set.inter_comm]
  have hμle : μ' ≤ μ := hμ' ▸ Measure.restrict_le_self
  have hνcap : ν' Set.univ ≤ ENNReal.ofReal (N ^ η₀) := by
    calc
      _ ≤ ν Set.univ := Measure.restrict_le_self _
      _ ≤ ENNReal.ofReal (N ^ η) := hν
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hpow _ _ hηle)
  have hprior : ∀ b : EuclideanSpace ℝ (Fin 3), ∀ r : ℝ, N ^ (-c) ≤ r →
      ν' {l | a l ∈ Metric.ball b r} ≤ ENNReal.ofReal (N ^ η₀ * r ^ d) := by
    intro b r hr
    by_cases hex : ∃ l, a l ∈ Metric.ball b r
    swap
    · have hempty : {l | a l ∈ Metric.ball b r} = ∅ := by
        ext l
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun hl => hex ⟨l, hl⟩
      rw [hempty, measure_empty]
      exact zero_le
    have hr0 : 0 ≤ r := (Real.rpow_nonneg hNpos.le _).trans hr
    have hrd : 0 ≤ r ^ d := Real.rpow_nonneg hr0 _
    have hb := retained_coefficient_ball_cap_from_active_band ν a ha E hE hunit
      (ENNReal.ofReal τ) (ENNReal.ofReal_ne_zero_iff.mpr hτ) ENNReal.ofReal_ne_top b r
      (ENNReal.ofReal (N ^ η * r ^ d)) (hband b r hr hex)
    calc
      _ ≤ ENNReal.ofReal (N ^ η * r ^ d) / ENNReal.ofReal τ := hb
      _ = ENNReal.ofReal (N ^ (5 * η) * r ^ d) := by
        rw [← ENNReal.ofReal_div_of_pos hτ]
        congr 1
        dsimp [τ]
        rw [show -4 * η = -(4 * η) by ring]
        rw [Real.rpow_neg hNpos.le, div_eq_mul_inv, inv_inv]
        rw [show N ^ η * r ^ d * N ^ (4 * η) =
          (N ^ η * N ^ (4 * η)) * r ^ d by ring, ← Real.rpow_add hNpos]
        congr 2
        ring
      _ ≤ _ := ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (hpow _ _ hη5) hrd)
  obtain ⟨G, hfloor, hcount, hexcluded⟩ := hcover N hNM α ν' a E F ha hE hunit
    (fun l => (hnorm l).trans (hpow _ _ hηle)) hνcap
    (hcard.trans (mul_le_mul_of_nonneg_right (hpow _ _ hηle) (by positivity)))
    hsupport hprior
  refine ⟨G, (fun q hq => (hfloor q hq).trans (hμle _)), ?_, ?_⟩
  · apply hcount.trans
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hNpos.le _)
    apply ENNReal.toReal_mono
    · refine ne_of_lt (lt_of_le_of_lt (measure_mono hunit) ?_)
      simpa only [Measure.prod_prod, Real.volume_Icc, sub_zero, ENNReal.ofReal_one,
        mul_one] using hνfinite
    · exact Measure.prod_mono Measure.restrict_le_self le_rfl E
  · let U : Set (α × ℝ) := {p | coefficientCode (N ^ (-c)) (a p.1) ∉ G}
    have hU : MeasurableSet U := by
      exact ((measurable_coefficientCode _).comp (ha.comp measurable_fst))
        (G.measurableSet.compl)
    have hshort : μ (Sᶜ ×ˢ Set.univ) ≤ ENNReal.ofReal (N ^ (-3 * η)) := by
      calc
        _ ≤ ENNReal.ofReal τ * ν Set.univ := short_active_duration_omission ν E hE _
        _ ≤ ENNReal.ofReal τ * ENNReal.ofReal (N ^ η) :=
          mul_le_mul_of_nonneg_left hν (zero_le : (0 : ℝ≥0∞) ≤ _)
        _ = _ := by
          rw [← ENNReal.ofReal_mul hτ.le]
          congr 1
          dsimp [τ]
          rw [← Real.rpow_add hNpos]
          congr 1
          ring
    have hbad : μ U ≤ μ' U + μ (Sᶜ ×ˢ Set.univ) := by
      calc
        _ ≤ μ ((U ∩ (S ×ˢ Set.univ)) ∪ (Sᶜ ×ˢ Set.univ)) := measure_mono (by
          intro p hp
          by_cases hps : p.1 ∈ S
          · exact Or.inl ⟨hp, hps, Set.mem_univ _⟩
          · exact Or.inr ⟨hps, Set.mem_univ _⟩)
        _ ≤ μ (U ∩ (S ×ˢ Set.univ)) + μ (Sᶜ ×ˢ Set.univ) := measure_union_le _ _
        _ = _ := by rw [hμ', Measure.restrict_apply hU]
    have hsmall : 2 * N ^ (-3 * η) < N ^ (-η) := by
      have hh := mul_le_mul_of_nonneg_right (hR N hNR)
        (Real.rpow_nonneg hNpos.le (-3 * η))
      have heq : N ^ (2 * η) * N ^ (-3 * η) = N ^ (-η) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        ring
      rw [heq] at hh
      linarith [Real.rpow_pos_of_pos hNpos (-3 * η)]
    have hupper : μ U ≤ ENNReal.ofReal (2 * N ^ (-3 * η)) := by
      calc
        _ ≤ ENNReal.ofReal (N ^ (-η₀)) + ENNReal.ofReal (N ^ (-3 * η)) :=
          hbad.trans (add_le_add hexcluded.le hshort)
        _ ≤ ENNReal.ofReal (N ^ (-3 * η)) + ENNReal.ofReal (N ^ (-3 * η)) := by
          exact add_le_add (ENNReal.ofReal_le_ofReal (hpow _ _ (by linarith))) le_rfl
        _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    exact hupper.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      (Real.rpow_pos_of_pos hNpos _)).mpr hsmall)

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
