import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.RowFit

/-!
# Preparing the labels of the first jet

* `Data.mono`: the hypotheses of `FirstJet.Data` persist under a larger constant `K' ≥ K` and
  under restriction of the labels to a measurable `E' ⊆ E` of mass `≥ 1/K'`.
* `prepare_labels`: from labels of mass `δ`, keep the trajectories whose labeled duration is
  `≥ δ/4` and the times whose labeled mass is `≥ δ/4`; the result keeps mass `≥ δ/2`.
* `exists_heavy_block`: among `n` blocks of length `1/n`, one carries mass `≥ m/n`.
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The hypotheses persist under a larger constant and restricted labels. -/
theorem Data.mono {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E E' : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K K' ζ : ℝ} (h : Data ν y β γ E F d K ζ) (hKK : K ≤ K')
    (hζ : 0 < ζ) (hE' : MeasurableSet E') (hsub : E' ⊆ E)
    (hmass : ENNReal.ofReal K'⁻¹ ≤ (ν.prod volume) E') :
    Data ν y β γ E' F d K' ζ where
  measurable_y := h.measurable_y
  measurable_β := h.measurable_β
  measurable_γ := h.measurable_γ
  measurable_F := h.measurable_F
  measurableSet_E := hE'
  subset_E := hsub.trans h.subset_E
  bound_y l i := (h.bound_y l i).trans hKK
  bound_β l := (h.bound_β l).trans hKK
  bound_γ l := (h.bound_γ l).trans hKK
  bound_F t i := (h.bound_F t i).trans hKK
  mass := hmass
  support t q r a hq hqr hr := by
    obtain ⟨C, hC, hmem⟩ := h.support t q r a hq hqr hr
    refine ⟨C, hC.trans ?_, fun l hl => hmem l (hsub hl)⟩
    have hq0 : 0 < q := hζ.trans_le hq
    exact mul_le_mul_of_nonneg_right hKK (Real.rpow_nonneg (div_nonneg (hq0.le.trans hqr) hq0.le) _)
  absCap t q hq hq1 z := by
    refine (measure_mono ?_).trans ((h.absCap t q hq hq1 z).trans (ENNReal.ofReal_le_ofReal ?_))
    · rintro l ⟨hl, h1⟩; exact ⟨hsub hl, h1⟩
    · exact mul_le_mul_of_nonneg_right hKK (Real.rpow_nonneg (hζ.le.trans hq) _)
  rowLip t u ht hu i := by
    obtain ⟨l, hl⟩ := ht
    obtain ⟨l', hl'⟩ := hu
    refine (h.rowLip t u ⟨l, hsub hl⟩ ⟨l', hsub hl'⟩ i).trans ?_
    exact mul_le_mul_of_nonneg_right hKK (by have := abs_nonneg (t - u); linarith)
  slopeLip l l' t u hl hl' := by
    refine (h.slopeLip l l' t u (hsub hl) (hsub hl')).trans ?_
    refine mul_le_mul_of_nonneg_right hKK ?_
    have := abs_nonneg (t - u); have := abs_nonneg (xbar β γ l t - xbar β γ l' u)
    have := abs_nonneg (y l 0 - y l' 0); have := abs_nonneg (y l 1 - y l' 1)
    linarith
  binCap q n hq hqn b t z := by
    refine (measure_mono ?_).trans ((h.binCap q n hq hqn b t z).trans ?_)
    · rintro l ⟨hb, hl, h1⟩; exact ⟨hb, hsub hl, h1⟩
    · have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(n : ℤ)) := zpow_nonneg (by norm_num) _
      exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hKK
        (Real.rpow_nonneg (div_nonneg (hζ.le.trans hq) h2) _))) bot_le

/-- The labeled duration of a trajectory. -/
def duration (E : Set (Ω × ℝ)) (l : Ω) : ENNReal := volume {t | (l, t) ∈ E}

theorem measurable_duration {E : Set (Ω × ℝ)} (hE : MeasurableSet E) :
    Measurable (duration E) :=
  measurable_measure_prodMk_left hE

theorem measurable_timeMass {ν : Measure Ω} [SFinite ν] {E : Set (Ω × ℝ)}
    (hE : MeasurableSet E) : Measurable (timeMass ν E) :=
  measurable_measure_prodMk_right hE

/-- Keep the trajectories of labeled duration `≥ δ/4` and the times of labeled mass `≥ δ/4`. -/
def prepared (ν : Measure Ω) (E : Set (Ω × ℝ)) (δ : ℝ) : Set (Ω × ℝ) :=
  let Λ : Set Ω := {l | ENNReal.ofReal (δ / 4) ≤ duration E l}
  let E₁ : Set (Ω × ℝ) := E ∩ Λ ×ˢ univ
  E₁ ∩ univ ×ˢ {t | ENNReal.ofReal (δ / 4) ≤ timeMass ν E₁ t}

theorem prepared_subset (ν : Measure Ω) (E : Set (Ω × ℝ)) (δ : ℝ) : prepared ν E δ ⊆ E :=
  fun _ h => h.1.1

theorem measurableSet_prepared {ν : Measure Ω} [SFinite ν] {E : Set (Ω × ℝ)}
    (hE : MeasurableSet E) (δ : ℝ) : MeasurableSet (prepared ν E δ) := by
  have hΛ : MeasurableSet {l : Ω | ENNReal.ofReal (δ / 4) ≤ duration E l} :=
    measurableSet_le measurable_const (measurable_duration hE)
  have hE₁ : MeasurableSet (E ∩ {l : Ω | ENNReal.ofReal (δ / 4) ≤ duration E l} ×ˢ univ) :=
    hE.inter (hΛ.prod MeasurableSet.univ)
  exact hE₁.inter (MeasurableSet.univ.prod
    (measurableSet_le measurable_const (measurable_timeMass hE₁)))

/-- Every prepared trajectory has labeled duration `≥ δ/4` in the original labels. -/
theorem duration_of_mem_prepared {ν : Measure Ω} {E : Set (Ω × ℝ)} {δ : ℝ} {l : Ω} {t : ℝ}
    (h : (l, t) ∈ prepared ν E δ) : ENNReal.ofReal (δ / 4) ≤ duration E l :=
  h.1.2.1

/-- Every prepared time carries prepared labeled mass `≥ δ/4`. -/
theorem timeMass_of_mem_prepared {ν : Measure Ω} {E : Set (Ω × ℝ)} {δ : ℝ} {l : Ω} {t : ℝ}
    (h : (l, t) ∈ prepared ν E δ) : ENNReal.ofReal (δ / 4) ≤ timeMass ν (prepared ν E δ) t := by
  have ht : ENNReal.ofReal (δ / 4) ≤
      timeMass ν (E ∩ {l : Ω | ENNReal.ofReal (δ / 4) ≤ duration E l} ×ˢ univ) t := h.2.2
  refine ht.trans (le_of_eq ?_)
  unfold timeMass prepared
  congr 1
  ext l'
  simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_univ, and_true, true_and]
  constructor
  · intro hl'; exact ⟨hl', ht⟩
  · intro hl'; exact hl'.1

/-- The prepared labels keep at least half of the mass. -/
theorem prepared_mass {ν : Measure Ω} [IsProbabilityMeasure ν] {E : Set (Ω × ℝ)}
    (hE : MeasurableSet E) (hE01 : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {δ : ℝ} (hδ : 0 ≤ δ)
    (hmass : ENNReal.ofReal δ ≤ (ν.prod volume) E) :
    ENNReal.ofReal (δ / 2) ≤ (ν.prod volume) (prepared ν E δ) := by
  set Λ : Set Ω := {l | ENNReal.ofReal (δ / 4) ≤ duration E l} with hΛdef
  have hΛ : MeasurableSet Λ := measurableSet_le measurable_const (measurable_duration hE)
  set E₁ : Set (Ω × ℝ) := E ∩ Λ ×ˢ univ with hE₁def
  have hE₁ : MeasurableSet E₁ := hE.inter (hΛ.prod MeasurableSet.univ)
  set Td : Set ℝ := {t | ENNReal.ofReal (δ / 4) ≤ timeMass ν E₁ t} with hTd
  have hTdm : MeasurableSet Td := measurableSet_le measurable_const (measurable_timeMass hE₁)
  -- short trajectories carry at most `δ/4`
  have hshort : (ν.prod volume) (E ∩ Λᶜ ×ˢ univ) ≤ ENNReal.ofReal (δ / 4) := by
    rw [Measure.prod_apply (hE.inter (hΛ.compl.prod MeasurableSet.univ))]
    calc ∫⁻ l, volume (Prod.mk l ⁻¹' (E ∩ Λᶜ ×ˢ univ)) ∂ν
        ≤ ∫⁻ _l, ENNReal.ofReal (δ / 4) ∂ν := by
          refine lintegral_mono (fun l => ?_)
          show volume (Prod.mk l ⁻¹' (E ∩ Λᶜ ×ˢ univ)) ≤ ENNReal.ofReal (δ / 4)
          by_cases hl : l ∈ Λ
          · have : Prod.mk l ⁻¹' (E ∩ Λᶜ ×ˢ univ) = ∅ := by
              ext t; simp [hl]
            rw [this, measure_empty]; exact bot_le
          · have hsl : Prod.mk l ⁻¹' (E ∩ Λᶜ ×ˢ univ) = {t | (l, t) ∈ E} := by
              ext t; simp [hl]
            rw [hsl]
            simp only [hΛdef, mem_ofPred_eq, not_le] at hl
            exact hl.le
      _ = ENNReal.ofReal (δ / 4) := by rw [lintegral_const, measure_univ, mul_one]
  -- sparse times carry at most `δ/4`
  have hsparse : (ν.prod volume) (E₁ ∩ univ ×ˢ Tdᶜ) ≤ ENNReal.ofReal (δ / 4) := by
    rw [Measure.prod_apply_symm (hE₁.inter (MeasurableSet.univ.prod hTdm.compl))]
    calc ∫⁻ t, ν ((fun l => (l, t)) ⁻¹' (E₁ ∩ univ ×ˢ Tdᶜ))
        ≤ ∫⁻ t, (Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (δ / 4)) t := by
          refine lintegral_mono (fun t => ?_)
          show ν ((fun l => (l, t)) ⁻¹' (E₁ ∩ univ ×ˢ Tdᶜ)) ≤
            (Icc (0 : ℝ) 1).indicator (fun _ => ENNReal.ofReal (δ / 4)) t
          by_cases ht : t ∈ Td
          · have : (fun l => (l, t)) ⁻¹' (E₁ ∩ univ ×ˢ Tdᶜ) = ∅ := by
              ext l; simp [ht]
            rw [this, measure_empty]; exact bot_le
          · by_cases ht01 : t ∈ Icc (0 : ℝ) 1
            · rw [indicator_of_mem ht01]
              have hsl : (fun l => (l, t)) ⁻¹' (E₁ ∩ univ ×ˢ Tdᶜ) = {l | (l, t) ∈ E₁} := by
                ext l; simp [ht]
              rw [hsl]
              simp only [hTd, mem_ofPred_eq, not_le] at ht
              exact ht.le
            · have : (fun l => (l, t)) ⁻¹' (E₁ ∩ univ ×ˢ Tdᶜ) = ∅ := by
                ext l
                simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, true_and,
                  mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
                intro hl _
                exact ht01 (hE01 hl.1).2
              rw [this, measure_empty]; exact bot_le
      _ = ENNReal.ofReal (δ / 4) := by
          rw [lintegral_indicator_const measurableSet_Icc, Real.volume_Icc]
          simp
  -- combine
  have hcover : E ⊆ prepared ν E δ ∪ (E ∩ Λᶜ ×ˢ univ) ∪ (E₁ ∩ univ ×ˢ Tdᶜ) := by
    intro q hq
    by_cases hl : q.1 ∈ Λ
    · by_cases ht : q.2 ∈ Td
      · left; left; exact ⟨⟨hq, hl, trivial⟩, trivial, ht⟩
      · right; exact ⟨⟨hq, hl, trivial⟩, trivial, ht⟩
    · left; right; exact ⟨hq, hl, trivial⟩
  have htot : ENNReal.ofReal δ ≤ (ν.prod volume) (prepared ν E δ) +
      ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) :=
    hmass.trans ((measure_mono hcover).trans ((measure_union_le _ _).trans
      (add_le_add ((measure_union_le _ _).trans (add_le_add le_rfl hshort)) hsparse)))
  have hsplit : ENNReal.ofReal δ = ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 4) +
      ENNReal.ofReal (δ / 4) := by
    rw [← ENNReal.ofReal_add (by positivity) (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    congr 1; ring
  rw [hsplit] at htot
  have hfin : ENNReal.ofReal (δ / 4) + ENNReal.ofReal (δ / 4) ≠ ⊤ := by simp
  rw [add_assoc, add_assoc] at htot
  exact (ENNReal.add_le_add_iff_right hfin).mp htot

/-- One of `n` consecutive blocks of length `1/n` carries at least a `1/n` share. -/
theorem exists_heavy_block {ν : Measure Ω} {E : Set (Ω × ℝ)}
    (hE01 : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {n : ℕ} (hn : 0 < n) {m : ENNReal}
    (hmass : m ≤ (ν.prod volume) E) :
    ∃ j : ℕ, j < n ∧ m / n ≤
      (ν.prod volume) (E ∩ univ ×ˢ Icc ((j : ℝ) / n) (((j : ℝ) + 1) / n)) := by
  by_contra hcon
  push Not at hcon
  have hcover : E ⊆ ⋃ j ∈ Finset.range n,
      E ∩ univ ×ˢ Icc ((j : ℝ) / n) (((j : ℝ) + 1) / n) := by
    intro q hq
    have ht := (hE01 hq).2
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    set j : ℕ := min ⌊q.2 * n⌋₊ (n - 1) with hj
    have hjn : j < n := by omega
    refine mem_iUnion₂.mpr ⟨j, Finset.mem_range.mpr hjn, hq, trivial, ?_⟩
    have h0 : 0 ≤ q.2 * n := mul_nonneg ht.1 hn'.le
    constructor
    · rw [div_le_iff₀ hn']
      calc (j : ℝ) ≤ ⌊q.2 * n⌋₊ := by exact_mod_cast min_le_left _ _
        _ ≤ q.2 * n := Nat.floor_le h0
    · rw [le_div_iff₀ hn']
      by_cases hc : ⌊q.2 * n⌋₊ ≤ n - 1
      · have : j = ⌊q.2 * n⌋₊ := by omega
        rw [this]
        exact (Nat.lt_floor_add_one _).le
      · have : j = n - 1 := by omega
        rw [this]
        have : ((n - 1 : ℕ) : ℝ) + 1 = n := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        rw [this]
        nlinarith [ht.2]
  have hsum := (measure_mono (μ := ν.prod volume) hcover).trans
    (measure_biUnion_finset_le (Finset.range n) _)
  have hlt : ∑ j ∈ Finset.range n,
      (ν.prod volume) (E ∩ univ ×ˢ Icc ((j : ℝ) / n) (((j : ℝ) + 1) / n)) <
      ∑ _j ∈ Finset.range n, m / n :=
    ENNReal.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hn⟩ (fun j hj =>
      hcon j (Finset.mem_range.mp hj))
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlt
  have hmn : (n : ENNReal) * (m / n) ≤ m := by
    rw [ENNReal.mul_div_cancel (by exact_mod_cast hn.ne') (by simp)]
  exact absurd (lt_of_le_of_lt (hmass.trans hsum) hlt) (not_lt.mpr hmn)

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
