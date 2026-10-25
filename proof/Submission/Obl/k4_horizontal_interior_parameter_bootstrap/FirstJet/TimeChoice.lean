import Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet.Slab

/-!
# Choosing the reading time

On a set `T` of times, each carrying labeled mass `≥ m`, the duration `durT l` of a
trajectory's labels inside `T` satisfies `∫ durT² ≥ (m |T|)²` (Cauchy–Schwarz, `ν` a
probability), so some `t* ∈ T` has `∫_{labeled at t*} durT ≥ m² |T|` (`exists_reading_time`).
-/

open MeasureTheory Set

noncomputable section

namespace Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The labeled duration of a trajectory inside the time set `T`. -/
def durIn (E : Set (Ω × ℝ)) (T : Set ℝ) (l : Ω) : ENNReal := volume {t | t ∈ T ∧ (l, t) ∈ E}

theorem measurable_durIn {E : Set (Ω × ℝ)} (hE : MeasurableSet E) {T : Set ℝ}
    (hT : MeasurableSet T) : Measurable (durIn E T) := by
  have : MeasurableSet (E ∩ univ ×ˢ T) := hE.inter (MeasurableSet.univ.prod hT)
  have h := measurable_measure_prodMk_left (ν := volume) this
  convert h using 2 with l
  unfold durIn
  congr 1
  ext t
  simp [and_comm]

/-- `∫ durT = ∫_T labeled mass`. -/
theorem lintegral_durIn {ν : Measure Ω} [SFinite ν] {E : Set (Ω × ℝ)} (hE : MeasurableSet E)
    {T : Set ℝ} (hT : MeasurableSet T) :
    ∫⁻ l, durIn E T l ∂ν = ∫⁻ t in T, timeMass ν E t := by
  have hET : MeasurableSet (E ∩ univ ×ˢ T) := hE.inter (MeasurableSet.univ.prod hT)
  have h1 := Measure.prod_apply (μ := ν) (ν := volume) hET
  have h2 := Measure.prod_apply_symm (μ := ν) (ν := volume) hET
  have e1 : ∫⁻ l, durIn E T l ∂ν = ∫⁻ l, volume (Prod.mk l ⁻¹' (E ∩ univ ×ˢ T)) ∂ν := by
    congr 1; ext l; unfold durIn; congr 1; ext t; simp [and_comm]
  have e2 : ∫⁻ t in T, timeMass ν E t =
      ∫⁻ t, ν ((fun l => (l, t)) ⁻¹' (E ∩ univ ×ˢ T)) := by
    rw [← lintegral_indicator hT]
    congr 1; ext t
    by_cases ht : t ∈ T
    · rw [indicator_of_mem ht]; unfold timeMass; congr 1; ext l; simp [ht]
    · rw [indicator_of_notMem ht]
      have : (fun l => (l, t)) ⁻¹' (E ∩ univ ×ˢ T) = ∅ := by ext l; simp [ht]
      rw [this, measure_empty]
  rw [e1, e2, ← h1, ← h2]

/-- Cauchy–Schwarz for a probability measure in `ℝ≥0∞`. -/
theorem sq_lintegral_le_lintegral_sq {ν : Measure Ω} [IsProbabilityMeasure ν] {g : Ω → ENNReal}
    (hg : Measurable g) : (∫⁻ l, g l ∂ν) ^ 2 ≤ ∫⁻ l, g l ^ 2 ∂ν := by
  have hpq : (2:ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν hpq hg.aemeasurable
    (aemeasurable_const (b := (1 : ENNReal)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ,
    ENNReal.one_rpow] at h
  have h3 : (∫⁻ x, g x ∂ν) ^ (2:ℝ) ≤ ((∫⁻ x, g x ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ))) ^ (2:ℝ) := by
    apply ENNReal.rpow_le_rpow _ (by norm_num)
    simpa using h
  rw [← ENNReal.rpow_mul] at h3
  norm_num at h3
  have e : ∀ x : ENNReal, x ^ (2:ℝ) = x ^ (2:ℕ) := fun x => by
    rw [← ENNReal.rpow_natCast]; norm_num
  simpa [e] using h3

/-- Some time of `T` sees labeled trajectories of total `T`-duration `≥ m² |T|`. -/
theorem exists_reading_time {ν : Measure Ω} [IsProbabilityMeasure ν] {E : Set (Ω × ℝ)}
    (hE : MeasurableSet E) {T : Set ℝ} (hT : MeasurableSet T) (hTfin : volume T ≠ ⊤)
    (hT0 : volume T ≠ 0) {m : ENNReal} (hm : ∀ t ∈ T, m ≤ timeMass ν E t) :
    ∃ t ∈ T, m ^ 2 * volume T ≤ ∫⁻ l, {l | (l, t) ∈ E}.indicator (durIn E T) l ∂ν := by
  by_contra hcon
  push Not at hcon
  have hd := measurable_durIn hE hT
  -- the time integral of the inner integral is `∫ durT²`
  have hfub : ∫⁻ t in T, ∫⁻ l, {l | (l, t) ∈ E}.indicator (durIn E T) l ∂ν =
      ∫⁻ l, durIn E T l ^ 2 ∂ν := by
    have hf : Measurable (fun q : Ω × ℝ => (E ∩ univ ×ˢ T).indicator
        (fun q : Ω × ℝ => durIn E T q.1) q) :=
      (hd.comp measurable_fst).indicator (hE.inter (MeasurableSet.univ.prod hT))
    have hmeas : Measurable (fun p : ℝ × Ω => (E ∩ univ ×ˢ T).indicator
        (fun q : Ω × ℝ => durIn E T q.1) (p.2, p.1)) :=
      hf.comp (measurable_snd.prodMk measurable_fst)
    have e1 : ∫⁻ t in T, ∫⁻ l, {l | (l, t) ∈ E}.indicator (durIn E T) l ∂ν =
        ∫⁻ t, ∫⁻ l, (E ∩ univ ×ˢ T).indicator (fun q : Ω × ℝ => durIn E T q.1) (l, t) ∂ν := by
      rw [← lintegral_indicator hT]
      congr 1; ext t
      by_cases ht : t ∈ T
      · rw [indicator_of_mem ht]
        congr 1; ext l
        by_cases hl : (l, t) ∈ E
        · rw [indicator_of_mem (show l ∈ {l | (l, t) ∈ E} from hl),
            indicator_of_mem (show (l, t) ∈ E ∩ univ ×ˢ T from ⟨hl, trivial, ht⟩)]
        · rw [indicator_of_notMem (show l ∉ {l | (l, t) ∈ E} from hl),
            indicator_of_notMem (show (l, t) ∉ E ∩ univ ×ˢ T from fun h => hl h.1)]
      · rw [indicator_of_notMem ht]
        symm
        apply lintegral_eq_zero_of_ae_eq_zero
        filter_upwards with l
        exact indicator_of_notMem (fun h => ht h.2.2) _
    rw [e1, lintegral_lintegral_swap (hmeas.aemeasurable)]
    congr 1; ext l
    have : ∫⁻ t, (E ∩ univ ×ˢ T).indicator (fun q : Ω × ℝ => durIn E T q.1) (l, t) =
        durIn E T l * durIn E T l := by
      have hset : MeasurableSet {t | t ∈ T ∧ (l, t) ∈ E} :=
        hT.inter (measurable_prodMk_left hE)
      calc ∫⁻ t, (E ∩ univ ×ˢ T).indicator (fun q : Ω × ℝ => durIn E T q.1) (l, t)
          = ∫⁻ t, {t | t ∈ T ∧ (l, t) ∈ E}.indicator (fun _ => durIn E T l) t := by
            congr 1; ext t
            by_cases h : t ∈ T ∧ (l, t) ∈ E
            · rw [indicator_of_mem (show (l, t) ∈ E ∩ univ ×ˢ T from ⟨h.2, trivial, h.1⟩),
                indicator_of_mem (show t ∈ {t | t ∈ T ∧ (l, t) ∈ E} from h)]
            · rw [indicator_of_notMem (show (l, t) ∉ E ∩ univ ×ˢ T from
                fun h' => h ⟨h'.2.2, h'.1⟩), indicator_of_notMem
                (show t ∉ {t | t ∈ T ∧ (l, t) ∈ E} from h)]
        _ = durIn E T l * volume {t | t ∈ T ∧ (l, t) ∈ E} := lintegral_indicator_const hset _
        _ = durIn E T l * durIn E T l := rfl
    rw [this, sq]
  -- lower bound for `∫ durT²`
  have hlow : (m * volume T) ^ 2 ≤ ∫⁻ l, durIn E T l ^ 2 ∂ν := by
    refine le_trans ?_ (sq_lintegral_le_lintegral_sq hd)
    gcongr
    rw [lintegral_durIn hE hT]
    calc m * volume T = ∫⁻ _t in T, m := by rw [setLIntegral_const, mul_comm]
      _ ≤ ∫⁻ t in T, timeMass ν E t := setLIntegral_mono (measurable_timeMass hE) hm
  -- upper bound from the contrary hypothesis
  have hup : ∫⁻ t in T, ∫⁻ l, {l | (l, t) ∈ E}.indicator (durIn E T) l ∂ν <
      ∫⁻ _t in T, m ^ 2 * volume T := by
    apply setLIntegral_strict_mono hT hT0 measurable_const
    · -- the left integral is finite: the inner integral is at most `|T|`
      have hle : ∀ t, ∫⁻ l, {l | (l, t) ∈ E}.indicator (durIn E T) l ∂ν ≤ volume T := by
        intro t
        calc ∫⁻ l, {l | (l, t) ∈ E}.indicator (durIn E T) l ∂ν ≤ ∫⁻ _l, volume T ∂ν := by
              apply lintegral_mono
              intro l
              by_cases hl : l ∈ {l | (l, t) ∈ E}
              · rw [indicator_of_mem hl]; exact measure_mono (fun t ht => ht.1)
              · rw [indicator_of_notMem hl]; exact bot_le
          _ = volume T := by rw [lintegral_const, measure_univ, mul_one]
      refine ne_top_of_le_ne_top ?_ (setLIntegral_mono measurable_const (fun t _ => hle t))
      rw [setLIntegral_const]
      exact ENNReal.mul_ne_top hTfin hTfin
    · exact Filter.Eventually.of_forall (fun t ht => hcon t ht)
  rw [hfub, setLIntegral_const] at hup
  have : (m * volume T) ^ 2 = m ^ 2 * volume T * volume T := by ring
  rw [this] at hlow
  exact absurd (lt_of_le_of_lt hlow hup) (lt_irrefl _)

end Submission.Obl.k4_horizontal_interior_parameter_bootstrap.FirstJet

end
