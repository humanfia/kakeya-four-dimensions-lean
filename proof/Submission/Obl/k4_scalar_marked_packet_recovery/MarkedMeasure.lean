import Submission.Obl.k4_scalar_marked_packet_recovery.Definitions

namespace Submission.Obl.k4_scalar_marked_packet_recovery

open Set MeasureTheory
open scoped ENNReal

abbrev Coeff := Fin 5 → ℝ
abbrev Label := ℕ × Coeff

/-- A single common coefficient jitter is a probability law. -/
theorem noise_probability {σ : ℝ} (hσ : 0 < σ) : IsProbabilityMeasure (Noise σ) := by
  haveI : IsProbabilityMeasure (ENNReal.ofReal σ⁻¹ • volume.restrict (Icc (0 : ℝ) σ)) := by
    constructor
    simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_inv_of_pos hσ]
    exact ENNReal.inv_mul_cancel (by positivity) ENNReal.ofReal_ne_top
  exact inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

/-- The noise is supported on the coefficient cube. -/
theorem noise_ae_cube {σ : ℝ} (hσ : 0 < σ) :
    ∀ᵐ u ∂Noise σ, ∀ e, u e ∈ Icc (0 : ℝ) σ := by
  haveI := (volume.restrict (Icc (0 : ℝ) σ)).smul_finite
    (c := ENNReal.ofReal σ⁻¹) ENNReal.ofReal_ne_top
  apply (ae_all_iff).mpr
  intro e
  exact Measure.tendsto_eval_ae_ae (i := e) (μ := fun _ : Fin 5 =>
    ENNReal.ofReal σ⁻¹ • volume.restrict (Icc (0 : ℝ) σ))
    (show ∀ᵐ x ∂(ENNReal.ofReal σ⁻¹ • volume.restrict (Icc (0 : ℝ) σ)),
      x ∈ Icc (0 : ℝ) σ from by
        exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_Icc) _)

abbrev embed {H : ℕ} (b₀ : Fin H → Coeff) (j : Fin H) (u : Coeff) : Label :=
  (j.val, b₀ j + u)

theorem measurable_embed {H : ℕ} (b₀ : Fin H → Coeff) (j : Fin H) :
    Measurable (embed b₀ j) :=
  measurable_const.prodMk (measurable_const.add measurable_id)

abbrev timeCell (J : ℕ) (z : Fin J) : Set ℝ :=
  Ico ((z : ℝ) / (J : ℝ)) (((z : ℝ) + 1) / (J : ℝ))

abbrev markTimes {H J : ℕ} (mark : Fin H → Fin J → Bool) (j : Fin H) : Set ℝ :=
  {t | ∃ z : Fin J, mark j z = true ∧ t ∈ timeCell J z}

theorem measurableSet_markTimes {H J : ℕ} (mark : Fin H → Fin J → Bool) (j : Fin H) :
    MeasurableSet (markTimes mark j) := by
  classical
  simp only [markTimes, ofPred_exists, ofPred_and]
  exact .iUnion fun z => (MeasurableSet.const _).inter measurableSet_Ico

theorem measurableSet_markedEvent {H J : ℕ} (mark : Fin H → Fin J → Bool) :
    MeasurableSet (MarkedEvent H J mark) := by
  classical
  unfold MarkedEvent
  measurability

theorem embed_mem_event {H J : ℕ} (b₀ : Fin H → Coeff) (mark : Fin H → Fin J → Bool)
    (j : Fin H) (u : Coeff) (t : ℝ) :
    (embed b₀ j u, t) ∈ MarkedEvent H J mark ↔ t ∈ markTimes mark j := by
  constructor
  · rintro ⟨j', hj', ht⟩
    have hj : j = j' := Fin.ext hj'
    subst j
    exact ht
  · intro ht
    exact ⟨j, rfl, ht⟩

theorem timeCell_subset_unit {J : ℕ} (hJ : 0 < J) (z : Fin J) :
    timeCell J z ⊆ Icc (0 : ℝ) 1 := by
  have hJ' : 0 < (J : ℝ) := by exact_mod_cast hJ
  have hz : (z : ℝ) + 1 ≤ J := by exact_mod_cast z.isLt
  intro t ht
  exact ⟨(div_nonneg (by positivity) hJ'.le).trans ht.1,
    ht.2.le.trans ((div_le_one hJ').2 hz)⟩

theorem markTimes_subset_unit {H J : ℕ} (hJ : 0 < J)
    (mark : Fin H → Fin J → Bool) (j : Fin H) :
    markTimes mark j ⊆ Icc (0 : ℝ) 1 := by
  rintro t ⟨z, _, ht⟩
  exact timeCell_subset_unit hJ z ht

theorem markedEvent_subset_unit {H J : ℕ} (hJ : 0 < J)
    (mark : Fin H → Fin J → Bool) :
    MarkedEvent H J mark ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
  rintro p ⟨j, _, ht⟩
  exact ⟨mem_univ _, markTimes_subset_unit hJ mark j ht⟩

theorem markedPrior_probability {σ : ℝ} (hσ : 0 < σ) {H : ℕ}
    (b₀ : Fin H → Coeff) (w : Fin H → ℝ) (hw : ∀ j, 0 ≤ w j)
    (hw1 : ∑ j, w j = 1) : IsProbabilityMeasure (MarkedPrior σ H b₀ w) := by
  haveI := noise_probability hσ
  constructor
  simp only [MarkedPrior, Measure.finsetSum_apply, MeasurableSet.univ, Measure.smul_apply,
    smul_eq_mul, Measure.map_apply (measurable_embed b₀ _) MeasurableSet.univ,
    preimage_univ, measure_univ, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => hw j), hw1, ENNReal.ofReal_one]

theorem markedLaw_mass_le_one {σ : ℝ} (hσ : 0 < σ) {H J : ℕ} (hJ : 0 < J)
    (b₀ : Fin H → Coeff) (w : Fin H → ℝ) (mark : Fin H → Fin J → Bool)
    (hw : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1) :
    MarkedLaw σ H J b₀ w mark univ ≤ 1 := by
  haveI := markedPrior_probability hσ b₀ w hw hw1
  change ((MarkedPrior σ H b₀ w).prod volume).restrict _ univ ≤ 1
  rw [Measure.restrict_apply_univ]
  calc
    _ ≤ ((MarkedPrior σ H b₀ w).prod volume) (univ ×ˢ Icc (0 : ℝ) 1) :=
      measure_mono (markedEvent_subset_unit hJ mark)
    _ = 1 := by simp [Measure.prod_prod]

end Submission.Obl.k4_scalar_marked_packet_recovery
