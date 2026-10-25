import Submission.Obl.k4_scalar_marked_coefficient_smoothing.Interface

/-!
# The coefficient noise

`Noise σ` is the product of five independent uniform laws on `[0, σ]`.  This file records
that it is a probability law living on the box `[0, σ]⁵`, and the slice estimate behind every
density ceiling: the intercept noise `u 0` enters the base trace by translation, so it gives
the base trace a density at most `1/σ`, while the remaining four noises only enter through an
event `Q` whose probability is kept as a factor.

The splitting of the first coordinate follows the same route as
`volume_box_yTrace_le` of x0215's `Submission/Lib/K4ScalarMeshSmoothing.lean` (o062, branch
x0215), written here for the product law `Noise σ` instead of the volume of a box.
-/

namespace Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw

open MeasureTheory Set
open scoped ENNReal

/-- One coordinate of the coefficient noise: the uniform law on `[0, σ]`. -/
noncomputable def noise1 (σ : ℝ) : Measure ℝ :=
  ENNReal.ofReal (σ⁻¹) • volume.restrict (Icc 0 σ)

/-- The law of the last four noise coordinates. -/
noncomputable def noise4 (σ : ℝ) : Measure (Fin 4 → ℝ) :=
  Measure.pi (fun _ : Fin 4 => noise1 σ)

theorem Noise_eq_pi (σ : ℝ) : Noise σ = Measure.pi (fun _ : Fin 5 => noise1 σ) := rfl

theorem noise1_apply (σ : ℝ) (A : Set ℝ) :
    noise1 σ A = ENNReal.ofReal (σ⁻¹) * volume (A ∩ Icc 0 σ) := by
  rw [noise1, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply' measurableSet_Icc]

theorem isProbabilityMeasure_noise1 {σ : ℝ} (hσ : 0 < σ) : IsProbabilityMeasure (noise1 σ) := by
  constructor
  rw [noise1_apply, univ_inter, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (by positivity),
    inv_mul_cancel₀ hσ.ne', ENNReal.ofReal_one]

theorem isProbabilityMeasure_noise4 {σ : ℝ} (hσ : 0 < σ) : IsProbabilityMeasure (noise4 σ) := by
  have := isProbabilityMeasure_noise1 hσ
  unfold noise4
  infer_instance

theorem isProbabilityMeasure_Noise {σ : ℝ} (hσ : 0 < σ) : IsProbabilityMeasure (Noise σ) := by
  have := isProbabilityMeasure_noise1 hσ
  rw [Noise_eq_pi]
  infer_instance

/-- A translated set has `noise1`-mass at most `1/σ` times its length. -/
theorem noise1_preimage_add_le (σ c : ℝ) (A : Set ℝ) :
    noise1 σ ((fun v => v + c) ⁻¹' A) ≤ ENNReal.ofReal (σ⁻¹) * volume A := by
  rw [noise1_apply]
  refine mul_le_mul_right ?_ _
  calc volume ((fun v => v + c) ⁻¹' A ∩ Icc 0 σ) ≤ volume ((fun v => v + c) ⁻¹' A) :=
        measure_mono inter_subset_left
    _ = volume A := measure_preimage_add_right _ _ _

/-- `noise1` lives on `[0, σ]`. -/
theorem noise1_compl_Icc (σ : ℝ) : noise1 σ (Icc 0 σ)ᶜ = 0 := by
  rw [noise1_apply, compl_inter_self, measure_empty, mul_zero]

/-- The coefficient noise lives on the box `[0, σ]⁵`. -/
theorem Noise_ae_mem {σ : ℝ} (hσ : 0 < σ) : ∀ᵐ u ∂(Noise σ), ∀ i, u i ∈ Icc 0 σ := by
  have := isProbabilityMeasure_noise1 hσ
  rw [ae_all_iff]
  intro i
  have hmp := measurePreserving_eval (fun _ : Fin 5 => noise1 σ) i
  rw [Noise_eq_pi, ae_iff]
  have hset : {a : Fin 5 → ℝ | ¬a i ∈ Icc 0 σ} = Function.eval i ⁻¹' (Icc 0 σ)ᶜ := rfl
  rw [hset, hmp.measure_preimage measurableSet_Icc.compl.nullMeasurableSet]
  exact noise1_compl_Icc σ

/-- The first coordinate is split off: `Noise σ = noise1 σ ⊗ noise4 σ` along
`u ↦ (u 0, Fin.tail u)`. -/
theorem measurePreserving_Noise_split {σ : ℝ} (hσ : 0 < σ) :
    MeasurePreserving (fun u : Fin 5 → ℝ => (u 0, Fin.tail u)) (Noise σ)
      ((noise1 σ).prod (noise4 σ)) := by
  have := isProbabilityMeasure_noise1 hσ
  have h := measurePreserving_piFinSuccAbove (fun _ : Fin 5 => noise1 σ) 0
  have heq : (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) 0 : (Fin 5 → ℝ) → _) =
      fun u => (u 0, Fin.tail u) := by
    funext u
    simp [MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv, Fin.removeNth_zero]
  rw [heq] at h
  exact h

/-- **Noise slice.**  If the base trace is `u 0 + Y (tail u)` and the remaining event only
depends on the last four coordinates, then the probability that the base trace lies in `A`
while the event `Q` holds is at most `(1/σ) · P(Q) · |A|`. -/
theorem Noise_slice_le {σ : ℝ} (hσ : 0 < σ) {Y : (Fin 4 → ℝ) → ℝ} (hY : Measurable Y)
    {A : Set ℝ} (hA : MeasurableSet A) {Q : Set (Fin 4 → ℝ)} (hQ : MeasurableSet Q) :
    Noise σ {u | u 0 + Y (Fin.tail u) ∈ A ∧ Fin.tail u ∈ Q} ≤
      ENNReal.ofReal (σ⁻¹) * noise4 σ Q * volume A := by
  have := isProbabilityMeasure_noise1 hσ
  have := isProbabilityMeasure_noise4 hσ
  set S' : Set (ℝ × (Fin 4 → ℝ)) := {p | p.1 + Y p.2 ∈ A ∧ p.2 ∈ Q} with hS'
  have hS'm : MeasurableSet S' :=
    (hA.preimage (measurable_fst.add (hY.comp measurable_snd))).inter (hQ.preimage measurable_snd)
  have hset : {u : Fin 5 → ℝ | u 0 + Y (Fin.tail u) ∈ A ∧ Fin.tail u ∈ Q} =
      (fun u : Fin 5 → ℝ => (u 0, Fin.tail u)) ⁻¹' S' := rfl
  rw [hset, (measurePreserving_Noise_split hσ).measure_preimage hS'm.nullMeasurableSet,
    Measure.prod_apply_symm hS'm]
  calc ∫⁻ u', noise1 σ ((fun x => (x, u')) ⁻¹' S') ∂noise4 σ
      ≤ ∫⁻ u', Q.indicator (fun _ => ENNReal.ofReal (σ⁻¹) * volume A) u' ∂noise4 σ := by
        refine lintegral_mono fun u' => ?_
        by_cases hu' : u' ∈ Q
        · rw [indicator_of_mem hu']
          refine (measure_mono ?_).trans (noise1_preimage_add_le σ (Y u') A)
          intro v hv
          exact hv.1
        · rw [indicator_of_notMem hu']
          have : (fun x => (x, u')) ⁻¹' S' = ∅ := by
            ext v
            simp only [mem_preimage, hS', mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
            exact fun _ h => hu' h
          rw [this, measure_empty]
    _ = ENNReal.ofReal (σ⁻¹) * volume A * noise4 σ Q := lintegral_indicator_const hQ _
    _ = ENNReal.ofReal (σ⁻¹) * noise4 σ Q * volume A := by ring

/-- The noisy slope `β + u 1` (the first coordinate of the tail) has the law of
`β + noise1`. -/
theorem noise4_slope (σ : ℝ) (hσ : 0 < σ) (β : ℝ) {Ksl : Set ℝ} (hK : MeasurableSet Ksl) :
    noise4 σ {u' | β + u' 0 ∈ Ksl} = noise1 σ {v | β + v ∈ Ksl} := by
  have := isProbabilityMeasure_noise1 hσ
  have hmp := measurePreserving_eval (fun _ : Fin 4 => noise1 σ) 0
  have hm : MeasurableSet {v : ℝ | β + v ∈ Ksl} := hK.preimage (measurable_const.add measurable_id)
  exact hmp.measure_preimage hm.nullMeasurableSet

/-- A bin of width `ρ` has `noise1`-probability at most `min 1 (ρ/σ)`. -/
theorem noise1_bin_le {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ) (β : ℝ) (k : ℤ) :
    noise1 σ {v | ⌊(β + v) / ρ⌋ = k} ≤ ENNReal.ofReal (min 1 (ρ / σ)) := by
  rw [noise1_apply]
  have hset : {v : ℝ | ⌊(β + v) / ρ⌋ = k} = Ico (k * ρ - β) ((k + 1) * ρ - β) := by
    ext v
    simp only [mem_ofPred_eq, mem_Ico, Int.floor_eq_iff, le_div_iff₀ hρ, div_lt_iff₀ hρ]
    constructor
    · rintro ⟨h1, h2⟩; constructor <;> linarith
    · rintro ⟨h1, h2⟩; constructor <;> linarith
  rw [hset]
  rcases le_total 1 (ρ / σ) with h | h
  · rw [min_eq_left h]
    calc ENNReal.ofReal σ⁻¹ * volume (Ico (k * ρ - β) ((k + 1) * ρ - β) ∩ Icc 0 σ)
        ≤ ENNReal.ofReal σ⁻¹ * volume (Icc (0 : ℝ) σ) := by gcongr; exact inter_subset_right
      _ = 1 := by
        rw [Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (by positivity),
          inv_mul_cancel₀ hσ.ne', ENNReal.ofReal_one]
      _ = ENNReal.ofReal 1 := ENNReal.ofReal_one.symm
  · rw [min_eq_right h]
    calc ENNReal.ofReal σ⁻¹ * volume (Ico (k * ρ - β) ((k + 1) * ρ - β) ∩ Icc 0 σ)
        ≤ ENNReal.ofReal σ⁻¹ * volume (Ico (k * ρ - β) ((k + 1) * ρ - β)) := by
          gcongr; exact inter_subset_left
      _ = ENNReal.ofReal (ρ / σ) := by
        rw [Real.volume_Ico, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        field_simp
        ring

theorem noise1_le_one {σ : ℝ} (hσ : 0 < σ) (A : Set ℝ) : noise1 σ A ≤ 1 := by
  have := isProbabilityMeasure_noise1 hσ
  exact prob_le_one

end Submission.Obl.k4_scalar_marked_coefficient_smoothing.Raw
