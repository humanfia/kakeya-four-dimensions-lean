import Mathlib

namespace Submission.Obl.k4_horizontal_supercritical_three_projections

open Set MeasureTheory

/-- Normalize the current chart restriction by its unchanged original prior
mass. The prior itself is the conditional original trajectory law. -/
noncomputable def chartLaw {α : Type} [MeasurableSpace α]
    (ν : Measure α) (ζ : Measure (α × ℝ)) (A : Set α) : Measure (α × ℝ) :=
  (ν A)⁻¹ • ζ.restrict (A ×ˢ univ)

/-- Conditioning keeps the same prior-times-time domination constant. -/
theorem chartLaw_domination {α : Type} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (ζ : Measure (α × ℝ)) (A : Set α) (C : ENNReal)
    (hdom : ζ ≤ C • (ν.prod volume)) :
    chartLaw ν ζ A ≤ C • ((ProbabilityTheory.cond ν A).prod volume) := by
  have h := Measure.restrict_mono (s := A ×ˢ (univ : Set ℝ)) le_rfl hdom
  rw [Measure.restrict_smul, ← Measure.restrict_prod_eq_prod_univ] at h
  have h' := smul_le_smul_left (ν A)⁻¹ h
  simpa only [chartLaw, ProbabilityTheory.cond, Measure.prod_smul_left, smul_smul, mul_comm] using h'

/-- No original prior mass is lost when restoring a normalized chart law. -/
theorem chartLaw_restore {α : Type} [MeasurableSpace α]
    (ν : Measure α) (ζ : Measure (α × ℝ)) (A : Set α)
    (hA₀ : ν A ≠ 0) (hAtop : ν A ≠ ⊤) :
    ν A • chartLaw ν ζ A = ζ.restrict (A ×ˢ univ) := by
  rw [chartLaw, smul_smul, ENNReal.mul_inv_cancel hA₀ hAtop, one_smul]

theorem chartLaw_apply {α : Type} [MeasurableSpace α]
    (ν : Measure α) (ζ : Measure (α × ℝ)) (A : Set α)
    {E : Set (α × ℝ)} (hE : MeasurableSet E) :
    chartLaw ν ζ A E = (ν A)⁻¹ * ζ (E ∩ (A ×ˢ univ)) := by
  rw [chartLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hE]

/-- Its normalized total mass is the original selected chart mass divided
by the full original trajectory assignment mass. -/
theorem chartLaw_univ {α : Type} [MeasurableSpace α]
    (ν : Measure α) (ζ : Measure (α × ℝ)) (A : Set α) :
    chartLaw ν ζ A univ = (ν A)⁻¹ * ζ (A ×ˢ univ) := by
  rw [chartLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]

/-- Every normalized incidence still belongs to its original assignment. -/
theorem chartLaw_supported {α : Type} [MeasurableSpace α]
    (ν : Measure α) (ζ : Measure (α × ℝ)) {A : Set α} (hA : MeasurableSet A) :
    ∀ᵐ p ∂chartLaw ν ζ A, p.1 ∈ A := by
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem (hA.prod MeasurableSet.univ)] with p hp
  exact hp.1

/-- Restricting to a chart does not alter the time support. -/
theorem chartLaw_time_support {α : Type} [MeasurableSpace α]
    (ν : Measure α) (ζ : Measure (α × ℝ)) (A : Set α)
    (hsupp : ζ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0) :
    chartLaw ν ζ A (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [chartLaw, Measure.smul_apply, smul_eq_mul]
  have hz : (ζ.restrict (A ×ˢ univ)) (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 :=
    le_antisymm ((Measure.restrict_le_self _).trans_eq hsupp) bot_le
  rw [hz, mul_zero]

/-- Chart caps transfer to the normalized law without changing their palette. -/
theorem chartLaw_cap {α : Type} [MeasurableSpace α]
    (ν : Measure α) (ζ μ : Measure (α × ℝ)) (A : Set α) (hζ : ζ ≤ μ)
    {E : Set (α × ℝ)} (hE : MeasurableSet E) (C : ENNReal)
    (hcap : μ (E ∩ (A ×ˢ univ)) ≤ C) :
    chartLaw ν ζ A E ≤ (ν A)⁻¹ * C := by
  rw [chartLaw_apply ν ζ A hE]
  exact mul_le_mul_right ((hζ _).trans hcap) _

/-- A chart active relative to its original prior is a dense scalar input. -/
theorem chartLaw_mass_lower {α : Type} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (ζ : Measure (α × ℝ)) (A : Set α)
    (hA₀ : ν A ≠ 0) (δ : ENNReal) (h : δ * ν A ≤ ζ (A ×ˢ univ)) :
    δ ≤ chartLaw ν ζ A univ := by
  rw [chartLaw_univ]
  calc
    δ = (ν A)⁻¹ * (δ * ν A) := by
      rw [mul_left_comm, ENNReal.inv_mul_cancel hA₀ (measure_ne_top ν A), mul_one]
    _ ≤ _ := mul_le_mul_right h _

/-- The active-prior and reference-weight cutoffs together control the scalar
density ratio, using the original chart cap and prior-times-time domination. -/
theorem chart_density_ratio_bounds {a W δ H K : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hH : 0 < H)
    (hlower : δ * a ≤ H * W) (hupper : δ * W ≤ K * a) :
    δ / H ≤ W / a ∧ W / a ≤ K / δ := by
  constructor
  · exact (div_le_div_iff₀ hH ha).mpr (by nlinarith)
  · exact (div_le_div_iff₀ ha hδ).mpr (by nlinarith)

/-- Convert the unchanged prior denominator to the real density prefactor
used by the scalar premise. -/
theorem chartLaw_real_cap {α : Type} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (ζ μ : Measure (α × ℝ)) (A : Set α)
    (hA₀ : ν A ≠ 0) (hζ : ζ ≤ μ) {E : Set (α × ℝ)} (hE : MeasurableSet E)
    (C W : ℝ) (hcap : μ (E ∩ (A ×ˢ univ)) ≤ ENNReal.ofReal (C * W)) :
    chartLaw ν ζ A E ≤ ENNReal.ofReal (C * (W / (ν A).toReal)) := by
  have hpos : 0 < (ν A).toReal := ENNReal.toReal_pos hA₀ (measure_ne_top ν A)
  apply (chartLaw_cap ν ζ μ A hζ hE _ hcap).trans_eq
  have hi : (ν A)⁻¹ = ENNReal.ofReal ((ν A).toReal⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_toReal (measure_ne_top ν A)]
  rw [hi, ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
  congr 1
  ring

/-- Every scalar floor restores to a floor under the unchanged current
physical law, with its original full prior factor. -/
theorem chartLaw_restore_floor {α : Type} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (ζ : Measure (α × ℝ)) (A : Set α)
    (hA₀ : ν A ≠ 0) (E : Set (α × ℝ)) {t : ℝ}
    (h : ENNReal.ofReal t ≤ chartLaw ν ζ A E) :
    ENNReal.ofReal ((ν A).toReal * t) ≤ ζ E := by
  calc
    _ = ν A * ENNReal.ofReal t := by
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (measure_ne_top ν A)]
    _ ≤ ν A * chartLaw ν ζ A E := mul_le_mul_right h _
    _ = (ν A • chartLaw ν ζ A) E := by rw [Measure.smul_apply, smul_eq_mul]
    _ = (ζ.restrict (A ×ˢ univ)) E := by
      rw [chartLaw_restore ν ζ A hA₀ (measure_ne_top ν A)]
    _ ≤ ζ E := Measure.restrict_le_self _

end Submission.Obl.k4_horizontal_supercritical_three_projections
