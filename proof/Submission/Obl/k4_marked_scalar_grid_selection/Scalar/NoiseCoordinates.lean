/- Adapted from this LOT tree, obligation o100, session x0340, commit fb1668b,
   Submission/Obl/k4_scalar_marked_profile_selection/NoiseCoordinates.lean. -/
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.Atoms
import Submission.Obl.k4_marked_scalar_grid_selection.Scalar.LabelNoise
import Submission.Obl.k4_native_grid_profile_extension.Labels

noncomputable section

namespace Submission.Obl.k4_marked_scalar_grid_selection.Scalar

open MeasureTheory Set
open scoped ENNReal

abbrev otherNoise (σ : ℝ) : Measure (Fin 4 → ℝ) :=
  Measure.pi (fun _ : Fin 4 => intervalNoise σ)

abbrev dropY (u : Fin 5 → ℝ) : Fin 4 → ℝ := ![u 1, u 2, u 3, u 4]

abbrev noiseReorder (p : (Fin 5 → ℝ) × ℝ) :
    (ℝ × (Fin 4 → ℝ)) × ℝ := ((p.2, dropY p.1), p.1 0)

theorem otherNoise_probability {σ : ℝ} (hσ : 0 < σ) :
    IsProbabilityMeasure (otherNoise σ) := by
  letI := intervalNoise_probability hσ
  infer_instance

/-- Extract the independent linear intercept noise, with time first and the
other four noises in the middle. -/
theorem noiseReorder_law {σ : ℝ} (hσ : 0 < σ) (τ : Measure ℝ) [SFinite τ] :
    ((noise σ).prod τ).map noiseReorder =
      (τ.prod (otherNoise σ)).prod (intervalNoise σ) := by
  letI := intervalNoise_probability hσ
  letI := noise_probability hσ
  letI := otherNoise_probability hσ
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin 5 => ℝ) (0 : Fin 5)
  have he : MeasurePreserving e (noise σ) ((intervalNoise σ).prod (otherNoise σ)) :=
    measurePreserving_piFinSuccAbove (fun _ : Fin 5 => intervalNoise σ) (0 : Fin 5)
  have h₁ := he.prod (MeasurePreserving.id τ)
  have h₂ := measurePreserving_prodAssoc (intervalNoise σ) (otherNoise σ) τ
  have h₃ := (MeasurePreserving.id (intervalNoise σ)).prod
    (Measure.measurePreserving_swap (μ := otherNoise σ) (ν := τ))
  have h₄ := Measure.measurePreserving_swap (μ := intervalNoise σ)
    (ν := τ.prod (otherNoise σ))
  have h := (h₄.comp (h₃.comp (h₂.comp h₁))).map_eq
  convert h using 1
  congr 1
  funext p
  apply Prod.ext
  · apply Prod.ext
    · rfl
    · funext i
      fin_cases i <;> rfl
  · rfl

/-- The probability of a shifted scalar noise falling in a bin is bounded both
by one and by bin width divided by the noise width. -/
theorem intervalNoise_bin {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ)
    (b : ℝ) (z : ℤ) :
    intervalNoise σ {a | ⌊(b + a) / ρ⌋ = z} ≤
      ENNReal.ofReal (min 1 (ρ / σ)) := by
  letI := intervalNoise_probability hσ
  have hle₁ : intervalNoise σ {a | ⌊(b + a) / ρ⌋ = z} ≤ 1 :=
    (measure_mono (subset_univ _)).trans_eq (measure_univ)
  have hsub : {a : ℝ | ⌊(b + a) / ρ⌋ = z} ⊆
      Ico (ρ * (z : ℝ) - b) (ρ * ((z : ℝ) + 1) - b) := by
    intro a ha
    obtain ⟨hl, hu⟩ := Int.floor_eq_iff.mp ha
    constructor
    · have hh := (le_div_iff₀ hρ).mp hl
      nlinarith
    · have hh := (div_lt_iff₀ hρ).mp hu
      nlinarith
  have hle₂ : intervalNoise σ {a | ⌊(b + a) / ρ⌋ = z} ≤
      ENNReal.ofReal (ρ / σ) := by
    calc
      _ ≤ intervalNoise σ (Ico (ρ * (z : ℝ) - b) (ρ * ((z : ℝ) + 1) - b)) :=
        measure_mono hsub
      _ ≤ ENNReal.ofReal σ⁻¹ *
          volume (Ico (ρ * (z : ℝ) - b) (ρ * ((z : ℝ) + 1) - b)) := by
        exact mul_le_mul' le_rfl (Measure.restrict_le_self _)
      _ = ENNReal.ofReal (ρ / σ) := by
        rw [Real.volume_Ico]
        have heq : ρ * ((z : ℝ) + 1) - b - (ρ * (z : ℝ) - b) = ρ := by ring
        rw [heq, ← ENNReal.ofReal_mul (inv_nonneg.mpr hσ.le)]
        congr 1
        ring
  rw [ENNReal.ofReal_min, ENNReal.ofReal_one]
  exact le_min hle₁ hle₂

/-- Any other label may be adjoined to the noisy slope bin without changing its
counting-measure ceiling. -/
theorem otherNoise_joint_bin {σ ρ : ℝ} (hσ : 0 < σ) (hρ : 0 < ρ)
    (b : ℝ) (f : (Fin 4 → ℝ) → ℤ) (hf : Measurable f) :
    (otherNoise σ).map (fun v => (f v, (⌊(b + v 0) / ρ⌋ : ℤ))) ≤
      ENNReal.ofReal (min 1 (ρ / σ)) • (Measure.count : Measure (ℤ × ℤ)) := by
  letI := intervalNoise_probability hσ
  letI := otherNoise_probability hσ
  apply pair_label_count_bound _ f _ hf (by fun_prop)
  intro z
  have hmap : (otherNoise σ).map (Function.eval (0 : Fin 4)) = intervalNoise σ :=
    (measurePreserving_eval (fun _ : Fin 4 => intervalNoise σ) (0 : Fin 4)).map_eq
  have hset : MeasurableSet {a : ℝ | ⌊(b + a) / ρ⌋ = z} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have heq := Measure.map_apply (μ := otherNoise σ) (measurable_pi_apply (0 : Fin 4)) hset
  rw [hmap] at heq
  exact heq ▸ intervalNoise_bin hσ hρ b z

end Submission.Obl.k4_marked_scalar_grid_selection.Scalar
