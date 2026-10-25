import Submission.Obl.k4_native_calibrated_homogeneous_remainder.TypicalOperations

/-! One-sided typical exponent comparison.
The argument is adapted from this LOT tree, o119, session x0404, commit
459c108, CompCompare.lean, and expressed using the accepted IsPowerSmall API. -/

namespace Submission.Obl.k4_native_calibrated_homogeneous_remainder

open MeasureTheory Set Filter
open scoped ENNReal
open Submission.Obl.k4_native_grid_profile_extension.Profiles
open Submission.Obl.k4_scalar_grid_density_extension

/-- A typical lower density cannot exceed a typical upper density by a fixed
power on a family whose mass is not power-small. -/
theorem exponent_le_of_one_sided_comparison {Ω : ℕ → Type*}
    [∀ k, MeasurableSpace (Ω k)]
    (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (Ω k)) (lower upper : (k : ℕ) → Ω k → ENNReal)
    (a b : ℝ) (hmass : ¬ IsPowerSmall N (fun k => μ k univ))
    (hlo : ∀ τ : ℝ, 0 < τ → IsPowerSmall N
      (fun k => μ k {z | lower k z < ENNReal.ofReal (N k ^ (-a - τ))}))
    (hhi : ∀ τ : ℝ, 0 < τ → IsPowerSmall N
      (fun k => μ k {z | ENNReal.ofReal (N k ^ (-b + τ)) < upper k z}))
    (hcompare : ∀ ε : ℝ, 0 < ε → IsPowerSmall N
      (fun k => μ k {z | ENNReal.ofReal (N k ^ ε) * upper k z < lower k z})) :
    b ≤ a := by
  by_contra hab
  have hgap : a < b := lt_of_not_ge hab
  let τ : ℝ := (b - a) / 4
  have hτ : 0 < τ := by dsimp [τ]; linarith
  apply hmass
  apply (((hlo τ hτ).add hNt (hhi τ hτ)).add hNt (hcompare τ hτ)).mono
  apply Eventually.of_forall
  intro k
  refine le_trans (measure_mono ?_) (measure_union_le₃ _ _ _ _)
  intro z _
  by_contra hz
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hz
  have hpow : ENNReal.ofReal (N k ^ (-a - τ)) ≤
      ENNReal.ofReal (N k ^ τ) * ENNReal.ofReal (N k ^ (-b + τ)) :=
    hz.1.1.trans (hz.2.trans (mul_le_mul' le_rfl hz.1.2))
  rw [ofReal_rpow_mul_rpow (by linarith [hN k])] at hpow
  have h := le_of_ofReal_rpow_le (by linarith [hN k]) hpow
  dsimp [τ] at h
  linarith

theorem typical_lower_powerSmall {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    {N : ℕ → ℝ} {μ : (k : ℕ) → Measure (Ω k)} {f : (k : ℕ) → Ω k → ENNReal}
    {e : ℝ} (ht : HasTypicalDensity N μ f e) (τ : ℝ) (hτ : 0 < τ) :
    IsPowerSmall N (fun k => μ k {z | f k z < ENNReal.ofReal (N k ^ (-e - τ))}) :=
  IsPowerSmall.mono (ht τ hτ)
    (Eventually.of_forall fun _ => measure_mono fun _ hz => Or.inl hz)

theorem typical_upper_powerSmall {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    {N : ℕ → ℝ} {μ : (k : ℕ) → Measure (Ω k)} {f : (k : ℕ) → Ω k → ENNReal}
    {e : ℝ} (ht : HasTypicalDensity N μ f e) (τ : ℝ) (hτ : 0 < τ) :
    IsPowerSmall N (fun k => μ k {z | ENNReal.ofReal (N k ^ (-e + τ)) < f k z}) :=
  IsPowerSmall.mono (ht τ hτ)
    (Eventually.of_forall fun _ => measure_mono fun _ hz => Or.inr hz)

/-- A lower comparison with growth exponent `c` forces the corresponding
ordering of typical density exponents. -/
theorem exponent_le_of_power_lower_comparison {Ω : ℕ → Type*}
    [∀ k, MeasurableSpace (Ω k)]
    (N : ℕ → ℝ) (hN : ∀ k, 2 ≤ N k) (hNt : Tendsto N atTop atTop)
    (μ : (k : ℕ) → Measure (Ω k)) (old current : (k : ℕ) → Ω k → ENNReal)
    (a b c : ℝ) (hmass : ¬ IsPowerSmall N (fun k => μ k univ))
    (hold : HasTypicalDensity N μ old a) (hcurrent : HasTypicalDensity N μ current b)
    (hcompare : ∀ ε : ℝ, 0 < ε → IsPowerSmall N
      (fun k => μ k {z | current k z < ENNReal.ofReal (N k ^ (c - ε)) * old k z})) :
    b + c ≤ a := by
  by_contra hbad
  have hgap : a < b + c := lt_of_not_ge hbad
  let τ : ℝ := (b + c - a) / 4
  have hτ : 0 < τ := by dsimp [τ]; linarith
  apply hmass
  apply (((typical_lower_powerSmall hold τ hτ).add hNt
    (typical_upper_powerSmall hcurrent τ hτ)).add hNt (hcompare τ hτ)).mono
  apply Eventually.of_forall
  intro k
  refine le_trans (measure_mono ?_) (measure_union_le₃ _ _ _ _)
  intro z _
  by_contra hz
  simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hz
  have hpow : ENNReal.ofReal (N k ^ (c - τ)) * ENNReal.ofReal (N k ^ (-a - τ)) ≤
      ENNReal.ofReal (N k ^ (-b + τ)) :=
    ((mul_le_mul' le_rfl hz.1.1).trans hz.2).trans hz.1.2
  rw [ofReal_rpow_mul_rpow (by linarith [hN k])] at hpow
  have h := le_of_ofReal_rpow_le (by linarith [hN k]) hpow
  dsimp [τ] at h
  linarith

end Submission.Obl.k4_native_calibrated_homogeneous_remainder
