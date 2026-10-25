import Submission.Obl.k4_oss_flat_decay.Smoothing

namespace Submission.Obl.k4_oss_flat_decay

open MeasureTheory Set
open scoped MeasureTheory ENNReal NNReal

/-- Uniform interval smoothing has density equal to the normalized mass of the
sliding interval. The identity is stated for nonnegative test functions. -/
theorem lintegral_uniform_smoothing (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {δ : ℝ} (hδ : 0 < δ) (f : ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ x, f x ∂(μ ∗ uniformNoise δ)) =
      (ENNReal.ofReal (2 * δ))⁻¹ *
        ∫⁻ x, f x * μ (Icc (x - δ) (x + δ)) := by
  let : IsProbabilityMeasure (uniformNoise δ) := uniformNoise_probability hδ
  have hvol : volume (Icc (-δ) δ) = ENNReal.ofReal (2 * δ) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  have hc : (ENNReal.ofReal (2 * δ))⁻¹ ≠ ∞ :=
    ENNReal.inv_ne_top.mpr (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
  have htranslate (x : ℝ) :
      (∫⁻ z, f (x + z) ∂(volume.restrict (Icc (-δ) δ))) =
        ∫⁻ y, (Icc (x - δ) (x + δ)).indicator f y := by
    rw [← lintegral_indicator measurableSet_Icc,
      ← lintegral_add_left_eq_self ((Icc (x - δ) (x + δ)).indicator f) x]
    apply lintegral_congr
    intro z
    have hmem : x + z ∈ Icc (x - δ) (x + δ) ↔ z ∈ Icc (-δ) δ := by
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    simp only [indicator_apply, hmem]
  have hK : Measurable (Function.uncurry
      (fun x y : ℝ => (Icc (x - δ) (x + δ)).indicator f y)) := by
    convert (hf.comp measurable_snd).indicator
      ((measurableSet_le (measurable_fst.sub (measurable_const (a := δ))) measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_fst.add (measurable_const (a := δ))))) using 1
    ext p
    rcases p with ⟨x, y⟩
    rfl
  have hflip (x y : ℝ) :
      (Icc (x - δ) (x + δ)).indicator f y =
        (Icc (y - δ) (y + δ)).indicator (fun _ => f y) x := by
    have hmem : y ∈ Icc (x - δ) (x + δ) ↔ x ∈ Icc (y - δ) (y + δ) := by
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    simp only [indicator_apply, hmem]
  rw [Measure.lintegral_conv hf]
  simp_rw [uniformNoise, ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul,
    hvol, htranslate]
  rw [lintegral_const_mul' _ _ hc]
  congr 1
  rw [lintegral_lintegral_swap hK.aemeasurable]
  simp_rw [hflip, lintegral_indicator_const measurableSet_Icc]

/-- Smoothing below the Frostman cutoff has a bounded density, with a compact
support retained for subsequent frequency integration. -/
theorem lintegral_uniform_smoothing_le_on (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {M : ℝ} (hsupp : μ (Icc (-M) M)ᶜ = 0)
    {δ r C s : ℝ} (hδ : 0 < δ) (hδr : δ ≤ r) (hr1 : r ≤ 1)
    (hcap : ∀ x : ℝ, μ (Icc (x - r) (x + r)) ≤ ENNReal.ofReal (C * r ^ s))
    (f : ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ x, f x ∂(μ ∗ uniformNoise δ)) ≤
      ENNReal.ofReal (C * r ^ s / (2 * δ)) * ∫⁻ x in Icc (-M - 1) (M + 1), f x := by
  have hr : 0 < r := hδ.trans_le hδr
  have hδ1 : δ ≤ 1 := hδr.trans hr1
  have hmass (x : ℝ) : μ (Icc (x - δ) (x + δ)) ≤
      (Icc (-M - 1) (M + 1)).indicator (fun _ => ENNReal.ofReal (C * r ^ s)) x := by
    by_cases hx : x ∈ Icc (-M - 1) (M + 1)
    · rw [indicator_of_mem hx]
      exact (measure_mono (Icc_subset_Icc (by linarith) (by linarith))).trans (hcap x)
    · rw [indicator_of_notMem hx]
      have hsub : Icc (x - δ) (x + δ) ⊆ (Icc (-M) M)ᶜ := by
        intro y hy hyI
        apply hx
        obtain ⟨hy₁, hy₂⟩ := hy
        obtain ⟨hI₁, hI₂⟩ := hyI
        constructor <;> linarith
      exact (measure_mono hsub).trans_eq hsupp
  rw [lintegral_uniform_smoothing μ hδ f hf]
  calc
    _ ≤ (ENNReal.ofReal (2 * δ))⁻¹ *
        ∫⁻ x, f x * (Icc (-M - 1) (M + 1)).indicator
          (fun _ => ENNReal.ofReal (C * r ^ s)) x := by
      gcongr with x
      exact hmass x
    _ = (ENNReal.ofReal (2 * δ))⁻¹ * ENNReal.ofReal (C * r ^ s) *
        ∫⁻ x in Icc (-M - 1) (M + 1), f x := by
      have hpoint (x : ℝ) : f x * (Icc (-M - 1) (M + 1)).indicator
          (fun _ => ENNReal.ofReal (C * r ^ s)) x =
          ENNReal.ofReal (C * r ^ s) * (Icc (-M - 1) (M + 1)).indicator f x := by
        by_cases hx : x ∈ Icc (-M - 1) (M + 1) <;> simp [hx, mul_comm]
      simp_rw [hpoint, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [lintegral_indicator measurableSet_Icc, mul_assoc]
    _ = _ := by
      rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 * δ),
        ENNReal.div_eq_inv_mul]

end Submission.Obl.k4_oss_flat_decay
