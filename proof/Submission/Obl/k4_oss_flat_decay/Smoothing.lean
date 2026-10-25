import Submission.Obl.k4_oss_flat_decay.Energy

namespace Submission.Obl.k4_oss_flat_decay

open MeasureTheory Set
open scoped MeasureTheory ENNReal NNReal

/-- Evaluating the additive convolution on a closed real interval. -/
theorem conv_apply_Icc (μ ν : Measure ℝ) [SFinite ν] (x u : ℝ) :
    (μ ∗ ν) (Icc (x - u) (x + u)) =
      ∫⁻ y, ν (Icc ((x - y) - u) ((x - y) + u)) ∂μ := by
  rw [Measure.conv, Measure.map_apply measurable_add measurableSet_Icc,
    Measure.prod_apply (measurableSet_Icc.preimage measurable_add)]
  apply lintegral_congr
  intro y
  congr 1
  ext z
  simp only [mem_preimage, mem_Icc]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Convolution with a probability law preserves all interval caps at their
stated scales, since the cap is uniform in the interval's center. -/
theorem interval_cap_conv (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {u B : ℝ}
    (hcap : ∀ x : ℝ, μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal B) (x : ℝ) :
    (μ ∗ ν) (Icc (x - u) (x + u)) ≤ ENNReal.ofReal B := by
  rw [Measure.conv_comm, conv_apply_Icc]
  calc _ ≤ ∫⁻ _y, ENNReal.ofReal B ∂ν := lintegral_mono (fun y => hcap (x - y))
    _ = _ := by simp

private theorem small_scale_power {r u s : ℝ}
    (hr : 0 < r) (hu : 0 < u) (hur : u ≤ r) (hs1 : s ≤ 1) :
    u / r * r ^ s ≤ u ^ s := by
  have hratio : u / r ≤ (u / r) ^ s := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_ge (div_pos hu hr) ((div_le_one hr).mpr hur) hs1
  calc u / r * r ^ s ≤ (u / r) ^ s * r ^ s :=
      mul_le_mul_of_nonneg_right hratio (Real.rpow_nonneg hr.le _)
    _ = u ^ s := by
      rw [← Real.mul_rpow (div_nonneg hu.le hr.le) hr.le,
        div_mul_cancel₀ _ hr.ne']

/-- A probability smoothing law with support in `[-r,r]` and density of size
`D/r` upgrades a finite-scale Frostman cap to an all-scale cap. -/
theorem all_scale_interval_cap_conv (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {r C D s : ℝ}
    (hr : 0 < r) (hr1 : 2 * r ≤ 1) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (_hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hcap : ∀ x u : ℝ, r ≤ u → u ≤ 1 →
      μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (C * u ^ s))
    (hsupp : ν (Icc (-r) r)ᶜ = 0)
    (hdensity : ∀ x u : ℝ, 0 < u → u ≤ r →
      ν (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (D * u / r)) :
    ∀ x u : ℝ, 0 < u → u ≤ 1 →
      (μ ∗ ν) (Icc (x - u) (x + u)) ≤ ENNReal.ofReal ((2 * D * C) * u ^ s) := by
  intro x u hu hu1
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hcoef : C ≤ 2 * D * C := by nlinarith [mul_nonneg hC0 (sub_nonneg.mpr hD)]
  by_cases hru : r ≤ u
  · exact (interval_cap_conv μ ν (fun y => hcap y u hru hu1) x).trans
      (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hu.le s)))
  · have hur : u ≤ r := le_of_not_ge hru
    rw [conv_apply_Icc]
    let B : Set ℝ := Icc (x - 2 * r) (x + 2 * r)
    have hbound (y : ℝ) : ν (Icc ((x - y) - u) ((x - y) + u)) ≤
        B.indicator (fun _ => ENNReal.ofReal (D * u / r)) y := by
      by_cases hy : y ∈ B
      · rw [indicator_of_mem hy]
        exact hdensity (x - y) u hu hur
      · rw [indicator_of_notMem hy]
        have hsub : Icc ((x - y) - u) ((x - y) + u) ⊆ (Icc (-r) r)ᶜ := by
          intro z hz hzr
          apply hy
          dsimp [B]
          obtain ⟨hz₁, hz₂⟩ := hz
          obtain ⟨hr₁, hr₂⟩ := hzr
          constructor <;> linarith
        exact (measure_mono hsub).trans_eq hsupp
    have htwo : (2 * r) ^ s ≤ 2 * r ^ s := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.rpow_one] using
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs1)
        (Real.rpow_nonneg hr.le _)
    calc (∫⁻ y, ν (Icc ((x - y) - u) ((x - y) + u)) ∂μ) ≤
          ∫⁻ y, B.indicator (fun _ => ENNReal.ofReal (D * u / r)) y ∂μ :=
        lintegral_mono hbound
      _ = ENNReal.ofReal (D * u / r) * μ B :=
        lintegral_indicator_const measurableSet_Icc _
      _ ≤ ENNReal.ofReal (D * u / r) * ENNReal.ofReal (C * (2 * r) ^ s) :=
        mul_le_mul' le_rfl (hcap x (2 * r) (by linarith) hr1)
      _ = ENNReal.ofReal ((D * u / r) * (C * (2 * r) ^ s)) :=
        (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal ((2 * D * C) * u ^ s) := by
        apply ENNReal.ofReal_le_ofReal
        calc
          (D * u / r) * (C * (2 * r) ^ s) ≤ (D * u / r) * (C * (2 * r ^ s)) := by
            gcongr
          _ = (2 * D * C) * (u / r * r ^ s) := by ring
          _ ≤ (2 * D * C) * u ^ s :=
            mul_le_mul_of_nonneg_left (small_scale_power hr hu hur hs1) (by positivity)

/-- The uniform smoothing law on a real interval of radius `r`. -/
noncomputable def uniformNoise (r : ℝ) : Measure ℝ :=
  ProbabilityTheory.cond volume (Icc (-r) r)

theorem uniformNoise_probability {r : ℝ} (hr : 0 < r) :
    IsProbabilityMeasure (uniformNoise r) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

theorem uniformNoise_support (r : ℝ) : (uniformNoise r) (Icc (-r) r)ᶜ = 0 := by
  rw [uniformNoise, ProbabilityTheory.cond_apply' measurableSet_Icc.compl]
  simp

theorem uniformNoise_interval_bound {r : ℝ} (hr : 0 < r) (x u : ℝ) :
    (uniformNoise r) (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (u / r) := by
  rw [uniformNoise, ProbabilityTheory.cond_apply' measurableSet_Icc]
  calc _ ≤ (volume (Icc (-r) r))⁻¹ * volume (Icc (x - u) (x + u)) :=
      mul_le_mul' le_rfl (measure_mono inter_subset_right)
    _ = _ := by
      rw [Real.volume_Icc, Real.volume_Icc,
        show r - -r = 2 * r by ring, show x + u - (x - u) = 2 * u by ring,
        ← ENNReal.div_eq_inv_mul,
        ← ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 * r)]
      congr 1
      field_simp

/-- Uniform interval smoothing makes a finite-scale Frostman cap valid below
the original cutoff as well. -/
theorem uniform_smoothing_interval_bound (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {r C s : ℝ} (hr : 0 < r) (hr1 : 2 * r ≤ 1) (hC : 1 ≤ C)
    (hs : 0 ≤ s) (hs1 : s ≤ 1)
    (hcap : ∀ x u : ℝ, r ≤ u → u ≤ 1 →
      μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (C * u ^ s)) :
    ∀ x u : ℝ, 0 < u → u ≤ 1 →
      (μ ∗ uniformNoise r) (Icc (x - u) (x + u)) ≤
        ENNReal.ofReal ((2 * C) * u ^ s) := by
  let : IsProbabilityMeasure (uniformNoise r) := uniformNoise_probability hr
  simpa only [mul_one, one_mul] using all_scale_interval_cap_conv μ (uniformNoise r)
    hr hr1 hC le_rfl hs hs1 hcap (uniformNoise_support r)
    (fun x u _ _ => by simpa only [one_mul] using uniformNoise_interval_bound hr x u)

/-- A uniform interval mollifier has bounded subcritical Riesz energy, uniformly
in its scale. -/
theorem uniform_smoothing_energy_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {r C s t : ℝ} (hr : 0 < r) (hr1 : 2 * r ≤ 1) (hC : 1 ≤ C)
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (hst : t < s)
    (hcap : ∀ x u : ℝ, r ≤ u → u ≤ 1 →
      μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (C * u ^ s)) :
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (|x - y| ^ (-t))
      ∂(μ ∗ uniformNoise r) ∂(μ ∗ uniformNoise r)) ≤
      ENNReal.ofReal ((2 * C) * (1 / 2 : ℝ) ^ (-t) /
        (1 - (1 / 2 : ℝ) ^ (s - t))) := by
  let : IsProbabilityMeasure (uniformNoise r) := uniformNoise_probability hr
  exact energy_le_of_all_scale_interval_bound (μ ∗ uniformNoise r) (by linarith) ht hst
    (uniform_smoothing_interval_bound μ hr hr1 hC hs hs1 hcap)

/-- Finite-scale nonconcentration implies the mollified-energy hypothesis with
an arbitrary prescribed power loss. -/
theorem finite_scale_mollified_energy_bound {s t ε : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 ≤ t) (hst : t < s) (hε : 0 < ε) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ r₀ ≤ 1 / 2 ∧
      ∀ r : ℝ, 0 < r → r < r₀ →
      ∀ μ : Measure ℝ, IsProbabilityMeasure μ →
      (∀ x u : ℝ, r ≤ u → u ≤ 1 →
        μ (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (r ^ (-(ε / 2)) * u ^ s)) →
      (∫⁻ x, ∫⁻ y, ENNReal.ofReal (|x - y| ^ (-t))
        ∂(μ ∗ uniformNoise r) ∂(μ ∗ uniformNoise r)) ≤
        ENNReal.ofReal (r ^ (-ε)) := by
  let A : ℝ := 2 * (1 / 2 : ℝ) ^ (-t) / (1 - (1 / 2 : ℝ) ^ (s - t))
  obtain ⟨r₁, hr₁, hr₁1, hA⟩ := exists_scale_absorb_constant A (ε / 2) (by linarith)
  refine ⟨min r₁ (1 / 2), lt_min hr₁ (by norm_num), min_le_right _ _, ?_⟩
  intro r hr hrr μ hμ hcap
  let : IsProbabilityMeasure μ := hμ
  have hrhalf : r ≤ 1 / 2 := (hrr.trans_le (min_le_right _ _)).le
  have hC : 1 ≤ r ^ (-(ε / 2)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr (by linarith) (by linarith)
  have henergy := uniform_smoothing_energy_le μ hr (by linarith) hC hs hs1 ht hst hcap
  refine henergy.trans (ENNReal.ofReal_le_ofReal ?_)
  calc (2 * r ^ (-(ε / 2))) * (1 / 2 : ℝ) ^ (-t) /
        (1 - (1 / 2 : ℝ) ^ (s - t)) = r ^ (-(ε / 2)) * A := by dsimp [A]; ring
    _ ≤ r ^ (-(ε / 2)) * r ^ (-(ε / 2)) :=
      mul_le_mul_of_nonneg_left (hA r hr (hrr.trans_le (min_le_left _ _)))
        (Real.rpow_nonneg hr.le _)
    _ = r ^ (-ε) := by rw [← Real.rpow_add hr]; congr 1; ring

end Submission.Obl.k4_oss_flat_decay
