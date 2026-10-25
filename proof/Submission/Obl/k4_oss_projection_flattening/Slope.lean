-- From o024 session x0067, commit 9dab30f2086d5fbe6f0edb2475a9e1c856bdab0e.
import Submission.Obl.k4_oss_projection_flattening.Frostman

namespace Submission.Obl.k4_oss_projection_flattening

open Set MeasureTheory
open scoped ENNReal

/-- The normalized ratio of two positive coefficients. -/
noncomputable def ratioDirection (p : ℝ × ℝ) : ℝ := p.2 / (2 * p.1)

/-- The direction distribution induced by two independent coefficients. -/
noncomputable def slopeLaw (β : Measure ℝ) : Measure ℝ :=
  Measure.map ratioDirection (β.prod β)

@[fun_prop]
theorem measurable_ratioDirection : Measurable ratioDirection := by
  unfold ratioDirection
  fun_prop

theorem slopeLaw_probability (β : Measure ℝ) [IsProbabilityMeasure β] :
    IsProbabilityMeasure (slopeLaw β) := by
  unfold slopeLaw
  infer_instance

theorem ratioDirection_mem {p : ℝ × ℝ}
    (h₁ : p.1 ∈ Icc (1 : ℝ) 2) (h₂ : p.2 ∈ Icc (1 : ℝ) 2) :
    ratioDirection p ∈ Icc (1 / 4 : ℝ) 1 := by
  have hp : 0 < 2 * p.1 := by linarith [h₁.1]
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [h₁.2, h₂.1]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [h₁.1, h₂.2]

theorem slopeLaw_support (β : Measure ℝ) [IsProbabilityMeasure β]
    (hβ : β (Icc (1 : ℝ) 2)ᶜ = 0) :
    slopeLaw β (Icc (1 / 4 : ℝ) 1)ᶜ = 0 := by
  rw [slopeLaw, Measure.map_apply measurable_ratioDirection measurableSet_Icc.compl]
  apply measure_mono_null _ (Measure.measure_prod_compl_eq_zero hβ hβ)
  intro p hp hprod
  exact hp (ratioDirection_mem hprod.1 hprod.2)

/-- Positive coefficient ratios preserve scale Frostman bounds, up to a fixed factor. -/
theorem slopeLaw_frostman {δ C s : ℝ} (hδ : 0 < δ) (hs1 : s ≤ 1) (hC : 1 ≤ C)
    (β : Measure ℝ) [IsProbabilityMeasure β]
    (hβ : β (Icc (1 : ℝ) 2)ᶜ = 0) (hF : ScaleFrostman δ C s β) :
    ScaleFrostman δ (4 * C) s (slopeLaw β) := by
  intro x u hδu hu1
  have hu : 0 < u := hδ.trans_le hδu
  have hC0 : 0 ≤ C := by linarith
  by_cases h4u : 4 * u ≤ 1
  · rw [slopeLaw, Measure.map_apply measurable_ratioDirection measurableSet_Icc,
      Measure.prod_apply (measurable_ratioDirection measurableSet_Icc)]
    have hfull : ∀ᵐ a ∂β, a ∈ Icc (1 : ℝ) 2 := by
      rw [ae_iff]
      exact hβ
    have hbound : ∀ᵐ a ∂β,
        β (Prod.mk a ⁻¹' (ratioDirection ⁻¹' Icc (x - u) (x + u))) ≤
          ENNReal.ofReal (C * (4 * u) ^ s) := by
      filter_upwards [hfull] with a ha
      apply le_trans (measure_mono ?_) (hF (2 * a * x) (4 * u) (by linarith) h4u)
      intro y hy
      change x - u ≤ y / (2 * a) ∧ y / (2 * a) ≤ x + u at hy
      have ha2 : 0 < 2 * a := by linarith [ha.1]
      have hlo := (le_div_iff₀ ha2).mp hy.1
      have hhi := (div_le_iff₀ ha2).mp hy.2
      have hau : 2 * a * u ≤ 4 * u := by nlinarith [ha.2]
      exact ⟨by nlinarith, by nlinarith⟩
    have hint := lintegral_mono_ae hbound
    simp only [lintegral_const, measure_univ, mul_one] at hint
    apply hint.trans (ENNReal.ofReal_le_ofReal ?_)
    have hfour : (4 : ℝ) ^ s ≤ 4 := by
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) hs1)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hu.le]
    nlinarith [mul_le_mul_of_nonneg_left hfour (mul_nonneg hC0 (Real.rpow_nonneg hu.le s))]
  · have : IsProbabilityMeasure (slopeLaw β) := slopeLaw_probability β
    have hmass : slopeLaw β (Icc (x - u) (x + u)) ≤ 1 := by
      exact (measure_mono (subset_univ _)).trans_eq (measure_univ (μ := slopeLaw β))
    have hupow : u ≤ u ^ s := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hu hu1 hs1
    have hconst : 1 ≤ 4 * C * u ^ s := by
      have := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hu.le s)
      nlinarith
    exact hmass.trans (by simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hconst)

/-- Collision energy for the normalized scalar projection. -/
noncomputable def scalarProjectionEnergy (r : ℝ) (α : Measure ℝ) (t : ℝ) : ℝ≥0∞ :=
  ((α.prod α).prod (α.prod α))
    {q : (ℝ × ℝ) × (ℝ × ℝ) | |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ r}

@[fun_prop]
theorem measurable_scalarProjectionEnergy (r : ℝ) (α : Measure ℝ) [SFinite α] :
    Measurable (scalarProjectionEnergy r α) := by
  apply measurable_measure_prodMk_left
    (s := {p : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) |
      |(p.2.1.1 - p.2.1.2) - 2 * p.1 * (p.2.2.1 - p.2.2.2)| ≤ r})
  exact (by fun_prop : Measurable (fun p : ℝ × ((ℝ × ℝ) × (ℝ × ℝ)) =>
    |(p.2.1.1 - p.2.1.2) - 2 * p.1 * (p.2.2.1 - p.2.2.2)|)) measurableSet_Iic

/-- Dividing the original projection by its first coefficient decreases its collision radius. -/
theorem averaged_projection_le_slope_energy {δ : ℝ} (hδ : 0 ≤ δ)
    (α β : Measure ℝ) [SFinite α] [IsProbabilityMeasure β]
    (hβ : β (Icc (1 : ℝ) 2)ᶜ = 0) :
    (∫⁻ p : ℝ × ℝ, ((α.prod α).prod (α.prod α))
      {q : (ℝ × ℝ) × (ℝ × ℝ) |
        |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ} ∂β.prod β) ≤
      ∫⁻ t : ℝ, scalarProjectionEnergy (4 * δ) α t ∂slopeLaw β := by
  rw [slopeLaw, lintegral_map (measurable_scalarProjectionEnergy _ α) measurable_ratioDirection]
  have hfull : ∀ᵐ p ∂β.prod β, p ∈ Icc (1 : ℝ) 2 ×ˢ Icc (1 : ℝ) 2 := by
    rw [ae_iff]
    exact Measure.measure_prod_compl_eq_zero hβ hβ
  apply lintegral_mono_ae
  filter_upwards [hfull] with p hp
  apply measure_mono
  intro q hq
  have hp1 : 0 < p.1 := by linarith [hp.1.1]
  have heq : (q.1.1 - q.1.2) - 2 * ratioDirection p * (q.2.1 - q.2.2) =
      (p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)) / p.1 := by
    unfold ratioDirection
    field_simp [hp1.ne']
  change |(q.1.1 - q.1.2) - 2 * ratioDirection p * (q.2.1 - q.2.2)| ≤ 4 * δ
  rw [heq, abs_div, abs_of_pos hp1]
  apply (div_le_iff₀ hp1).mpr
  exact hq.trans (by nlinarith [hp.1.1])

/-- The ratio-direction distribution, with the exact quantitative bounds used in flattening. -/
theorem ratio_direction_law (s ε δ : ℝ) (_hs : 0 < s) (hs1 : s ≤ 1)
    (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (β : Measure ℝ) [IsProbabilityMeasure β]
    (hβ : β (Icc (1 : ℝ) 2)ᶜ = 0)
    (hF : ∀ x u : ℝ, δ ≤ u → u ≤ 1 →
      β (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (δ ^ (-ε) * u ^ s)) :
    ∃ ν : Measure ℝ, IsProbabilityMeasure ν ∧ ν (Icc (1 / 4 : ℝ) 1)ᶜ = 0 ∧
      (∀ x u : ℝ, δ ≤ u → u ≤ 1 →
        ν (Icc (x - u) (x + u)) ≤ ENNReal.ofReal (4 * δ ^ (-ε) * u ^ s)) ∧
      ∀ α : Measure ℝ, IsProbabilityMeasure α →
        (∫⁻ p : ℝ × ℝ, ((α.prod α).prod (α.prod α))
          {q : (ℝ × ℝ) × (ℝ × ℝ) |
            |p.1 * (q.1.1 - q.1.2) - p.2 * (q.2.1 - q.2.2)| ≤ 4 * δ} ∂β.prod β) ≤
          ∫⁻ t : ℝ, ((α.prod α).prod (α.prod α))
            {q : (ℝ × ℝ) × (ℝ × ℝ) |
              |(q.1.1 - q.1.2) - 2 * t * (q.2.1 - q.2.2)| ≤ 4 * δ} ∂ν := by
  have hC : 1 ≤ δ ^ (-ε) := by
    simpa only [Real.rpow_zero] using
      Real.rpow_le_rpow_of_exponent_ge hδ hδ1 (show -ε ≤ 0 by linarith)
  refine ⟨slopeLaw β, slopeLaw_probability β, slopeLaw_support β hβ,
    slopeLaw_frostman hδ hs1 hC β hβ hF, ?_⟩
  intro α hα
  have : IsProbabilityMeasure α := hα
  exact averaged_projection_le_slope_energy hδ.le α β hβ

end Submission.Obl.k4_oss_projection_flattening
