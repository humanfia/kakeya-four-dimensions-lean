import Submission.Lib.K4ScalarActualSwitching.BoundedIncidence

/-!
# Time kernels of a block incidence measure

An incidence measure `μ ≤ H • (ν ⊗ dt)` supported in a time block of length
`h` is disintegrated over its line marginal by a Markov time kernel. On lines
of long duration the kernel has density at most `D / h` against Lebesgue
measure, and the short lines carry little incidence mass.
-/

namespace Submission.Obl.k4_scalar_capped_heavy_potential.Cons

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal

/-- A measure dominated by a finite multiple of a finite measure has a
density bounded by that multiple everywhere. -/
theorem exists_bounded_density {α : Type*} [MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure ν] (c : ℝ≥0∞) (hc : c ≠ ∞) (hle : μ ≤ c • ν) :
    ∃ F : α → ℝ≥0∞, Measurable F ∧ (∀ z, F z ≤ c) ∧ ν.withDensity F = μ := by
  have hac : μ ≪ ν := by
    refine Measure.AbsolutelyContinuous.mk fun s _ hs => ?_
    have h := Measure.le_iff'.mp hle s
    rw [Measure.smul_apply, smul_eq_mul, hs, mul_zero] at h
    exact le_antisymm h bot_le
  haveI : IsFiniteMeasure μ := by
    refine ⟨(Measure.le_iff'.mp hle univ).trans_lt ?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) (measure_lt_top ν univ)
  have hrn : μ.rnDeriv ν ≤ᵐ[ν] fun _ => c := by
    apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite (Measure.measurable_rnDeriv μ ν)
    intro s hs _
    rw [Measure.setLIntegral_rnDeriv hac, setLIntegral_const]
    have h := Measure.le_iff'.mp hle s
    rw [Measure.smul_apply, smul_eq_mul] at h
    exact h
  refine ⟨fun z => min (μ.rnDeriv ν z) c, (Measure.measurable_rnDeriv μ ν).min measurable_const,
    fun z => min_le_right _ _, ?_⟩
  have hae : (fun z => min (μ.rnDeriv ν z) c) =ᵐ[ν] μ.rnDeriv ν := by
    filter_upwards [hrn] with z hz
    exact min_eq_left hz
  rw [withDensity_congr_ae hae]
  exact Measure.withDensity_rnDeriv_eq μ ν hac

/-- The uniform probability law on the block `[t₀, t₀ + h]`. -/
noncomputable def blockLaw (t₀ h : ℝ) : Measure ℝ :=
  (ENNReal.ofReal h)⁻¹ • volume.restrict (Icc t₀ (t₀ + h))

theorem blockLaw_isProbability {t₀ h : ℝ} (hh : 0 < h) : IsProbabilityMeasure (blockLaw t₀ h) := by
  constructor
  rw [blockLaw, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply MeasurableSet.univ,
    univ_inter, Real.volume_Icc, show t₀ + h - t₀ = h by ring]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hh).ne' ENNReal.ofReal_ne_top

theorem volume_restrict_block_eq {t₀ h : ℝ} (hh : 0 < h) :
    volume.restrict (Icc t₀ (t₀ + h)) = ENNReal.ofReal h • blockLaw t₀ h := by
  rw [blockLaw, smul_smul, ENNReal.mul_inv_cancel (ENNReal.ofReal_pos.mpr hh).ne'
    ENNReal.ofReal_ne_top, one_smul]

theorem blockLaw_le {t₀ h : ℝ} :
    blockLaw t₀ h ≤ (ENNReal.ofReal h)⁻¹ • volume := by
  rw [blockLaw]
  exact smul_le_smul_left _ Measure.restrict_le_self

/-- A block-supported incidence measure dominated by `H • (ν ⊗ dt)` is
dominated by `H h • (ν ⊗ blockLaw)`. -/
theorem block_domination {X : Type*} [MeasurableSpace X]
    (μ : Measure (X × ℝ)) (ν : Measure X) [SFinite ν] {t₀ h Hd : ℝ} (hh : 0 < h)
    (hdom : μ ≤ ENNReal.ofReal Hd • (ν.prod volume))
    (hsupp : μ (univ ×ˢ Icc t₀ (t₀ + h))ᶜ = 0) :
    μ ≤ ENNReal.ofReal (Hd * h) • (ν.prod (blockLaw t₀ h)) := by
  haveI : IsProbabilityMeasure (blockLaw t₀ h) := blockLaw_isProbability hh
  have hrestrict : μ = μ.restrict (univ ×ˢ Icc t₀ (t₀ + h)) :=
    (Measure.restrict_eq_self_of_ae_mem (mem_ae_iff.mpr hsupp)).symm
  rw [hrestrict]
  calc
    μ.restrict (univ ×ˢ Icc t₀ (t₀ + h)) ≤
        (ENNReal.ofReal Hd • (ν.prod volume)).restrict (univ ×ˢ Icc t₀ (t₀ + h)) :=
      Measure.restrict_mono le_rfl hdom
    _ = ENNReal.ofReal Hd • ((ν.restrict univ).prod (volume.restrict (Icc t₀ (t₀ + h)))) := by
      rw [Measure.restrict_smul, Measure.prod_restrict]
    _ = ENNReal.ofReal (Hd * h) • (ν.prod (blockLaw t₀ h)) := by
      rw [Measure.restrict_univ, volume_restrict_block_eq hh, Measure.prod_smul_right, smul_smul]
      by_cases hHd : 0 ≤ Hd
      · rw [ENNReal.ofReal_mul hHd]
      · have h1 : ENNReal.ofReal Hd = 0 := ENNReal.ofReal_of_nonpos (le_of_not_ge hHd)
        have h2 : ENNReal.ofReal (Hd * h) = 0 :=
          ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hHd) hh.le)
        rw [h1, h2, zero_mul]

/-- **Block disintegration.** A block-supported incidence measure
`μ ≤ Hd • (ν ⊗ dt)` with `ν` finite has a Markov time kernel `κ` with
`μ.fst ⊗ₘ κ = μ`; on a measurable set of long lines `κ ≤ (D/h) • volume`
with `D = Hd h / q`, and the complementary short lines carry incidence
mass at most `q ν(univ)`. -/
theorem block_disintegration {X : Type*} [MeasurableSpace X]
    (μ : Measure (X × ℝ)) (ν : Measure X) [IsFiniteMeasure ν] {t₀ h Hd q : ℝ}
    (hh : 0 < h) (hq : 0 < q)
    (hdom : μ ≤ ENNReal.ofReal Hd • (ν.prod volume))
    (hsupp : μ (univ ×ˢ Icc t₀ (t₀ + h))ᶜ = 0) :
    IsFiniteMeasure μ ∧ ∃ κ : Kernel X ℝ, IsMarkovKernel κ ∧ μ.fst ⊗ₘ κ = μ ∧
      ∃ L : Set X, MeasurableSet L ∧
        (∀ x ∈ L, κ x ≤ ((ENNReal.ofReal h)⁻¹ * ENNReal.ofReal (Hd * h / q)) • volume) ∧
        μ (Prod.fst ⁻¹' Lᶜ) ≤ ENNReal.ofReal q * ν univ := by
  have : IsProbabilityMeasure (blockLaw t₀ h) := blockLaw_isProbability hh
  have hdom' := block_domination μ ν hh hdom hsupp
  obtain ⟨F, hF, hFle, hFeq⟩ := exists_bounded_density μ (ν.prod (blockLaw t₀ h))
    (ENNReal.ofReal (Hd * h)) ENNReal.ofReal_ne_top hdom'
  obtain ⟨hfin, κ, hκ, hjoint, hlong, hshort⟩ :=
    Submission.Lib.K4ScalarActualSwitching.bounded_incidence_disintegration ν (blockLaw t₀ h) F hF
      (ENNReal.ofReal (Hd * h)) ENNReal.ofReal_ne_top hFle
  rw [hFeq] at hfin hjoint hshort
  refine ⟨hfin, κ, hκ, hjoint, Submission.Lib.K4Homogenization.durationRetained (blockLaw t₀ h) F
    univ (ENNReal.ofReal q), Submission.Lib.K4Homogenization.measurableSet_durationRetained _ hF _ _,
    ?_, hshort (ENNReal.ofReal q)⟩
  intro x hx
  have h1 := hlong (ENNReal.ofReal q) (ENNReal.ofReal_pos.mpr hq) x hx
  calc
    κ x ≤ (ENNReal.ofReal (Hd * h) / ENNReal.ofReal q) • blockLaw t₀ h := h1
    _ ≤ (ENNReal.ofReal (Hd * h) / ENNReal.ofReal q) • ((ENNReal.ofReal h)⁻¹ • volume) :=
      smul_le_smul_left _ blockLaw_le
    _ = ((ENNReal.ofReal h)⁻¹ * ENNReal.ofReal (Hd * h / q)) • volume := by
      rw [smul_smul, ENNReal.ofReal_div_of_pos hq, mul_comm]

end Submission.Obl.k4_scalar_capped_heavy_potential.Cons
