/- Consolidated from the unadmitted prototype Submission/Lib/K4ScalarFinalization/FinitePaletteFreeze.lean at 34bf057964440b5ed25e8d148b45315a2683e87d.
Original proof and adaptation credits are retained below. -/

/-
Adapted from: here:o062
Original proof: x0511/c7adae5efc1a19e31a5e4f292e29e5584d20edda, FinitePaletteFreeze.lean.
Generalizes the finite-fiber argument in accepted K4RepresentativeAssembly.FrozenSelection
(here:o114, x0383) to an arbitrary original finite inner law.
-/

import Mathlib

namespace Submission.Lib.K4ScalarCoreTools.Finalization

open Set MeasureTheory

/-- A probability-weighted palette has a section with at least the original
average success, even when the original inner law has small finite mass. -/
theorem exists_finite_original_palette_section {V Θ : Type*}
    [MeasurableSpace V] [MeasurableSpace Θ]
    (π : Measure V) (ν : Measure Θ) [IsProbabilityMeasure π] [IsFiniteMeasure ν]
    (law : Measure (V × Θ)) (S : Set (V × Θ)) (U : Set V)
    (L p : ℝ) (hL : 0 < L) (hp : 0 < p) (hS : MeasurableSet S)
    (hdom : law ≤ ENNReal.ofReal L • (π.prod ν)) (hmass : ENNReal.ofReal p ≤ law S)
    (hgood : ∀ z ∈ S, z.1 ∈ U) :
    ∃ v ∈ U, MeasurableSet (Prod.mk v ⁻¹' S) ∧
      ENNReal.ofReal (p / L) ≤ ν (Prod.mk v ⁻¹' S) ∧
      ν.restrict (Prod.mk v ⁻¹' S) ≤ ν := by
  have hprod : ENNReal.ofReal (p / L) ≤ (π.prod ν) S := by
    rw [ENNReal.ofReal_div_of_pos hL]
    apply (ENNReal.div_le_iff (ENNReal.ofReal_pos.mpr hL).ne' ENNReal.ofReal_ne_top).mpr
    calc
      ENNReal.ofReal p ≤ law S := hmass
      _ ≤ (ENNReal.ofReal L • (π.prod ν)) S := hdom S
      _ = (π.prod ν) S * ENNReal.ofReal L := by
        rw [Measure.smul_apply, smul_eq_mul, mul_comm]
  have hint : (∫⁻ v, ν (Prod.mk v ⁻¹' S) ∂π) ≤ ν univ := by
    calc
      _ ≤ ∫⁻ _v, ν univ ∂π := lintegral_mono fun _ => measure_mono (subset_univ _)
      _ = ν univ := by simp
  obtain ⟨v, _, hv⟩ := exists_notMem_null_lintegral_le
    (ne_of_lt (hint.trans_lt (measure_lt_top ν univ)))
    (by simp : π (∅ : Set V) = 0)
  have hfloor : ENNReal.ofReal (p / L) ≤ ν (Prod.mk v ⁻¹' S) :=
    hprod.trans (by simpa only [Measure.prod_apply hS] using hv)
  have hpos : ν (Prod.mk v ⁻¹' S) ≠ 0 :=
    ne_of_gt ((ENNReal.ofReal_pos.mpr (div_pos hp hL)).trans_le hfloor)
  obtain ⟨θ, hθ⟩ := nonempty_of_measure_ne_zero hpos
  exact ⟨v, hgood (v, θ) hθ, hS.preimage (measurable_const.prodMk measurable_id),
    hfloor, Measure.restrict_le_self⟩

/-- Relative success freezes at the same fraction of the original finite
mass. The original law is never divided by the successful mass. -/
theorem exists_relative_original_palette_section {V Θ : Type*}
    [MeasurableSpace V] [MeasurableSpace Θ]
    (π : Measure V) (ν : Measure Θ) [IsProbabilityMeasure π] [IsFiniteMeasure ν] [NeZero ν]
    (law : Measure (V × Θ)) (S : Set (V × Θ)) (U : Set V)
    (L p : ℝ) (hL : 0 < L) (hp : 0 < p) (hS : MeasurableSet S)
    (hdom : law ≤ ENNReal.ofReal L • (π.prod ν))
    (hmass : ENNReal.ofReal (p * (ν univ).toReal) ≤ law S)
    (hgood : ∀ z ∈ S, z.1 ∈ U) :
    ∃ v ∈ U, MeasurableSet (Prod.mk v ⁻¹' S) ∧
      ENNReal.ofReal ((p / L) * (ν univ).toReal) ≤ ν (Prod.mk v ⁻¹' S) ∧
      ν.restrict (Prod.mk v ⁻¹' S) ≤ ν := by
  have hm : 0 < (ν univ).toReal :=
    ENNReal.toReal_pos (NeZero.ne (ν univ)) (measure_ne_top _ _)
  obtain ⟨v, hU, hmS, hfloor, hrestrict⟩ := exists_finite_original_palette_section
    π ν law S U L (p * (ν univ).toReal) hL (mul_pos hp hm) hS hdom hmass hgood
  refine ⟨v, hU, hmS, ?_, hrestrict⟩
  simpa only [div_mul_eq_mul_div] using hfloor

end Submission.Lib.K4ScalarCoreTools.Finalization
