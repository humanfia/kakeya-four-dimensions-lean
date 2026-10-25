/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/PositiveCodes.lean.
Earlier source credits are retained below. -/

import Mathlib
import Submission.Obl.k4_scalar_heavy_intercept_selection.SupportCounting

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open MeasureTheory Set

noncomputable section

/-- A positive original fiber contains a point outside every specified
original null exception. The good property need not be measurable. -/
theorem exists_good_in_positive_code {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → Q) (q : Q) (hpos : μ (code ⁻¹' {q}) ≠ 0)
    (Good : Ω → Prop) (hGood : ∀ᵐ p ∂μ, Good p) :
    ∃ p, Good p ∧ code p = q := by
  by_contra h
  apply hpos
  apply measure_mono_null (t := {p | ¬Good p}) _ (ae_iff.mp hGood)
  intro p hp hgood
  exact h ⟨p, hgood, hp⟩

/-- A finite list containing every positive original code is conull
for that original law. -/
theorem ae_mem_finite_positive_codes {Ω Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ : Measure Ω) (code : Ω → Q) (hc : Measurable code) (F : Finset Q)
    (hF : ∀ q, μ (code ⁻¹' {q}) ≠ 0 → q ∈ F) :
    ∀ᵐ p ∂μ, code p ∈ F := by
  have hmap : ∀ᵐ q ∂μ.map code, (μ.map code) {q} ≠ 0 :=
    ae_iff_of_countable.mpr (fun q hq => hq)
  have hpull := ae_of_ae_map hc.aemeasurable hmap
  filter_upwards [hpull] with p hp
  apply hF
  simpa only [Measure.map_apply hc (measurableSet_singleton _)] using hp

/-- Actual positive group-cell masses supply all the witnesses in the
finite joint-support budget. This keeps the original incidence law and
all its null exceptions throughout the counting argument. -/
theorem measured_group_cell_budget {Ω G B J O : Type*}
    [MeasurableSpace Ω] [DecidableEq G] [DecidableEq B] [DecidableEq J] [DecidableEq O]
    (μ : Measure Ω) (ν : G → Measure Ω)
    (groups : Finset G) (base : G → Finset B) (joints : Finset J) (offsets : Finset O)
    (group : Ω → G) (assigned : Ω → B) (joint : Ω → J)
    (allowed : J → Finset G) (encode : J → O → B) {D : ℝ}
    (hD : ∀ j ∈ joints, ((allowed j).card : ℝ) ≤ D)
    (hdom : ∀ g ∈ groups, ν g ≤ μ)
    (hgroup : ∀ g ∈ groups, ∀ᵐ p ∂ν g, group p = g)
    (hgood : ∀ᵐ p ∂μ, joint p ∈ joints ∧ group p ∈ allowed (joint p) ∧
      ∃ o ∈ offsets, assigned p = encode (joint p) o)
    (hpositive : ∀ g ∈ groups, ∀ b ∈ base g, ν g (assigned ⁻¹' {b}) ≠ 0) :
    (∑ g ∈ groups, ((base g).card : ℝ)) ≤
      (joints.card : ℝ) * offsets.card * D := by
  apply group_base_cell_budget groups base joints offsets allowed encode hD
  intro g hg b hb
  have ha := (hgroup g hg).and (ae_mono (hdom g hg) hgood)
  obtain ⟨p, hp, hpb⟩ := exists_good_in_positive_code (ν g) assigned b (hpositive g hg b hb) _ ha
  obtain ⟨hpg, hpj, hallowed, o, ho, hencode⟩ := hp
  refine ⟨joint p, hpj, o, ho, ?_, ?_⟩
  · simpa only [hpg] using hallowed
  · exact hpb.symm.trans hencode


/-- Keep exactly the positive original fibers of a finite carrier. -/
def positiveCodeWindow {Ω Q : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (code : Ω → Q) (F : Finset Q) : Finset Q := by
  classical
  exact F.filter (fun q => μ (code ⁻¹' {q}) ≠ 0)

theorem ae_mem_positiveCodeWindow {Ω Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q] [Countable Q]
    (μ σ : Measure Ω) (hσμ : σ ≤ μ) (code : Ω → Q) (hc : Measurable code)
    (F : Finset Q) (hcarrier : ∀ᵐ p ∂μ, code p ∈ F) :
    ∀ᵐ p ∂σ, code p ∈ positiveCodeWindow σ code F := by
  classical
  apply ae_mem_finite_positive_codes σ code hc
  intro q hq
  obtain ⟨p, hp, hpq⟩ := exists_good_in_positive_code σ code q hq _ (ae_mono hσμ hcarrier)
  apply Finset.mem_filter.mpr
  exact ⟨by simpa only [hpq] using hp, hq⟩

/-- Summing the real masses of any finite conull code carrier preserves
the exact original total mass. -/
theorem sum_real_mass_finite_codes {Ω Q : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Q] [MeasurableSingletonClass Q]
    (μ : Measure Ω) [IsFiniteMeasure μ] (code : Ω → Q) (hc : Measurable code)
    (F : Finset Q) (hcarrier : ∀ᵐ p ∂μ, code p ∈ F) :
    (∑ q ∈ F, (μ (code ⁻¹' {q})).toReal) = (μ univ).toReal := by
  have hcover : μ (code ⁻¹' (F : Set Q)) = μ univ := by
    apply measure_congr
    filter_upwards [hcarrier] with p hp
    simp only [mem_preimage, Finset.mem_coe, hp, mem_univ]
  have h := sum_measure_preimage_singleton (μ := μ) F
    (fun q _ => hc (measurableSet_singleton q))
  rw [hcover] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun q hq => measure_ne_top _ _)] at hr
  exact hr

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
