/- Adapted from this LOT tree oai_074_kakeya_four_dimensions, obligation o231,
session x0798, branch x0798, commit fbdba9e7,
Submission/Obl/k4_scalar_capped_heavy_potential/BoundedBase.lean.
Earlier source credits are retained below. -/

import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Module
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Ring

namespace Submission.Obl.k4_scalar_heavy_intercept_selection

open Set MeasureTheory

noncomputable section

/-- An original-prior almost-everywhere line property holds for every
incidence law with the original product-density ceiling. -/
theorem line_property_of_product_domination {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (μ : Measure (α × ℝ)) (K : ENNReal)
    (hdom : μ ≤ K • ν.prod volume) (P : α → Prop) (hP : ∀ᵐ l ∂ν, P l) :
    ∀ᵐ p ∂μ, P p.1 := by
  exact ae_mono hdom (Measure.ae_smul_measure (Measure.quasiMeasurePreserving_fst.ae hP) K)

/-- Bounded affine coordinates may be extended off the incidence
support without changing the original trajectory prior. -/
theorem bounded_base_extension {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (u₀ v₀ : α → ℝ)
    (hu₀ : Measurable u₀) (hv₀ : Measurable v₀) {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ᵐ p ∂μ, |u₀ p.1| ≤ H ∧ |v₀ p.1| ≤ H) :
    ∃ (Λ : Set α) (u v : α → ℝ),
      MeasurableSet Λ ∧ (∀ᵐ p ∂μ, p.1 ∈ Λ) ∧
      Measurable u ∧ Measurable v ∧
      (∀ l, |u l| ≤ H) ∧ (∀ l, |v l| ≤ H) ∧
      ∀ l ∈ Λ, u l = u₀ l ∧ v l = v₀ l := by
  let Λ := {l | |u₀ l| ≤ H ∧ |v₀ l| ≤ H}
  have hΛ : MeasurableSet Λ :=
    (measurableSet_le hu₀.abs measurable_const).inter
      (measurableSet_le hv₀.abs measurable_const)
  refine ⟨Λ, Λ.indicator u₀, Λ.indicator v₀, hΛ, hbound,
    hu₀.indicator hΛ, hv₀.indicator hΛ, ?_, ?_, ?_⟩
  · intro l
    by_cases hl : l ∈ Λ
    · simpa only [indicator_of_mem hl] using hl.1
    · simpa only [indicator_of_notMem hl, abs_zero] using hH
  · intro l
    by_cases hl : l ∈ Λ
    · simpa only [indicator_of_mem hl] using hl.2
    · simpa only [indicator_of_notMem hl, abs_zero] using hH
  · intro l hl
    exact ⟨indicator_of_mem hl _, indicator_of_mem hl _⟩

/-- A whole-block variation bound supplies one globally bounded
measurable intercept, keeping the original incidence measure. -/
theorem exists_bounded_intercept_of_ae_variation {α : Type*} [MeasurableSpace α]
    (μ : Measure (α × ℝ)) (F : α → ℝ → ℝ) (I : Set ℝ) (t₀ : ℝ)
    {H ε : ℝ} (hH : 0 ≤ H) (hF : Measurable (fun l => F l t₀))
    (hbound : ∀ᵐ p ∂μ, |F p.1 t₀| ≤ H)
    (hvariation : ∀ᵐ p ∂μ, ∀ t ∈ I, |F p.1 t - F p.1 t₀| ≤ ε) :
    ∃ c : α → ℝ, Measurable c ∧ (∀ l, |c l| ≤ H) ∧
      ∀ᵐ p ∂μ, ∀ t ∈ I, |F p.1 t - c p.1| ≤ ε := by
  obtain ⟨Λ, c, v, hΛ, hΛμ, hc, hv, hbc, hbv, heq⟩ :=
    bounded_base_extension μ (fun l => F l t₀) (fun _ => 0) hF measurable_const hH
      (by
        filter_upwards [hbound] with p hp
        exact ⟨hp, by simpa only [abs_zero] using hH⟩)
  refine ⟨c, hc, hbc, ?_⟩
  filter_upwards [hΛμ, hvariation] with p hp hvar
  intro t ht
  rw [(heq p.1 hp).1]
  exact hvar t ht

/-- Equal fine physical bins give the expected normalized coordinate
diameter, independently of the origin of the coarse mesh. -/
theorem normalized_base_close_of_fine_code {b h : ℝ} (hb : 0 < b) (hh : 0 < h)
    (z : Fin 2 → ℝ) (x y : Fin 3 → ℝ)
    (hcode : (fun j => (⌊x j / b⌋ : ℤ)) = (fun j => (⌊y j / b⌋ : ℤ)))
    (i : Fin 2) :
    |(y i.castSucc - z i) / h - (x i.castSucc - z i) / h| ≤ b / h := by
  have ht := (Int.abs_sub_lt_one_of_floor_eq_floor (congrFun hcode i.castSucc)).le
  rw [← sub_div, abs_div, abs_of_pos hb] at ht
  have hxy : |x i.castSucc - y i.castSucc| ≤ b := by
    simpa only [one_mul] using (div_le_iff₀ hb).mp ht
  rw [← sub_div, show y i.castSucc - z i - (x i.castSucc - z i) =
    -(x i.castSucc - y i.castSucc) by ring, abs_div, abs_neg, abs_of_pos hh]
  exact div_le_div_of_nonneg_right hxy hh.le

end
end Submission.Obl.k4_scalar_heavy_intercept_selection
