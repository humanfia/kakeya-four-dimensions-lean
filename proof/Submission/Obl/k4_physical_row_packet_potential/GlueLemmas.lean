/-
x1077 (o295). Small measure facts for the row-packet glue:

* `prod_restrict_line_set`: the line law restricted to `A` is the product law
  restricted to `A ×ˢ univ`, so on events whose lines lie in `A` the two agree;
* `restrict_whole_state`, `cap_whole_state`: on a set `E0` of whole states of
  `Se` (every state meeting `E0` keeps all its events of `Se`), each state has
  the same conditional law, so per-state caps pass from `Se` to `E0`.
-/
import Mathlib

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential.Glue

open MeasureTheory Set
open scoped ENNReal

theorem prod_restrict_line_set {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) [SFinite ν]
    (A : Set Λ) :
    (ν.restrict A).prod (volume : Measure ℝ) = (ν.prod volume).restrict (A ×ˢ univ) := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

theorem prod_restrict_line_set_apply {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ)
    [SFinite ν] {A : Set Λ} (hA : MeasurableSet A) {X : Set (Λ × ℝ)} (hX : X ⊆ A ×ˢ univ) :
    ((ν.restrict A).prod (volume : Measure ℝ)) X = (ν.prod volume) X := by
  rw [prod_restrict_line_set, Measure.restrict_apply' (hA.prod MeasurableSet.univ),
    inter_eq_left.mpr hX]

theorem prod_restrict_line_set_real {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ)
    [SFinite ν] {A : Set Λ} (hA : MeasurableSet A) {X : Set (Λ × ℝ)} (hX : X ⊆ A ×ˢ univ) :
    ((ν.restrict A).prod (volume : Measure ℝ)).real X = (ν.prod volume).real X := by
  rw [measureReal_def, measureReal_def, prod_restrict_line_set_apply ν hA hX]

theorem prod_restrict_line_set_restrict {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ)
    [SFinite ν] {A : Set Λ} (hA : MeasurableSet A) {E : Set (Λ × ℝ)} (hE : E ⊆ A ×ˢ univ) :
    ((ν.restrict A).prod (volume : Measure ℝ)).restrict E = (ν.prod volume).restrict E := by
  rw [prod_restrict_line_set, Measure.restrict_restrict' (hA.prod MeasurableSet.univ),
    inter_eq_left.mpr hE]

/-- On whole states, the state laws are unchanged. -/
theorem restrict_whole_state {Ω σ : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (st : Ω → σ)
    {Se E0 : Set Ω} (hSe : MeasurableSet Se) (hE0 : MeasurableSet E0) (hE0Se : E0 ⊆ Se)
    (hsat : ∀ x ∈ Se, ∀ y ∈ E0, st x = st y → x ∈ E0) (D : σ) :
    (∀ X : Set Ω, (μ.restrict E0) (st ⁻¹' {D} ∩ X) = 0) ∨
      (∀ X : Set Ω, (μ.restrict E0) (st ⁻¹' {D} ∩ X) = (μ.restrict Se) (st ⁻¹' {D} ∩ X)) := by
  by_cases hD : ∃ y ∈ E0, st y = D
  · right
    obtain ⟨y, hyE0, hyD⟩ := hD
    intro X
    rw [Measure.restrict_apply' hE0, Measure.restrict_apply' hSe]
    congr 1
    ext x
    constructor
    · rintro ⟨hx, hxE0⟩
      exact ⟨hx, hE0Se hxE0⟩
    · rintro ⟨hx, hxSe⟩
      refine ⟨hx, hsat x hxSe y hyE0 ?_⟩
      rw [show st x = D from hx.1, hyD]
  · left
    intro X
    rw [Measure.restrict_apply' hE0]
    apply measure_mono_null _ (measure_empty (μ := μ))
    rintro x ⟨⟨hxD, -⟩, hxE0⟩
    exact hD ⟨x, hxE0, hxD⟩

/-- Per-state caps pass from `Se` to a set of whole states. -/
theorem cap_whole_state {Ω σ : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (st : Ω → σ)
    {Se E0 : Set Ω} (hSe : MeasurableSet Se) (hE0 : MeasurableSet E0) (hE0Se : E0 ⊆ Se)
    (hsat : ∀ x ∈ Se, ∀ y ∈ E0, st x = st y → x ∈ E0) (D : σ) (X : Set Ω) (c : ℝ≥0∞)
    (hcap : (μ.restrict Se) (st ⁻¹' {D} ∩ X) ≤ c * (μ.restrict Se) (st ⁻¹' {D})) :
    (μ.restrict E0) (st ⁻¹' {D} ∩ X) ≤ c * (μ.restrict E0) (st ⁻¹' {D}) := by
  rcases restrict_whole_state μ st hSe hE0 hE0Se hsat D with h0 | heq
  · rw [h0 X]
    exact zero_le
  · have h1 := heq X
    have h2 := heq univ
    rw [inter_univ] at h2
    rw [h1, h2]
    exact hcap

end Submission.Obl.k4_physical_row_packet_potential.Glue
