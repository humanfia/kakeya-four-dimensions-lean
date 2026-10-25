import Submission.Obl.k4_scalar_capped_heavy_potential.BaseCap

set_option autoImplicit false

namespace Submission.Obl.k4_physical_row_packet_potential

open Set MeasureTheory
open scoped ENNReal

/-- A cap on countably many refining states passes to any observation they
determine. All masses are taken in the given measure. -/
theorem cap_of_refining_states {Ω σ κ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace σ] [MeasurableSingletonClass σ] [Countable σ]
    (μ : Measure Ω) (st : Ω → σ) (hst : Measurable st) (code : Ω → κ)
    (hrefine : ∀ x y, st x = st y → code x = code y)
    (A : Set Ω) (C : ℝ≥0∞)
    (hcap : ∀ k, μ {x | st x = k ∧ x ∈ A} ≤ C * μ {x | st x = k}) :
    ∀ k, μ {x | code x = k ∧ x ∈ A} ≤ C * μ {x | code x = k} := by
  classical
  intro k
  let L : Set σ := {s | ∃ x, st x = s ∧ code x = k}
  have hpre (x : Ω) : st x ∈ L ↔ code x = k := by
    constructor
    · rintro ⟨y, hy, hycode⟩
      exact (hrefine x y hy.symm).trans hycode
    · intro hx
      exact ⟨x, rfl, hx⟩
  have h := Submission.Obl.k4_scalar_capped_heavy_potential.state_union_event_cap
    μ st hst A C hcap L
  have hcode : st ⁻¹' L = {x | code x = k} := by
    ext x
    exact hpre x
  simpa only [hpre, hcode] using h

/-- Retaining at least half of every state that survives doubles all its
original relative caps. States that disappear have zero numerator. -/
theorem cap_after_half_state_thinning {Ω σ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (st : Ω → σ) (Se S : Set Ω)
    (hSe : MeasurableSet Se) (hS : MeasurableSet S) (hSSe : S ⊆ Se)
    (hhalf : ∀ k, S ∩ st ⁻¹' {k} = ∅ ∨
      μ (Se ∩ st ⁻¹' {k}) ≤ 2 * μ (S ∩ st ⁻¹' {k}))
    (A : Set Ω) (C : ℝ≥0∞)
    (hcap : ∀ k, (μ.restrict Se) {x | st x = k ∧ x ∈ A} ≤
      C * (μ.restrict Se) {x | st x = k}) :
    ∀ k, (μ.restrict S) {x | st x = k ∧ x ∈ A} ≤
      (2 * C) * (μ.restrict S) {x | st x = k} := by
  intro k
  rcases hhalf k with hempty | hret
  · have hnum : {x | st x = k ∧ x ∈ A} ∩ S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨hx, hxS⟩
      have : x ∈ S ∩ st ⁻¹' {k} := ⟨hxS, hx.1⟩
      simpa only [hempty, Set.mem_empty_iff_false] using this
    rw [Measure.restrict_apply' hS, hnum, measure_empty]
    exact zero_le
  · have hden : (μ.restrict Se) {x | st x = k} ≤
        2 * (μ.restrict S) {x | st x = k} := by
      simpa only [Measure.restrict_apply' hSe, Measure.restrict_apply' hS,
        Set.preimage, Set.mem_singleton_iff, inter_comm] using hret
    calc
      _ ≤ (μ.restrict Se) {x | st x = k ∧ x ∈ A} := by
        rw [Measure.restrict_apply' hS, Measure.restrict_apply' hSe]
        exact measure_mono (inter_subset_inter_right _ hSSe)
      _ ≤ C * (μ.restrict Se) {x | st x = k} := hcap k
      _ ≤ C * (2 * (μ.restrict S) {x | st x = k}) := mul_le_mul' le_rfl hden
      _ = _ := by ring

/-- Physical-code breadth follows from original state breadth after a
half-mass thinning in each surviving refining state. -/
theorem refining_cap_after_half_state_thinning {Ω σ κ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace σ] [MeasurableSingletonClass σ] [Countable σ]
    (μ : Measure Ω) (st : Ω → σ) (hst : Measurable st) (code : Ω → κ)
    (hrefine : ∀ x y, st x = st y → code x = code y)
    (Se S : Set Ω) (hSe : MeasurableSet Se) (hS : MeasurableSet S) (hSSe : S ⊆ Se)
    (hhalf : ∀ k, S ∩ st ⁻¹' {k} = ∅ ∨
      μ (Se ∩ st ⁻¹' {k}) ≤ 2 * μ (S ∩ st ⁻¹' {k}))
    (A : Set Ω) (C : ℝ≥0∞)
    (hcap : ∀ k, (μ.restrict Se) {x | st x = k ∧ x ∈ A} ≤
      C * (μ.restrict Se) {x | st x = k}) :
    ∀ k, (μ.restrict S) {x | code x = k ∧ x ∈ A} ≤
      (2 * C) * (μ.restrict S) {x | code x = k} :=
  cap_of_refining_states (μ.restrict S) st hst code hrefine A (2 * C)
    (cap_after_half_state_thinning μ st Se S hSe hS hSSe hhalf A C hcap)

/-- A subsequent half-state thinning is measured against the original
packet when the preceding cut selected whole original states. -/
theorem half_state_thinning_after_whole_states {Ω σ : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (st : Ω → σ) (Se E0 S : Set Ω)
    (hE0Se : E0 ⊆ Se) (hSE0 : S ⊆ E0)
    (hsat : ∀ x ∈ Se, ∀ y ∈ E0, st x = st y → x ∈ E0)
    (hhalf : ∀ k, S ∩ st ⁻¹' {k} = ∅ ∨
      μ (E0 ∩ st ⁻¹' {k}) ≤ 2 * μ (S ∩ st ⁻¹' {k})) :
    ∀ k, S ∩ st ⁻¹' {k} = ∅ ∨
      μ (Se ∩ st ⁻¹' {k}) ≤ 2 * μ (S ∩ st ⁻¹' {k}) := by
  intro k
  by_cases hk : (S ∩ st ⁻¹' {k}).Nonempty
  · obtain ⟨y, hyS, hyk⟩ := hk
    have heq : Se ∩ st ⁻¹' {k} = E0 ∩ st ⁻¹' {k} := by
      apply Set.Subset.antisymm
      · rintro x ⟨hxSe, hxk⟩
        refine ⟨hsat x hxSe y (hSE0 hyS) ?_, hxk⟩
        exact hxk.trans hyk.symm
      · exact inter_subset_inter_left _ hE0Se
    rcases hhalf k with hz | hret
    · exact False.elim (by simpa only [hz, Set.mem_empty_iff_false] using
        (show y ∈ S ∩ st ⁻¹' {k} from ⟨hyS, hyk⟩))
    · exact Or.inr (by rwa [heq])
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hk)

end Submission.Obl.k4_physical_row_packet_potential
