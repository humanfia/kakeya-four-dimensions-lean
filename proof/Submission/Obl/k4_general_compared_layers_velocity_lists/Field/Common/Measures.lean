-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Common.Measures; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
/- Written for obligation o254 (k4_general_parent_wide_layer_candidates), session x0900. -/
import Mathlib

/-!
# Generic measure tools for the common-field application

* `keepSet`: the states of a finite measure keeping at least half of their mass inside a set
  `G`; restricting to the kept states inside `G` keeps, in every state, nothing or at least half
  of its mass (`keepSet_half`), and loses at most three times the mass outside `G`
  (`keepSet_mass`).
* `half_domination`: conditional domination survives keeping nothing or at least half of every
  state, with a factor two.
* `refine_domination`: conditional domination at a countable state passes to every coarser
  state `Ψ ∘ state`.
* `timeEquiv`: the affine time normalization `(l, t) ↦ (l, (t - t₀) / q)` as a measurable
  equivalence; it scales the product with Lebesgue measure by `q`.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace FieldCommon

/-! ### Keeping half of every state -/

/-- The points whose state keeps at least half of its mass inside `G`. -/
def keepSet {Ω S : Type*} [MeasurableSpace Ω] (θ : Measure Ω) (state : Ω → S) (G : Set Ω) :
    Set Ω :=
  state ⁻¹' {σ | 2 * θ (state ⁻¹' {σ} ∩ Gᶜ) ≤ θ (state ⁻¹' {σ})}

theorem measurableSet_keepSet {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S] (θ : Measure Ω) {state : Ω → S}
    (hstate : Measurable state) (G : Set Ω) : MeasurableSet (keepSet θ state G) :=
  hstate (Set.to_countable _).measurableSet

theorem keepSet_half {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S] (θ : Measure Ω) [IsFiniteMeasure θ]
    {state : Ω → S} (hstate : Measurable state) {G : Set Ω} (hG : MeasurableSet G) (σ : S) :
    (θ.restrict (keepSet θ state G ∩ G)) (state ⁻¹' {σ}) = 0 ∨
      θ (state ⁻¹' {σ}) ≤ 2 * (θ.restrict (keepSet θ state G ∩ G)) (state ⁻¹' {σ}) := by
  have hσ : MeasurableSet (state ⁻¹' {σ}) := hstate (measurableSet_singleton σ)
  rw [Measure.restrict_apply hσ]
  by_cases hk : 2 * θ (state ⁻¹' {σ} ∩ Gᶜ) ≤ θ (state ⁻¹' {σ})
  · right
    have hsub : state ⁻¹' {σ} ⊆ keepSet θ state G := by
      intro ω hω
      simp only [mem_preimage, mem_singleton_iff] at hω
      simp only [keepSet, mem_preimage, mem_ofPred_eq, hω]
      exact hk
    have heq : state ⁻¹' {σ} ∩ (keepSet θ state G ∩ G) = state ⁻¹' {σ} ∩ G := by
      ext ω
      constructor
      · rintro ⟨h1, -, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨h1, hsub h1, h3⟩
    rw [heq]
    have hsplit : θ (state ⁻¹' {σ}) = θ (state ⁻¹' {σ} ∩ G) + θ (state ⁻¹' {σ} ∩ Gᶜ) := by
      rw [← measure_inter_add_sdiff (state ⁻¹' {σ}) hG, sdiff_eq]
    have hfin : θ (state ⁻¹' {σ} ∩ Gᶜ) ≠ ∞ := measure_ne_top _ _
    have hbad : θ (state ⁻¹' {σ} ∩ Gᶜ) ≤ θ (state ⁻¹' {σ} ∩ G) := by
      have h2 : 2 * θ (state ⁻¹' {σ} ∩ Gᶜ) =
          θ (state ⁻¹' {σ} ∩ Gᶜ) + θ (state ⁻¹' {σ} ∩ Gᶜ) := two_mul _
      rw [h2, hsplit, add_comm (θ (state ⁻¹' {σ} ∩ G))] at hk
      exact (ENNReal.add_le_add_iff_left hfin).mp hk
    calc θ (state ⁻¹' {σ}) = θ (state ⁻¹' {σ} ∩ G) + θ (state ⁻¹' {σ} ∩ Gᶜ) := hsplit
      _ ≤ θ (state ⁻¹' {σ} ∩ G) + θ (state ⁻¹' {σ} ∩ G) := add_le_add le_rfl hbad
      _ = 2 * θ (state ⁻¹' {σ} ∩ G) := (two_mul _).symm
  · left
    have hempty : state ⁻¹' {σ} ∩ (keepSet θ state G ∩ G) = ∅ := by
      ext ω
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, keepSet, mem_ofPred_eq,
        mem_empty_iff_false, iff_false, not_and]
      intro hω hkeep
      rw [hω] at hkeep
      exact absurd hkeep hk
    rw [hempty, measure_empty]

theorem keepSet_mass {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S] (θ : Measure Ω) [IsFiniteMeasure θ]
    {state : Ω → S} (hstate : Measurable state) {G : Set Ω} (hG : MeasurableSet G) :
    θ univ ≤ θ (keepSet θ state G ∩ G) + 3 * θ Gᶜ := by
  classical
  set T : Set S := {σ | 2 * θ (state ⁻¹' {σ} ∩ Gᶜ) ≤ θ (state ⁻¹' {σ})} with hT
  have hkeep : keepSet θ state G = state ⁻¹' T := rfl
  have hsing : ∀ y ∈ Tᶜ, MeasurableSet (state ⁻¹' {y}) :=
    fun y _ => hstate (measurableSet_singleton y)
  have hdrop : θ (keepSet θ state G)ᶜ ≤ 2 * θ Gᶜ := by
    rw [hkeep, ← preimage_compl]
    rw [← tsum_measure_preimage_singleton (Set.to_countable Tᶜ) hsing]
    have hterm : ∀ y : (Tᶜ : Set S), θ (state ⁻¹' {(y : S)}) ≤
        2 * (θ.restrict Gᶜ) (state ⁻¹' {(y : S)}) := by
      intro y
      have hy : ¬ (2 * θ (state ⁻¹' {(y : S)} ∩ Gᶜ) ≤ θ (state ⁻¹' {(y : S)})) := y.2
      rw [Measure.restrict_apply (hstate (measurableSet_singleton _))]
      exact (not_le.mp hy).le
    calc ∑' y : (Tᶜ : Set S), θ (state ⁻¹' {(y : S)}) ≤
          ∑' y : (Tᶜ : Set S), 2 * (θ.restrict Gᶜ) (state ⁻¹' {(y : S)}) :=
          ENNReal.tsum_le_tsum hterm
      _ = 2 * ∑' y : (Tᶜ : Set S), (θ.restrict Gᶜ) (state ⁻¹' {(y : S)}) :=
          ENNReal.tsum_mul_left
      _ = 2 * (θ.restrict Gᶜ) (state ⁻¹' Tᶜ) := by
          rw [tsum_measure_preimage_singleton (Set.to_countable Tᶜ) hsing]
      _ ≤ 2 * θ Gᶜ := by
          have h1 : (θ.restrict Gᶜ) (state ⁻¹' Tᶜ) ≤ θ Gᶜ := by
            rw [Measure.restrict_apply (hstate (Set.to_countable Tᶜ).measurableSet)]
            exact measure_mono inter_subset_right
          exact mul_le_mul' le_rfl h1
  have hK : MeasurableSet (keepSet θ state G) := measurableSet_keepSet θ hstate G
  calc θ univ = θ (keepSet θ state G ∩ G) + θ (keepSet θ state G ∩ G)ᶜ :=
        (measure_add_measure_compl (hK.inter hG)).symm
    _ ≤ θ (keepSet θ state G ∩ G) + (θ (keepSet θ state G)ᶜ + θ Gᶜ) := by
        gcongr
        rw [compl_inter]
        exact measure_union_le _ _
    _ ≤ θ (keepSet θ state G ∩ G) + (2 * θ Gᶜ + θ Gᶜ) := by gcongr
    _ = θ (keepSet θ state G ∩ G) + 3 * θ Gᶜ := by
        congr 1
        ring

/-! ### Conditional domination -/

/-- Keeping nothing or at least half of every state preserves conditional domination with a
factor two. -/
theorem half_domination {Ω S V : Type*} [MeasurableSpace Ω] (θ current : Measure Ω)
    (hsub : current ≤ θ) (state : Ω → S) (ctrl : Ω → V) (πv : V → ℝ≥0∞) (C : ℝ≥0∞)
    (hhalf : ∀ σ, current (state ⁻¹' {σ}) = 0 ∨
      θ (state ⁻¹' {σ}) ≤ 2 * current (state ⁻¹' {σ}))
    (hdom : ∀ σ v, θ {ω | state ω = σ ∧ ctrl ω = v} ≤ C * θ {ω | state ω = σ} * πv v)
    (σ : S) (v : V) :
    current {ω | state ω = σ ∧ ctrl ω = v} ≤ 2 * C * current {ω | state ω = σ} * πv v := by
  rcases hhalf σ with hz | hh
  · have hz' : current {ω | state ω = σ} = 0 := hz
    have h0 : current {ω | state ω = σ ∧ ctrl ω = v} = 0 :=
      measure_mono_null (fun ω hω => hω.1) hz'
    rw [h0]
    exact bot_le
  · have hh' : θ {ω | state ω = σ} ≤ 2 * current {ω | state ω = σ} := hh
    calc current {ω | state ω = σ ∧ ctrl ω = v} ≤ θ {ω | state ω = σ ∧ ctrl ω = v} := hsub _
      _ ≤ C * θ {ω | state ω = σ} * πv v := hdom σ v
      _ ≤ C * (2 * current {ω | state ω = σ}) * πv v := by gcongr
      _ = 2 * C * current {ω | state ω = σ} * πv v := by ring

/-- Conditional domination at a countable state passes to every coarser state. -/
theorem refine_domination {Ω S T V : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    [Countable S] [MeasurableSingletonClass S] (θ : Measure Ω) {state : Ω → S}
    (hstate : Measurable state) {ctrl : Ω → V} (πv : V → ℝ≥0∞) (C : ℝ≥0∞)
    (hdom : ∀ σ v, θ {ω | state ω = σ ∧ ctrl ω = v} ≤ C * θ {ω | state ω = σ} * πv v)
    (Ψ : S → T) (q : T) (v : V) :
    θ {ω | Ψ (state ω) = q ∧ ctrl ω = v} ≤ C * θ {ω | Ψ (state ω) = q} * πv v := by
  set s : Set S := Ψ ⁻¹' {q} with hs
  have hcount : s.Countable := Set.to_countable s
  have hsing : ∀ y ∈ s, MeasurableSet (state ⁻¹' {y}) :=
    fun y _ => hstate (measurableSet_singleton y)
  have hS : MeasurableSet (state ⁻¹' s) := hstate hcount.measurableSet
  have h1 : {ω | Ψ (state ω) = q ∧ ctrl ω = v} = state ⁻¹' s ∩ ctrl ⁻¹' {v} := by
    ext ω
    simp [hs]
  have h2 : {ω | Ψ (state ω) = q} = state ⁻¹' s := by
    ext ω
    simp [hs]
  rw [h1, h2]
  have hL : θ (state ⁻¹' s ∩ ctrl ⁻¹' {v}) = (θ.restrict (ctrl ⁻¹' {v})) (state ⁻¹' s) :=
    (Measure.restrict_apply hS).symm
  rw [hL, ← tsum_measure_preimage_singleton hcount hsing,
    ← tsum_measure_preimage_singleton hcount hsing]
  have hterm : ∀ y : s, (θ.restrict (ctrl ⁻¹' {v})) (state ⁻¹' {(y : S)}) ≤
      C * θ (state ⁻¹' {(y : S)}) * πv v := by
    intro y
    rw [Measure.restrict_apply (hstate (measurableSet_singleton _))]
    have h := hdom y v
    have he : {ω | state ω = (y : S) ∧ ctrl ω = v} = state ⁻¹' {(y : S)} ∩ ctrl ⁻¹' {v} := by
      ext ω
      simp
    rw [he] at h
    exact h
  calc ∑' y : s, (θ.restrict (ctrl ⁻¹' {v})) (state ⁻¹' {(y : S)}) ≤
        ∑' y : s, C * θ (state ⁻¹' {(y : S)}) * πv v := ENNReal.tsum_le_tsum hterm
    _ = C * (∑' y : s, θ (state ⁻¹' {(y : S)})) * πv v := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]

/-! ### Time normalization -/

/-- The affine time normalization `(l, t) ↦ (l, (t - t₀) / q)`. -/
def timeEquiv (α : Type*) [MeasurableSpace α] (t₀ q : ℝ) (hq : q ≠ 0) :
    (α × ℝ) ≃ᵐ (α × ℝ) where
  toFun ω := (ω.1, (ω.2 - t₀) / q)
  invFun x := (x.1, t₀ + q * x.2)
  left_inv ω := by
    ext
    · rfl
    · simp only
      field_simp
      ring
  right_inv x := by
    ext
    · rfl
    · simp only
      field_simp
      ring
  measurable_toFun := by
    change Measurable (fun ω : α × ℝ => (ω.1, (ω.2 - t₀) / q))
    fun_prop
  measurable_invFun := by
    change Measurable (fun x : α × ℝ => (x.1, t₀ + q * x.2))
    fun_prop

theorem timeEquiv_apply {α : Type*} [MeasurableSpace α] (t₀ q : ℝ) (hq : q ≠ 0)
    (ω : α × ℝ) : timeEquiv α t₀ q hq ω = (ω.1, (ω.2 - t₀) / q) := rfl

theorem timeEquiv_symm_apply {α : Type*} [MeasurableSpace α] (t₀ q : ℝ) (hq : q ≠ 0)
    (x : α × ℝ) : (timeEquiv α t₀ q hq).symm x = (x.1, t₀ + q * x.2) := rfl

/-- Lebesgue measure under the affine time normalization. -/
theorem map_volume_normalize {t₀ q : ℝ} (hq : 0 < q) :
    (volume : Measure ℝ).map (fun t => (t - t₀) / q) = ENNReal.ofReal q • volume := by
  have hcomp : (fun t : ℝ => (t - t₀) / q) = (fun x => q⁻¹ * x) ∘ (fun x => x + (-t₀)) := by
    funext t
    simp only [Function.comp_apply]
    rw [div_eq_inv_mul, sub_eq_add_neg]
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), map_add_right_eq_self,
    Real.map_volume_mul_left (inv_ne_zero hq.ne'), inv_inv, abs_of_pos hq]

/-- The product of a prior with Lebesgue measure under the affine time normalization. -/
theorem map_prod_timeEquiv {α : Type*} [MeasurableSpace α] (ν : Measure α) [SFinite ν]
    {t₀ q : ℝ} (hq : 0 < q) :
    (ν.prod volume).map (timeEquiv α t₀ q hq.ne') = ENNReal.ofReal q • (ν.prod volume) := by
  have hfun : (timeEquiv α t₀ q hq.ne' : α × ℝ → α × ℝ) =
      Prod.map id (fun t => (t - t₀) / q) := by
    funext ω
    rfl
  rw [hfun, ← Measure.map_prod_map ν volume measurable_id (by fun_prop), Measure.map_id,
    map_volume_normalize hq, Measure.prod_smul_right]

/-- Almost-everywhere statements pass to a scaled normalized law. -/
theorem ae_scaled_map {Ω : Type*} [MeasurableSpace Ω] {law : Measure Ω} (M : Ω ≃ᵐ Ω)
    (c : ℝ≥0∞) {P : Ω → Prop} (h : ∀ᵐ ω ∂law, P (M ω)) : ∀ᵐ x ∂(c • law.map M), P x := by
  apply Measure.ae_smul_measure _ c
  rw [← M.map_ae]
  exact Filter.eventually_map.mpr h

theorem scaled_map_apply {Ω : Type*} [MeasurableSpace Ω] (law : Measure Ω) (M : Ω ≃ᵐ Ω)
    (c : ℝ≥0∞) (X : Set Ω) : (c • law.map M) X = c * law (M ⁻¹' X) := by
  rw [Measure.smul_apply, smul_eq_mul, M.map_apply]

end FieldCommon

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
