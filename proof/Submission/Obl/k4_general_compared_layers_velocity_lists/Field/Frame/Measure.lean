-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Field.Frame.Measure; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Field.Interfaces

/-!
# The normalized law of one original block

A submeasure `law` of the original incidence measure, supported on the incidences of one
original true block `Q`, is normalized to the unit time of `Q`
(`t ↦ (t - t₀) / q`) and divided by the original reference `2^(-T) ν(A_Q)` of `Q`.
Against the conditioned prior `ν(· | A_Q)` this normalized law has the density bound of
the original measure, and it pushes back exactly to the original submeasure.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Parent.FieldFrame

variable {α : Type} [MeasurableSpace α]

/-- Normalization of physical time to the unit time of a block. -/
def normTime (t₀ q : ℝ) (ω : α × ℝ) : α × ℝ := (ω.1, (ω.2 - t₀) / q)

theorem measurable_normTime (t₀ q : ℝ) : Measurable (normTime (α := α) t₀ q) := by
  unfold normTime
  fun_prop

theorem measurableEmbedding_normTime {t₀ q : ℝ} (hq : q ≠ 0) :
    MeasurableEmbedding (normTime (α := α) t₀ q) := by
  refine MeasurableEmbedding.of_measurable_inverse
    (g := fun ω : α × ℝ => (ω.1, t₀ + q * ω.2))
    (measurable_normTime t₀ q) ?_ (by fun_prop) ?_
  · have : range (normTime (α := α) t₀ q) = univ := by
      apply eq_univ_of_forall
      intro ω
      refine ⟨(ω.1, t₀ + q * ω.2), ?_⟩
      simp only [normTime]
      congr 1
      field_simp
      ring
    rw [this]
    exact MeasurableSet.univ
  · intro ω
    simp only [normTime]
    congr 1
    field_simp
    ring

theorem map_volume_affine {t₀ q : ℝ} (hq : 0 < q) :
    (volume : Measure ℝ).map (fun t => (t - t₀) / q) = ENNReal.ofReal q • volume := by
  have h1 : (fun t : ℝ => (t - t₀) / q) = (fun x => q⁻¹ * x) ∘ (fun t => t + (-t₀)) := by
    funext t
    simp [div_eq_inv_mul, sub_eq_add_neg]
  rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop), map_add_right_eq_self,
    Real.map_volume_mul_left (inv_ne_zero hq.ne'), inv_inv, abs_of_pos hq]

theorem map_prod_normTime (ν : Measure α) [SFinite ν] {t₀ q : ℝ} (hq : 0 < q) :
    (ν.prod volume).map (normTime t₀ q) = ENNReal.ofReal q • ν.prod volume := by
  have : normTime (α := α) t₀ q = Prod.map id (fun t => (t - t₀) / q) := rfl
  rw [this, ← Measure.map_prod_map _ _ measurable_id (by fun_prop), Measure.map_id,
    map_volume_affine hq, Measure.prod_smul_right]

/-- The original prior conditioned on a set. -/
def condPrior (ν : Measure α) (A : Set α) : Measure α := (ν A)⁻¹ • ν.restrict A

theorem condPrior_prob (ν : Measure α) {A : Set α} (h0 : ν A ≠ 0) (htop : ν A ≠ ⊤) :
    IsProbabilityMeasure (condPrior ν A) := by
  constructor
  rw [condPrior, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    smul_eq_mul, ENNReal.inv_mul_cancel h0 htop]

/-- The normalized law of a submeasure on one block. -/
def normLaw (t₀ q : ℝ) (wt : ℝ≥0∞) (law : Measure (α × ℝ)) : Measure (α × ℝ) :=
  wt⁻¹ • law.map (normTime t₀ q)

theorem ae_normLaw {t₀ q : ℝ} (hq : q ≠ 0) (wt : ℝ≥0∞) {law : Measure (α × ℝ)}
    {P : α × ℝ → Prop} (h : ∀ᵐ ω ∂law, P (normTime t₀ q ω)) :
    ∀ᵐ ω ∂normLaw t₀ q wt law, P ω := by
  unfold normLaw
  apply Measure.ae_smul_measure
  exact (measurableEmbedding_normTime hq).ae_map_iff.mpr h

theorem normLaw_univ (t₀ q : ℝ) (wt : ℝ≥0∞) (law : Measure (α × ℝ)) :
    normLaw t₀ q wt law univ = wt⁻¹ * law univ := by
  rw [normLaw, Measure.smul_apply, Measure.map_apply (measurable_normTime t₀ q)
    MeasurableSet.univ, preimage_univ, smul_eq_mul]

/-- The normalized law pushes back exactly to the original submeasure. -/
theorem normLaw_pushback {t₀ q : ℝ} (hq : q ≠ 0) {wt : ℝ≥0∞} (h0 : wt ≠ 0) (htop : wt ≠ ⊤)
    (law : Measure (α × ℝ)) :
    wt • (normLaw t₀ q wt law).map (fun ω => (ω.1, t₀ + q * ω.2)) = law := by
  have hcomp : (fun ω : α × ℝ => (ω.1, t₀ + q * ω.2)) ∘ normTime t₀ q = id := by
    funext ω
    simp only [Function.comp_apply, normTime, id]
    congr 1
    field_simp
    ring
  have hm : Measurable (fun ω : α × ℝ => (ω.1, t₀ + q * ω.2)) := by fun_prop
  rw [normLaw, Measure.map_smul _ hm.aemeasurable, Measure.map_map hm (measurable_normTime t₀ q),
    hcomp, Measure.map_id, smul_smul, ENNReal.mul_inv_cancel h0 htop, one_smul]

/-- The normalized law is supported on unit time when the submeasure is supported on
the block. -/
theorem normLaw_time_support {t₀ q : ℝ} (hq : 0 < q) (wt : ℝ≥0∞) {law : Measure (α × ℝ)}
    (h : ∀ᵐ ω ∂law, ω.2 ∈ Icc t₀ (t₀ + q)) :
    normLaw t₀ q wt law (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 := by
  have hae : ∀ᵐ ω ∂normLaw t₀ q wt law, ω ∈ (univ ×ˢ Icc (0 : ℝ) 1) := by
    apply ae_normLaw hq.ne' wt
    filter_upwards [h] with ω hω
    simp only [normTime, mem_prod, mem_univ, true_and, mem_Icc]
    constructor
    · exact div_nonneg (by linarith [hω.1]) hq.le
    · rw [div_le_one hq]
      linarith [hω.2]
  rw [ae_iff] at hae
  simpa [compl_def] using hae

/-- The density bound of the normalized law against the conditioned prior. -/
theorem normLaw_domination {ν : Measure α} [IsFiniteMeasure ν] {μ law : Measure (α × ℝ)}
    {A : Set α} {t₀ q K : ℝ} (hq : 0 < q)
    (hμ : μ ≤ ENNReal.ofReal K • ν.prod volume) (hlaw : law ≤ μ)
    (hsupp : ∀ᵐ ω ∂law, ω.1 ∈ A) :
    normLaw t₀ q (ENNReal.ofReal q * ν A) law ≤
      ENNReal.ofReal K • (condPrior ν A).prod volume := by
  have hq0 : ENNReal.ofReal q ≠ 0 := by simpa using hq
  have hlaw' : law ≤ ENNReal.ofReal K • (ν.restrict A).prod volume := by
    have hres : law.restrict (A ×ˢ univ) = law := by
      apply Measure.restrict_eq_self_of_ae_mem
      filter_upwards [hsupp] with ω hω
      exact ⟨hω, mem_univ _⟩
    calc law = law.restrict (A ×ˢ univ) := hres.symm
      _ ≤ (ENNReal.ofReal K • ν.prod volume).restrict (A ×ˢ univ) :=
          Measure.restrict_mono subset_rfl (hlaw.trans hμ)
      _ = ENNReal.ofReal K • (ν.restrict A).prod volume := by
          rw [Measure.restrict_smul, Measure.restrict_prod_eq_prod_univ]
  have hmap : law.map (normTime t₀ q) ≤
      ENNReal.ofReal K • (ENNReal.ofReal q • (ν.restrict A).prod volume) := by
    calc law.map (normTime t₀ q)
        ≤ (ENNReal.ofReal K • (ν.restrict A).prod volume).map (normTime t₀ q) :=
          Measure.map_mono hlaw' (measurable_normTime t₀ q)
      _ = ENNReal.ofReal K • (ENNReal.ofReal q • (ν.restrict A).prod volume) := by
          rw [Measure.map_smul _ (measurable_normTime t₀ q).aemeasurable,
            map_prod_normTime _ hq]
  have hscal : (ENNReal.ofReal q * ν A)⁻¹ * (ENNReal.ofReal K * ENNReal.ofReal q) =
      ENNReal.ofReal K * (ν A)⁻¹ := by
    rw [ENNReal.mul_inv (Or.inl hq0) (Or.inl ENNReal.ofReal_ne_top)]
    calc (ENNReal.ofReal q)⁻¹ * (ν A)⁻¹ * (ENNReal.ofReal K * ENNReal.ofReal q)
        = ((ENNReal.ofReal q)⁻¹ * ENNReal.ofReal q) * (ENNReal.ofReal K * (ν A)⁻¹) := by ring
      _ = ENNReal.ofReal K * (ν A)⁻¹ := by
          rw [ENNReal.inv_mul_cancel hq0 ENNReal.ofReal_ne_top, one_mul]
  calc normLaw t₀ q (ENNReal.ofReal q * ν A) law
      ≤ (ENNReal.ofReal q * ν A)⁻¹ •
          (ENNReal.ofReal K • (ENNReal.ofReal q • (ν.restrict A).prod volume)) := by
        unfold normLaw
        exact smul_le_smul_left _ hmap
    _ = ENNReal.ofReal K • (condPrior ν A).prod volume := by
        rw [condPrior, Measure.prod_smul_left, smul_smul, smul_smul, smul_smul, mul_assoc, hscal]

end Parent.FieldFrame

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
