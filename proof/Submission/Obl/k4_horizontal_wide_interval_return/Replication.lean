import Mathlib

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- An independent uniform mark splits the first color without changing the
second marginal or the total pair mass. -/
def uniformMark (m : ℕ) : Measure (Fin m) := (m : ℝ≥0∞)⁻¹ • Measure.count

theorem uniformMark_singleton {m : ℕ} (i : Fin m) :
    uniformMark m {i} = (m : ℝ≥0∞)⁻¹ := by
  simp [uniformMark, Measure.smul_apply, smul_eq_mul]

theorem uniformMark_univ {m : ℕ} (hm : 0 < m) : uniformMark m univ = 1 := by
  have hcount : Measure.count (univ : Set (Fin m)) = (m : ℝ≥0∞) := by
    simpa using (Measure.count_apply_finset (Finset.univ : Finset (Fin m)))
  rw [uniformMark, Measure.smul_apply, smul_eq_mul, hcount,
    ENNReal.inv_mul_cancel (by exact_mod_cast hm.ne') (ENNReal.natCast_ne_top m)]

theorem uniformMark_probability {m : ℕ} (hm : 0 < m) :
    IsProbabilityMeasure (uniformMark m) := ⟨uniformMark_univ hm⟩

def replicatedLaw {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (m : ℕ) :
    Measure (Ω × Fin m) := μ.prod (uniformMark m)

theorem replicatedLaw_cylinder {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {m : ℕ} (hm : 0 < m) (E : Set Ω) :
    replicatedLaw μ m (E ×ˢ univ) = μ E := by
  haveI := uniformMark_probability hm
  simp [replicatedLaw, Measure.prod_prod]

theorem replicatedLaw_slice {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) {m : ℕ} (hm : 0 < m) (E : Set Ω) (i : Fin m) :
    replicatedLaw μ m (E ×ˢ {i}) = μ E * (m : ℝ≥0∞)⁻¹ := by
  haveI := uniformMark_probability hm
  rw [replicatedLaw, Measure.prod_prod, uniformMark_singleton]

/-- Each duplicated source density is divided by the replication count. -/
theorem replicated_source_cap {Ω Y I : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) (ν : Measure Y) (src : Ω → I) (x : Ω → Y)
    {m : ℕ} (hm : 0 < m) (ρ₁ ρ₂ : ℝ≥0∞)
    (hbalance : ρ₁ * (m : ℝ≥0∞)⁻¹ ≤ ρ₂)
    (hcap : ∀ i (U : Set Y), MeasurableSet U →
      μ {p | src p = i ∧ x p ∈ U} ≤ ρ₁ * ν U)
    (i : I) (a : Fin m) (U : Set Y) (hU : MeasurableSet U) :
    replicatedLaw μ m {p | (src p.1, p.2) = (i, a) ∧ x p.1 ∈ U} ≤ ρ₂ * ν U := by
  have heq : {p : Ω × Fin m | (src p.1, p.2) = (i, a) ∧ x p.1 ∈ U} =
      {p | src p = i ∧ x p ∈ U} ×ˢ {a} := by
    ext p
    simp only [Prod.mk.injEq, mem_setOf_eq, mem_prod, mem_singleton_iff]
    tauto
  rw [heq, replicatedLaw_slice μ hm]
  calc μ {p | src p = i ∧ x p ∈ U} * (m : ℝ≥0∞)⁻¹
      ≤ (ρ₁ * ν U) * (m : ℝ≥0∞)⁻¹ := mul_le_mul' (hcap i U hU) le_rfl
    _ = (ρ₁ * (m : ℝ≥0∞)⁻¹) * ν U := by ring
    _ ≤ ρ₂ * ν U := mul_le_mul' hbalance le_rfl

/-- The witness-color density stays unchanged by source replication. -/
theorem replicated_witness_cap {Ω Y I : Type*} [MeasurableSpace Ω] [MeasurableSpace Y]
    (μ : Measure Ω) (ν : Measure Y) (wit : Ω → I) (x : Ω → Y)
    {m : ℕ} (hm : 0 < m) (ρ : ℝ≥0∞)
    (hcap : ∀ i (U : Set Y), MeasurableSet U →
      μ {p | wit p = i ∧ x p ∈ U} ≤ ρ * ν U)
    (i : I) (U : Set Y) (hU : MeasurableSet U) :
    replicatedLaw μ m {p | wit p.1 = i ∧ x p.1 ∈ U} ≤ ρ * ν U := by
  have heq : {p : Ω × Fin m | wit p.1 = i ∧ x p.1 ∈ U} =
      {p | wit p = i ∧ x p ∈ U} ×ˢ univ := by
    ext p
    simp
  rw [heq, replicatedLaw_cylinder μ hm]
  exact hcap i U hU

/-- The least integer replication count has at most a factor-two reference
cost, even when the ratio of the layer thickness weights is a power of N. -/
theorem replication_count {r : ℝ} (hr : 1 ≤ r) :
    0 < ⌈r⌉₊ ∧ r ≤ (⌈r⌉₊ : ℝ) ∧ (⌈r⌉₊ : ℝ) ≤ 2 * r := by
  refine ⟨Nat.ceil_pos.mpr (by linarith), Nat.le_ceil r, ?_⟩
  have := Nat.ceil_lt_add_one (show 0 ≤ r by linarith)
  linarith

theorem replication_reference_cost {T₁ T₂ : ℝ} (hT₂ : 0 < T₂) (hT : T₂ ≤ T₁) :
    let m := ⌈T₁ / T₂⌉₊
    0 < m ∧ T₁ / (m : ℝ) ≤ T₂ ∧ (m : ℝ) * T₂ ≤ 2 * T₁ := by
  have hr : 1 ≤ T₁ / T₂ := (le_div_iff₀ hT₂).mpr (by simpa using hT)
  obtain ⟨hm, hlo, hhi⟩ := replication_count hr
  refine ⟨hm, ?_, ?_⟩
  · rw [div_le_iff₀ (by exact_mod_cast hm : (0 : ℝ) < ⌈T₁ / T₂⌉₊)]
    exact ((div_le_iff₀ hT₂).mp hlo).trans_eq (mul_comm _ _)
  · have := mul_le_mul_of_nonneg_right hhi hT₂.le
    calc (⌈T₁ / T₂⌉₊ : ℝ) * T₂ ≤ (2 * (T₁ / T₂)) * T₂ := this
      _ = 2 * T₁ := by field_simp

end

end Submission.Obl.k4_horizontal_wide_interval_return
