/- Adapted within this LOT tree from o218/x0764, commit a57aabc6806d303a53728cab0d5e6ea27469d825,
Submission/Obl/k4_horizontal_endpoint_wide_return/Wide/BlockRescale.lean. -/
import Mathlib

set_option linter.unusedVariables false

/-!
# Rescaling a time block and conditioning on a trajectory set

Scalar mesh projection is stated for incidence laws on unit time, dominated by a probability
prior times Lebesgue measure.  Inside a true label one has instead an incidence law `λ`
supported on `A × [t₀, t₀ + q]`, dominated by `C · ν ⊗ dt` for the original prior `ν`.
The affine change of time `t ↦ (t - t₀)/q` and division by `q ν(A)` turn it into a law
dominated by `C` times the conditional prior `ν(· | A)` times Lebesgue measure, with masses
divided by `q ν(A)`.  This file records that bookkeeping once (rate-free).
-/

namespace Submission.Obl.k4_horizontal_wide_interval_return

open MeasureTheory Set
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- The affine rescaling of the time block `[t₀, t₀ + q]` to unit time. -/
noncomputable def blockRescale (t₀ q : ℝ) (p : α × ℝ) : α × ℝ := (p.1, (p.2 - t₀) / q)

theorem measurable_blockRescale (t₀ q : ℝ) : Measurable (blockRescale (α := α) t₀ q) :=
  measurable_fst.prodMk ((measurable_snd.sub_const t₀).div_const q)

omit [MeasurableSpace α] in
theorem blockRescale_eq_prodMap (t₀ q : ℝ) :
    blockRescale (α := α) t₀ q = Prod.map id (fun t : ℝ => (t - t₀) / q) := rfl

/-- Lebesgue measure pushed through `t ↦ (t - t₀)/q` is `q` times Lebesgue measure. -/
theorem map_volume_block (t₀ q : ℝ) (hq : 0 < q) :
    (volume : Measure ℝ).map (fun t => (t - t₀) / q) = ENNReal.ofReal q • volume := by
  have h1 : (fun t : ℝ => (t - t₀) / q) = (fun x => q⁻¹ * x) ∘ (fun t => t + -t₀) := by
    funext t; simp [div_eq_inv_mul, sub_eq_add_neg]
  rw [h1, ← Measure.map_map (measurable_const_mul _) (measurable_add_const (-t₀)),
    Measure.IsAddRightInvariant.map_add_right_eq_self (-t₀),
    Real.map_volume_mul_left (inv_ne_zero hq.ne'), inv_inv, abs_of_pos hq]

/-- A law supported on `A × ℝ` and dominated by `C · ν ⊗ dt`, rescaled in time from a block of
length `q`, is dominated by `C q · ν|_A ⊗ dt`. -/
theorem map_blockRescale_le (ν : Measure α) [SFinite ν] {A : Set α} (hA : MeasurableSet A)
    (t₀ q : ℝ) (hq : 0 < q) (lam : Measure (α × ℝ)) (C : ℝ≥0∞)
    (hlam : lam ≤ C • ν.prod volume) (hsupp : ∀ᵐ p ∂lam, p.1 ∈ A) :
    lam.map (blockRescale t₀ q) ≤ (C * ENNReal.ofReal q) • (ν.restrict A).prod volume := by
  have hres : lam = lam.restrict (A ×ˢ univ) :=
    (Measure.restrict_eq_self_of_ae_mem (by
      filter_upwards [hsupp] with p hp using ⟨hp, mem_univ _⟩)).symm
  have h1 : lam ≤ C • (ν.restrict A).prod volume := by
    have h2 := Measure.restrict_mono (subset_refl (A ×ˢ (univ : Set ℝ))) hlam
    rw [Measure.restrict_smul, ← Measure.restrict_prod_eq_prod_univ] at h2
    rw [hres]
    exact h2
  calc lam.map (blockRescale t₀ q)
      ≤ (C • (ν.restrict A).prod volume).map (blockRescale t₀ q) :=
        Measure.map_mono h1 (measurable_blockRescale t₀ q)
    _ = C • ((ν.restrict A).map id).prod ((volume : Measure ℝ).map fun t => (t - t₀) / q) := by
        rw [Measure.map_smul C (measurable_blockRescale t₀ q).aemeasurable, blockRescale_eq_prodMap,
          ← Measure.map_prod_map (f := id) (g := fun t : ℝ => (t - t₀) / q) _ _ measurable_id
            ((measurable_sub_const t₀).div_const q)]
    _ = (C * ENNReal.ofReal q) • (ν.restrict A).prod volume := by
        rw [Measure.map_id, map_volume_block t₀ q hq, Measure.prod_smul_right, smul_smul]

/-- The conditional prior `ν(· | A) = ν(A)⁻¹ ν|_A` is a probability measure when
`0 < ν A < ∞`. -/
theorem isProbabilityMeasure_cond (ν : Measure α) {A : Set α} (h0 : ν A ≠ 0) (htop : ν A ≠ ∞) :
    IsProbabilityMeasure ((ν A)⁻¹ • ν.restrict A) := by
  constructor
  rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter, smul_eq_mul,
    ENNReal.inv_mul_cancel h0 htop]

/-- Rescaled and normalized by `q ν(A)`, a law dominated by `C · ν ⊗ dt` and supported on
`A × ℝ` is dominated by `C` times the conditional prior times Lebesgue measure. -/
theorem normalized_blockRescale_le (ν : Measure α) [SFinite ν] {A : Set α} (hA : MeasurableSet A)
    (h0 : ν A ≠ 0) (htop : ν A ≠ ∞) (t₀ q : ℝ) (hq : 0 < q) (lam : Measure (α × ℝ))
    (C : ℝ≥0∞) (hlam : lam ≤ C • ν.prod volume) (hsupp : ∀ᵐ p ∂lam, p.1 ∈ A) :
    (ENNReal.ofReal q * ν A)⁻¹ • lam.map (blockRescale t₀ q) ≤
      C • ((ν A)⁻¹ • ν.restrict A).prod volume := by
  have hq' : ENNReal.ofReal q ≠ 0 := by simpa using hq
  calc (ENNReal.ofReal q * ν A)⁻¹ • lam.map (blockRescale t₀ q)
      ≤ (ENNReal.ofReal q * ν A)⁻¹ • ((C * ENNReal.ofReal q) • (ν.restrict A).prod volume) :=
        smul_le_smul_left _ (map_blockRescale_le ν hA t₀ q hq lam C hlam hsupp)
    _ = C • ((ν A)⁻¹ • ν.restrict A).prod volume := by
        rw [Measure.prod_smul_left, smul_smul, smul_smul]
        congr 1
        rw [ENNReal.mul_inv (Or.inl hq') (Or.inl ENNReal.ofReal_ne_top)]
        calc (ENNReal.ofReal q)⁻¹ * (ν A)⁻¹ * (C * ENNReal.ofReal q)
            = C * ((ENNReal.ofReal q)⁻¹ * ENNReal.ofReal q) * (ν A)⁻¹ := by ring
          _ = C * (ν A)⁻¹ := by
            rw [ENNReal.inv_mul_cancel hq' ENNReal.ofReal_ne_top, mul_one]

/-- Masses of product events transport exactly: the rescaled law of `S × [0,1]` is the original
law of `S × [t₀, t₀ + q]`. -/
theorem map_blockRescale_prod_Icc (lam : Measure (α × ℝ)) {S : Set α} (hS : MeasurableSet S)
    (t₀ q : ℝ) (hq : 0 < q) :
    lam.map (blockRescale t₀ q) (S ×ˢ Icc 0 1) = lam (S ×ˢ Icc t₀ (t₀ + q)) := by
  rw [Measure.map_apply (measurable_blockRescale t₀ q) (hS.prod measurableSet_Icc)]
  congr 1
  ext ⟨l, t⟩
  simp only [blockRescale, mem_preimage, mem_prod, mem_Icc]
  constructor
  · rintro ⟨hl, h0, h1⟩
    refine ⟨hl, ?_, ?_⟩
    · have := (le_div_iff₀ hq).mp h0; linarith
    · have := (div_le_iff₀ hq).mp h1; linarith
  · rintro ⟨hl, h0, h1⟩
    refine ⟨hl, ?_, ?_⟩
    · exact div_nonneg (by linarith) hq.le
    · rw [div_le_iff₀ hq]; linarith

end Submission.Obl.k4_horizontal_wide_interval_return
