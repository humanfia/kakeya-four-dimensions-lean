/- Adapted from this LOT tree, obligation o211, session x0736,
   commit 83b764e828c02e4c2216b0015b1434127ef232e2, ContinuousNormalization.lean.
   Original source attributions below are retained. -/

import Submission.Lib.K4ChartLifting.Mass

/-! Adapted from our LOT tree o107, session x0353, ContinuousNormalization.lean
(commit 2d33b59a).

Normalize the original continuous incidence law in time and mass while
keeping the original trajectory prior, normalized only by its total mass. -/

namespace Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof

noncomputable section

open MeasureTheory Set
open scoped ENNReal

def unitTimeMap {α : Type*} (t₀ H : ℝ) (p : α × ℝ) : α × ℝ :=
  (p.1, (p.2 - t₀) / H)

theorem measurable_unitTimeMap {α : Type*} [MeasurableSpace α] (t₀ H : ℝ) :
    Measurable (unitTimeMap (α := α) t₀ H) :=
  measurable_fst.prodMk ((measurable_snd.sub_const t₀).div_const H)

theorem original_product_unit_time_map {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [SFinite ν] (t₀ H : ℝ) (hH : 0 < H) :
    (ν.prod volume).map (unitTimeMap t₀ H) = ENNReal.ofReal H • (ν.prod volume) := by
  change (ν.prod volume).map (Prod.map id (fun t : ℝ => (t - t₀) / H)) = _
  rw [← Measure.map_prod_map ν volume measurable_id
    (show Measurable (fun t : ℝ => (t - t₀) / H) from
      (measurable_id.sub_const t₀).div_const H), Measure.map_id,
    Submission.Lib.K4ChartLifting.map_volume_affine t₀ H hH, Measure.prod_smul_right]

theorem original_continuous_normalized_domination
    {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (μ : Measure (α × ℝ))
    (t₀ H K W : ℝ) (hH : 0 < H) (hK : 0 ≤ K) (hW : 0 < W)
    (hν : ν Set.univ ≠ 0) (hdom : μ ≤ ENNReal.ofReal K • (ν.prod volume)) :
    ENNReal.ofReal W⁻¹ • μ.map (unitTimeMap t₀ H) ≤
      ENNReal.ofReal (K * H * ν.real Set.univ / W) •
        (((ν Set.univ)⁻¹ • ν).prod volume) := by
  have hmap : μ.map (unitTimeMap t₀ H) ≤
      (ENNReal.ofReal K * ENNReal.ofReal H) • (ν.prod volume) := by
    have hh := Measure.map_mono hdom (measurable_unitTimeMap t₀ H)
    rwa [Measure.map_smul _ (measurable_unitTimeMap t₀ H).aemeasurable,
      original_product_unit_time_map ν t₀ H hH, smul_smul] at hh
  have hscalar :
      ENNReal.ofReal (K * H * ν.real Set.univ / W) * (ν Set.univ)⁻¹ =
        ENNReal.ofReal W⁻¹ * (ENNReal.ofReal K * ENNReal.ofReal H) := by
    rw [ENNReal.ofReal_div_of_pos hW,
      ENNReal.ofReal_mul (mul_nonneg hK hH.le), ENNReal.ofReal_mul hK,
      show ENNReal.ofReal (ν.real Set.univ) = ν Set.univ from
        ENNReal.ofReal_toReal (measure_ne_top ν _), ENNReal.ofReal_inv_of_pos hW]
    calc
      _ = (ENNReal.ofReal W)⁻¹ * (ENNReal.ofReal K * ENNReal.ofReal H) *
          (ν Set.univ * (ν Set.univ)⁻¹) := by simp only [div_eq_mul_inv]; ring
      _ = _ := by rw [ENNReal.mul_inv_cancel hν (measure_ne_top ν _), mul_one]
  rw [Measure.prod_smul_left, smul_smul, hscalar, ← smul_smul]
  exact smul_le_smul_left _ hmap

/-- A measurable normalized event has exactly its original-law preimage mass,
divided by the unchanged chosen reference mass W. -/
theorem original_continuous_normalized_apply
    {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ))
    (t₀ H W : ℝ) (A : Set (α × ℝ)) (hA : MeasurableSet A) :
    (ENNReal.ofReal W⁻¹ • μ.map (unitTimeMap t₀ H)) A =
      ENNReal.ofReal W⁻¹ * μ ((unitTimeMap t₀ H) ⁻¹' A) := by
  rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_unitTimeMap t₀ H) hA]

theorem original_continuous_normalized_mass_restore
    {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ))
    (t₀ H W θ : ℝ) (hW : 0 < W) (A : Set (α × ℝ)) (hA : MeasurableSet A)
    (hmass : ENNReal.ofReal θ ≤
      (ENNReal.ofReal W⁻¹ • μ.map (unitTimeMap t₀ H)) A) :
    ENNReal.ofReal (W * θ) ≤ μ ((unitTimeMap t₀ H) ⁻¹' A) := by
  rw [ENNReal.ofReal_mul hW.le]
  calc
    _ ≤ ENNReal.ofReal W *
        (ENNReal.ofReal W⁻¹ • μ.map (unitTimeMap t₀ H)) A :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by
      rw [original_continuous_normalized_apply μ t₀ H W A hA,
        ENNReal.ofReal_inv_of_pos hW, ← mul_assoc,
        ENNReal.mul_inv_cancel (by simpa using hW) ENNReal.ofReal_ne_top, one_mul]

theorem original_continuous_normalized_ae_restore
    {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ))
    (t₀ H W : ℝ) (hW : 0 < W) (P : α × ℝ → Prop)
    (hP : ∀ᵐ p ∂(ENNReal.ofReal W⁻¹ • μ.map (unitTimeMap t₀ H)), P p) :
    ∀ᵐ p ∂μ, P (unitTimeMap t₀ H p) := by
  apply ae_of_ae_map (measurable_unitTimeMap t₀ H).aemeasurable
  exact (Measure.ae_ennreal_smul_measure_iff (show ENNReal.ofReal W⁻¹ ≠ 0 by
    simp only [ne_eq, ENNReal.ofReal_eq_zero]; exact not_le.mpr (inv_pos.mpr hW))).mp hP

theorem original_continuous_normalized_support
    {α : Type*} [MeasurableSpace α] (μ : Measure (α × ℝ))
    (t₀ H W : ℝ) (hH : 0 < H)
    (hfull : μ (Set.univ ×ˢ Set.Icc t₀ (t₀ + H))ᶜ = 0) :
    (ENNReal.ofReal W⁻¹ • μ.map (unitTimeMap t₀ H))
      (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [original_continuous_normalized_apply μ t₀ H W _
    (MeasurableSet.univ.prod measurableSet_Icc).compl]
  have heq : (unitTimeMap (α := α) t₀ H) ⁻¹' (Set.univ ×ˢ Set.Icc (0 : ℝ) 1)ᶜ =
      (Set.univ ×ˢ Set.Icc t₀ (t₀ + H))ᶜ := by
    ext p
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_prod, Set.mem_univ,
      true_and, Set.mem_Icc, unitTimeMap]
    rw [le_div_iff₀ hH, div_le_iff₀ hH, zero_mul, one_mul]
    constructor <;> contrapose! <;> intro hp <;> constructor <;> linarith [hp.1, hp.2]
  rw [heq, hfull, mul_zero]

end

end Submission.Obl.k4_critical_derivative_evaluation_lists.ParentProof
