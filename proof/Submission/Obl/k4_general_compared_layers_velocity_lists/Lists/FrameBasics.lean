-- Copied for obligation o282 (k4_general_compared_layers_velocity_lists) from obligation o254
-- (k4_general_parent_wide_layer_candidates), branch x0900, module Submission.Obl.k4_general_parent_wide_layer_candidates.Lists.FrameBasics; only the module
-- and namespace prefix changed. Same LOT tree (o282 is a child of o254).
import Submission.Obl.k4_general_compared_layers_velocity_lists.Lists.Interface
import Submission.Obl.k4_wide_velocity_lists_scalar_preparation.Background
import Submission.Lib.K4ChartLifting.PolyAlgebra

/-!
# Basic facts about incoming list frames of a general parent

Adapted from accepted o248 (`k4_wide_velocity_lists_scalar_preparation`, files
`OriginalSupport.lean`, `FrameData.lean`, `FrameMeasure.lean` and the frame part of
`PoolBasics.lean`) to the general parent `Parent` and its native signal.
-/

namespace Submission.Obl.k4_general_compared_layers_velocity_lists

open MeasureTheory Set Filter
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] {p : Parent α}

/-- The original base coordinates are bounded on almost every original incidence,
from the trajectory prior bound and the unit-time support. -/
theorem Valid.base_bound_ae (h : p.Valid) (k : ℕ) :
    ∀ᵐ ω ∂p.μ k, ∀ e : Fin 3, |p.base k ω.1 ω.2 e| ≤ 2 * p.K k := by
  have : IsProbabilityMeasure (p.ν k) := (h.basic k).2.1
  have hmeas : MeasurableSet {ω : α × ℝ |
      |p.b k ω.1 0| + |p.b k ω.1 1| + |p.b k ω.1 3| + |p.b k ω.1 4| ≤ p.K k} := by
    apply measurableSet_le _ measurable_const
    have hb := (h.basic k).1
    fun_prop
  have hprod : ∀ᵐ ω ∂(p.ν k).prod (volume : Measure ℝ),
      |p.b k ω.1 0| + |p.b k ω.1 1| + |p.b k ω.1 3| + |p.b k ω.1 4| ≤ p.K k := by
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    filter_upwards [(h.basic k).2.2.2.2.2.2.2.2.1] with l hl
    exact Filter.Eventually.of_forall (fun _ => hl)
  have hb : ∀ᵐ ω ∂p.μ k,
      |p.b k ω.1 0| + |p.b k ω.1 1| + |p.b k ω.1 3| + |p.b k ω.1 4| ≤ p.K k :=
    ae_mono (h.basic k).2.2.2.1 (Measure.ae_smul_measure hprod _)
  have ht : ∀ᵐ ω ∂p.μ k, ω ∈ (univ : Set α) ×ˢ Icc (0 : ℝ) 1 := by
    apply ae_iff.mpr
    exact (h.basic k).2.2.2.2.2.1
  filter_upwards [hb, ht] with ω hb ht
  have hK : 1 ≤ p.K k := h.subpower.1 k
  have ht0 : 0 ≤ ω.2 := ht.2.1
  have ht1 : ω.2 ≤ 1 := ht.2.2
  have ht_abs : |ω.2| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have hcoord (a b : ℝ) : |a + ω.2 * b| ≤ |a| + |b| := by
    calc
      _ ≤ |a| + |ω.2 * b| := abs_add_le _ _
      _ = |a| + |ω.2| * |b| := by rw [abs_mul]
      _ ≤ |a| + 1 * |b| := add_le_add le_rfl
        (mul_le_mul_of_nonneg_right ht_abs (abs_nonneg _))
      _ = _ := by ring
  intro e
  fin_cases e
  · change |ω.2| ≤ _
    linarith
  · change |p.b k ω.1 0 + ω.2 * p.b k ω.1 3| ≤ _
    have hc := hcoord (p.b k ω.1 0) (p.b k ω.1 3)
    linarith [abs_nonneg (p.b k ω.1 1), abs_nonneg (p.b k ω.1 4)]
  · change |p.b k ω.1 1 + ω.2 * p.b k ω.1 4| ≤ _
    have hc := hcoord (p.b k ω.1 1) (p.b k ω.1 4)
    linarith [abs_nonneg (p.b k ω.1 0), abs_nonneg (p.b k ω.1 3)]

namespace ListFrame

variable {k : ℕ} {r v m ε : ℝ} (f : p.ListFrame k r v m ε)

/-- The normalized scalar velocity is the original horizontal velocity
translated by the fixed frame velocity. -/
theorem velocity_eq (l : α) (hl : l ∈ f.good) : f.coeff l 1 = p.b k l 3 - f.zv := by
  have h₀ := f.scalarY_eq l hl 0
  have h₁ := f.scalarY_eq l hl 1
  simp only [scalarY, Submission.Obl.k4_fixed_budget_quadratic_recovery.scalarY,
    Submission.Obl.k4_critical_intercept_concentration.Data.x,
    zero_mul, mul_zero, mul_one, one_mul, add_zero,
    Matrix.cons_val_one, Matrix.cons_val_zero] at h₀ h₁
  have h₀ := (eq_div_iff f.q_pos.ne').mp h₀
  have h₁ := (eq_div_iff f.q_pos.ne').mp h₁
  apply mul_right_cancel₀ f.q_pos.ne'
  calc
    f.coeff l 1 * f.q = (f.coeff l 0 + f.coeff l 1) * f.q - f.coeff l 0 * f.q := by ring
    _ = (p.b k l 3 - f.zv) * f.q := by rw [h₀, h₁]; ring

theorem q_le_one : f.q ≤ 1 := by
  rw [f.q_eq]
  exact inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))

theorem background_coeff_bound (e : Fin 3 →₀ ℕ) :
    |f.background.coeff e| ≤ p.N k ^ (m / 10) := by
  exact (Submission.Lib.K4ChartLifting.abs_coeff_le_coeffL1 f.background e).trans
    f.background_bound

theorem unit_time_mem (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 1) :
    f.t₀ + f.q * u ∈ block (p.T k r) (p.j k r f.parent) := by
  rw [f.time_eq]
  exact ⟨by linarith [mul_nonneg f.q_pos.le hu.1],
    by linarith [mul_le_mul_of_nonneg_left hu.2 f.q_pos.le]⟩

/-- Every component of the frame is controlled by its stated fixed budget. -/
theorem frame_component_bounds :
    f.q⁻¹ ≤ p.N k ^ (m / 10) ∧ |f.zv| ≤ p.N k ^ (m / 10) := by
  have hqi : 1 ≤ f.q⁻¹ := (one_le_inv₀ f.q_pos).mpr f.q_le_one
  have hqi0 : 0 ≤ f.q⁻¹ := inv_nonneg.mpr f.q_pos.le
  have hB := f.frame_bound
  rw [abs_of_pos (inv_pos.mpr f.q_pos)] at hB
  have hz : |f.zv| ≤ f.q⁻¹ * |f.zv| := le_mul_of_one_le_left (abs_nonneg _) hqi
  have hlarge : f.q⁻¹ * |f.zv| ≤
      f.q⁻¹ * (2 + |f.t₀| + |f.z₀| + |f.zv|) := by
    apply mul_le_mul_of_nonneg_left _ hqi0
    linarith [abs_nonneg f.t₀, abs_nonneg f.z₀]
  have hlarge' : 2 * f.q⁻¹ ≤
      f.q⁻¹ * (2 + |f.t₀| + |f.z₀| + |f.zv|) := by
    have hh : 2 ≤ 2 + |f.t₀| + |f.z₀| + |f.zv| := by
      linarith [abs_nonneg f.t₀, abs_nonneg f.z₀, abs_nonneg f.zv]
    nlinarith [mul_le_mul_of_nonneg_left hh hqi0]
  constructor <;> linarith

/-- Incoming normalized laws are finite. -/
theorem law_univ_le : f.law univ ≤ ENNReal.ofReal (p.N k ^ ε) := by
  calc f.law univ ≤ f.law ((univ : Set α) ×ˢ Icc (0 : ℝ) 1) +
        f.law ((univ : Set α) ×ˢ Icc (0 : ℝ) 1)ᶜ := measure_univ_le_add_compl _
    _ = f.law ((univ : Set α) ×ˢ Icc (0 : ℝ) 1) := by rw [f.time_support, add_zero]
    _ ≤ (ENNReal.ofReal (p.N k ^ ε) • (f.prior.prod volume))
          ((univ : Set α) ×ˢ Icc (0 : ℝ) 1) := f.law_domination _
    _ = ENNReal.ofReal (p.N k ^ ε) := by
        have := f.prior_probability
        rw [Measure.smul_apply, smul_eq_mul, Measure.prod_prod, measure_univ,
          Real.volume_Icc, sub_zero, ENNReal.ofReal_one, one_mul, mul_one]

theorem isFiniteMeasure_law : IsFiniteMeasure f.law :=
  ⟨lt_of_le_of_lt f.law_univ_le ENNReal.ofReal_lt_top⟩

/-- The time map from normalized block time to original time. -/
def timeMap : α × ℝ → α × ℝ := fun ω => (ω.1, f.t₀ + f.q * ω.2)

theorem measurable_timeMap : Measurable f.timeMap :=
  measurable_fst.prodMk (measurable_const.add (measurable_const.mul measurable_snd))

/-- The original reference factor of the frame. -/
def weight : ℝ≥0∞ := ENNReal.ofReal f.q * p.ν k (p.A k r f.parent)

theorem map_le (hρμ : p.ρ k ≤ p.μ k) (h0 : f.weight ≠ 0) (ht : f.weight ≠ ⊤) :
    f.law.map f.timeMap ≤ f.weight⁻¹ • p.μ k := by
  rw [Measure.le_iff']
  intro s
  have hd := Measure.le_iff'.mp (f.original_domination.trans hρμ) s
  rw [Measure.smul_apply, smul_eq_mul] at hd ⊢
  calc (f.law.map f.timeMap) s = f.weight⁻¹ * (f.weight * (f.law.map f.timeMap) s) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul]
    _ ≤ f.weight⁻¹ * p.μ k s := by
        gcongr
        exact hd

/-- Almost-sure facts about original incidences hold on the frame. -/
theorem ae_of_original (hρμ : p.ρ k ≤ p.μ k) (h0 : f.weight ≠ 0) (ht : f.weight ≠ ⊤)
    {P : α × ℝ → Prop} (hP : ∀ᵐ ω ∂p.μ k, P ω) :
    ∀ᵐ ω ∂f.law, P (ω.1, f.t₀ + f.q * ω.2) := by
  have hac : f.law.map f.timeMap ≪ p.μ k :=
    Measure.absolutelyContinuous_of_le_smul (f.map_le hρμ h0 ht)
  exact ae_of_ae_map f.measurable_timeMap.aemeasurable (hac.ae_le hP)

/-- Original measures of measurable events bound their frame pullbacks. -/
theorem law_preimage_le (hρμ : p.ρ k ≤ p.μ k) (h0 : f.weight ≠ 0) (ht : f.weight ≠ ⊤)
    {E : Set (α × ℝ)} (hE : MeasurableSet E) :
    f.law (f.timeMap ⁻¹' E) ≤ f.weight⁻¹ * p.μ k E := by
  rw [← Measure.map_apply f.measurable_timeMap hE]
  have h := Measure.le_iff'.mp (f.map_le hρμ h0 ht) E
  rwa [Measure.smul_apply, smul_eq_mul] at h

/-- Countably many normalized times carry no frame mass. -/
theorem law_time_countable_null {Z : Set ℝ} (hZ : Z.Countable) :
    f.law {ω | ω.2 ∈ Z} = 0 := by
  apply le_antisymm _ zero_le
  have hset : {ω : α × ℝ | ω.2 ∈ Z} = (univ : Set α) ×ˢ Z := by
    ext ω; simp
  calc f.law {ω | ω.2 ∈ Z} ≤ (ENNReal.ofReal (p.N k ^ ε) • (f.prior.prod volume))
        {ω | ω.2 ∈ Z} := f.law_domination _
    _ = 0 := by
        rw [hset, Measure.smul_apply, smul_eq_mul, Measure.prod_prod,
          hZ.measure_zero, mul_zero, mul_zero]

end ListFrame

end Parent

end

end Submission.Obl.k4_general_compared_layers_velocity_lists
