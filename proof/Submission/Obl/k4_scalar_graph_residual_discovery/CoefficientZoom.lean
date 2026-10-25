/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file CoefficientZoom.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.Model
import Submission.Lib.K4CommonLocalChoice

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open Submission.Lib.K4CommonLocalChoice

namespace Zoom

noncomputable section

def center (ρ : ℝ) (q : Fin 5 → ℤ) : ScalarLine :=
  (0, fun j => (q j : ℝ) * ρ)

def order : Fin 5 → Fin 5 := ![2, 3, 4, 0, 1]

/-- The higher-jet coordinates list the three quadratic coefficients first,
then the two affine coefficients. The original trajectory tag is retained. -/
def coeff (ρ : ℝ) (q : Fin 5 → ℤ) (l : ScalarLine) (e : Fin 5) : ℝ :=
  (l.2 (order e) - (q (order e) : ℝ) * ρ) / ρ

def x (ρ : ℝ) (q : Fin 5 → ℤ) (l : ScalarLine) (t : ℝ) : ℝ :=
  coeff ρ q l 0 + t * coeff ρ q l 1 + t ^ 2 * coeff ρ q l 2

def y (ρ : ℝ) (q : Fin 5 → ℤ) (l : ScalarLine) (t : ℝ) : ℝ :=
  coeff ρ q l 3 + t * coeff ρ q l 4

theorem x_eq (ρ : ℝ) (q : Fin 5 → ℤ) (l : ScalarLine) (t : ℝ) :
    x ρ q l t = (scalarX l t - scalarX (center ρ q) t) / ρ := by
  dsimp [x, coeff, order, center, scalarX]
  ring

theorem y_eq (ρ : ℝ) (q : Fin 5 → ℤ) (l : ScalarLine) (t : ℝ) :
    y ρ q l t = (scalarY l t - scalarY (center ρ q) t) / ρ := by
  dsimp [y, coeff, order, center, scalarY]
  ring

theorem measurable_coeff (ρ : ℝ) (q : Fin 5 → ℤ) : Measurable (coeff ρ q) := by
  apply Measurable.of_eval
  intro j
  dsimp only [coeff]
  fun_prop

theorem coeff_mem_unit {ρ : ℝ} (hρ : 0 < ρ) {q : Fin 5 → ℤ} {l : ScalarLine}
    (hl : cell ρ l.2 = q) (e : Fin 5) : coeff ρ q l e ∈ Ico (0 : ℝ) 1 := by
  have he := congr_fun hl (order e)
  change ⌊l.2 (order e) / ρ⌋ = q (order e) at he
  have hlo := Int.floor_le (l.2 (order e) / ρ)
  have hhi := Int.lt_floor_add_one (l.2 (order e) / ρ)
  rw [he] at hlo hhi
  dsimp only [coeff]
  rw [sub_div, mul_div_cancel_right₀ _ hρ.ne']
  constructor <;> linarith

theorem coeff_abs_le_one {ρ : ℝ} (hρ : 0 < ρ) {q : Fin 5 → ℤ} {l : ScalarLine}
    (hl : cell ρ l.2 = q) (e : Fin 5) : |coeff ρ q l e| ≤ 1 := by
  have h := coeff_mem_unit hρ hl e
  rw [abs_of_nonneg h.1]
  exact h.2.le

/-- A finer original coefficient box gives the exact diameter requirement
for the coefficient-piece partition in the higher-jet input. -/
theorem coeff_piece_diameter {ρ β r : ℝ} (hρ : 0 < ρ) (hβ : 0 < β)
    (hscale : β ≤ ρ * r) (q : Fin 5 → ℤ) {l l' : ScalarLine}
    (hbin : cell β l.2 = cell β l'.2) (e : Fin 5) :
    |coeff ρ q l e - coeff ρ q l' e| ≤ r := by
  have hd := norm_sub_lt_of_cell_eq hβ hbin
  have he := norm_le_pi_norm (l.2 - l'.2) (order e)
  have hid : coeff ρ q l e - coeff ρ q l' e =
      (l.2 (order e) - l'.2 (order e)) / ρ := by dsimp only [coeff]; ring
  rw [hid, abs_div, abs_of_pos hρ]
  apply (div_le_iff₀ hρ).2
  have hraw : |l.2 (order e) - l'.2 (order e)| ≤ β := he.trans hd.le
  nlinarith only [hraw, hscale]

def prior (θ : Measure ScalarLine) (ρ : ℝ) (q : Fin 5 → ℤ) : Measure ScalarLine :=
  (θ {l | cell ρ l.2 = q})⁻¹ • θ.restrict {l | cell ρ l.2 = q}

theorem measurableSet_block (ρ : ℝ) (q : Fin 5 → ℤ) :
    MeasurableSet {l : ScalarLine | cell ρ l.2 = q} :=
  (measurable_cell ρ measurable_snd) (measurableSet_singleton q)

theorem prior_probability (θ : Measure ScalarLine) [IsFiniteMeasure θ]
    (ρ : ℝ) (q : Fin 5 → ℤ) (hpos : θ {l | cell ρ l.2 = q} ≠ 0) :
    IsProbabilityMeasure (prior θ ρ q) := by
  constructor
  simp only [prior, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
  exact ENNReal.inv_mul_cancel hpos (measure_ne_top θ _)

/-- The fixed full-block prior is kept throughout all later restrictions of
the incidence labels. -/
theorem prior_cap_of_original_cap (θ : Measure ScalarLine) (ρ : ℝ) (q : Fin 5 → ℤ)
    (A : Set ScalarLine) (C : ENNReal)
    (hcap : θ (A ∩ {l | cell ρ l.2 = q}) ≤ C * θ {l | cell ρ l.2 = q}) :
    prior θ ρ q A ≤ C := by
  by_cases hpos : θ {l | cell ρ l.2 = q} = 0
  · have hnum : θ (A ∩ {l | cell ρ l.2 = q}) = 0 :=
      measure_mono_null inter_subset_right hpos
    simp only [prior, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply' (measurableSet_block ρ q), hnum, mul_zero, zero_le]
  by_cases htop : θ {l | cell ρ l.2 = q} = ⊤
  · simp [prior, htop]
  simp only [prior, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (measurableSet_block ρ q)]
  calc
    _ ≤ (θ {l | cell ρ l.2 = q})⁻¹ * (C * θ {l | cell ρ l.2 = q}) :=
      mul_le_mul_right hcap _
    _ = C := by rw [mul_left_comm, ENNReal.inv_mul_cancel hpos htop, mul_one]

/-- Cancellation against a fixed reference palette uses a prior floor, not
an incidence floor manufactured after a restriction. -/
theorem cap_of_palette_floor {m b π C a : ENNReal}
    (ha0 : a ≠ 0) (hatop : a ≠ ⊤) (hcap : m ≤ C * π) (hfloor : a * π ≤ b) :
    m ≤ (C / a) * b := by
  calc
    m ≤ C * π := hcap
    _ = (C / a) * (a * π) := by rw [← mul_assoc, ENNReal.div_mul_cancel ha0 hatop]
    _ ≤ (C / a) * b := mul_le_mul_right hfloor _

end

end Zoom

end Submission.Obl.k4_scalar_graph_residual_discovery
