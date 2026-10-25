/- Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
   session x0797, commit 21d8c848, file StripBudget.lean.
   The helper namespace and imports are renamed for obligation o278. -/
import Submission.Obl.k4_scalar_graph_residual_discovery.StripDuration

set_option autoImplicit false

namespace Submission.Obl.k4_scalar_graph_residual_discovery

open Set MeasureTheory
open scoped ENNReal
open Submission.Lib.K4CommonLocalChoice
open Submission.Obl.k4_initial_horizon_bound

noncomputable section

/-- Small normal variation makes the duration-cut budget independent of
the very small coarse physical width. -/
theorem strip_duration_count_cost {η H ρ p V : ℝ}
    (hη : 0 ≤ η) (hH : 1 ≤ H) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hp : 0 < p) (hV : 0 ≤ V) (hVp : V ≤ p) :
    (η * ρ) * (343 * (3 * H / ρ + 2) * (2 * V / p + 2)) ≤ 6860 * H * η := by
  have hfirst : ρ * (3 * H / ρ + 2) ≤ 5 * H := by
    have heq : ρ * (3 * H / ρ + 2) = 3 * H + 2 * ρ := by field_simp
    rw [heq]
    linarith
  have hsecond : 2 * V / p + 2 ≤ 4 := by
    have hh := (div_le_iff₀ hp).mpr (mul_le_mul_of_nonneg_left hVp (by norm_num : (0 : ℝ) ≤ 2))
    linarith only [hh]
  calc
    _ = (343 * η) * (ρ * (3 * H / ρ + 2)) * (2 * V / p + 2) := by ring
    _ ≤ (343 * η) * (5 * H) * 4 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hfirst (by positivity)) hsecond
        (by positivity) (by positivity)
    _ = _ := by ring

/-- Delete short original strip entries for a fixed-power small cost.
The original prior is unchanged and no number of coefficient worlds
appears. The geometric variation premise is paid by choosing rho small. -/
theorem short_strip_entry_mass_le_simple
    (ν : Measure ScalarLine) [SFinite ν] (μ : Measure ScalarIncidence)
    {c : ℝ≥0∞} (hdom : μ ≤ c • ν.prod volume)
    {E : Set ScalarIncidence} (hE : MeasurableSet E)
    (row : (Fin 3 → ℤ) → Fin 2 → ℝ) {η H b ρ p A D : ℝ}
    (hη : 0 ≤ η) (hH : 1 ≤ H) (hb : 0 < b) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hbρ : b ≤ ρ) (hp : 0 < p)
    (hcoeff : ∀ z ∈ E, ∀ e, |z.1.2 e| ≤ H)
    (htime : ∀ z ∈ E, z.2 ∈ Icc (0 : ℝ) 1)
    (hA : ∀ q, 1 + |row q 0| + |row q 1| ≤ A) (hD : 0 ≤ D)
    (hderiv : ∀ z ∈ E,
      |(normalPolynomial
        (row (cell ρ (leftCorner b (cell b (scalarPosition z))))) z.1).derivative.eval z.2| ≤ D)
    (hvariation : D * (ρ + 2 * b) + 2 * A * b ≤ p) :
    μ {z | z ∈ E ∧
      incidenceDuration (E ∩ stripRecord b ρ p row ⁻¹' {stripRecord b ρ p row z}) z.1 <
        ENNReal.ofReal (η * ρ)} ≤
      c * ENNReal.ofReal (6860 * H * η) * ν univ := by
  have hA₀ : 0 ≤ A := (by positivity : 0 ≤ 1 + |row 0 0| + |row 0 1|).trans (hA 0)
  have hraw := short_strip_entry_mass_le ν μ hdom hE row hH hb hρ hbρ hp
    hcoeff htime hA hD hderiv (ENNReal.ofReal (η * ρ))
  have hnum := ENNReal.ofReal_le_ofReal
    (strip_duration_count_cost hη hH hρ hρ₁ hp (by positivity) hvariation)
  rw [ENNReal.ofReal_mul (mul_nonneg hη hρ.le)] at hnum
  exact hraw.trans ((mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hnum zero_le) zero_le).trans_eq (by ring))

end

end Submission.Obl.k4_scalar_graph_residual_discovery
