-- Adapted from: here:o202 (session x0952), Regularization/CoefficientCover.lean.
import Submission.Lib.K4CoefficientBinRegularization.BinCount

namespace Submission.Lib.K4CoefficientBinRegularization.Reg

open MeasureTheory Set FirstJet
open scoped ENNReal Classical

noncomputable section

/-- Original trajectories whose original labeled time set has length at least `δ`. -/
def longLabels {Ω : Type*} (E : Set (Ω × ℝ)) (δ : ℝ) : Set Ω :=
  {l | ENNReal.ofReal δ ≤ volume (Prod.mk l ⁻¹' E)}

theorem measurableSet_longLabels {Ω : Type*} [MeasurableSpace Ω]
    {E : Set (Ω × ℝ)} (hE : MeasurableSet E) (δ : ℝ) : MeasurableSet (longLabels E δ) :=
  measurableSet_le measurable_const (measurable_measure_prodMk_left hE)

theorem measurable_coefficientCode {Ω : Type*} [MeasurableSpace Ω]
    {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} (hy : Measurable y)
    (hβ : Measurable β) (hγ : Measurable γ) (r : ℝ) :
    Measurable (coefficientCode y β γ r) := by
  apply measurable_pi_lambda
  intro i
  fin_cases i
  · exact Int.measurable_floor.comp ((measurable_pi_apply 0 |>.comp hy).div_const r)
  · exact Int.measurable_floor.comp ((measurable_pi_apply 1 |>.comp hy).div_const r)
  · exact Int.measurable_floor.comp (hβ.div_const r)
  · exact Int.measurable_floor.comp (hγ.div_const r)

/-- A finite cover of the long trajectories at one coefficient width. -/
theorem exists_coefficient_cover {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} {y : Ω → Fin 2 → ℝ} {β γ : Ω → ℝ} {E : Set (Ω × ℝ)}
    {F : ℝ → Fin 2 → ℝ} {d K ζ r δ : ℝ}
    (hU : UnregularizedChart ν y β γ E F d K ζ)
    (hSlope : SlopeComparison y β γ E K ζ) (hK : 1 ≤ K)
    (hζ : 0 < ζ) (hr : ζ ≤ r) (hr1 : r ≤ 1) (hδ : 0 < δ) :
    ∃ C : Finset (Fin 4 → ℤ),
      (C.card : ℝ) ≤ (packingBound K / δ) * r ^ (-2 - d) ∧
      ∀ l ∈ longLabels E δ, coefficientCode y β γ r l ∈ C := by
  classical
  have hr0 : 0 < r := hζ.trans_le hr
  let R : ℤ := ⌈K / r + 1⌉
  let allCodes : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (-R) R
  have hmem (l : Ω) : coefficientCode y β γ r l ∈ allCodes := by
    apply Fintype.mem_piFinset.mpr
    intro i
    have hb {v : ℝ} (hv : |v| ≤ K) : ⌊v / r⌋ ∈ Finset.Icc (-R) R := by
      have h := Submission.Lib.K4ProjectedGroups.abs_code_sub_le (x := v) (y := 0) hr0
        (by simpa only [sub_zero] using hv)
      simp only [zero_div, Int.floor_zero, Int.cast_zero, sub_zero] at h
      have hceil : K / r + 1 ≤ (R : ℝ) := Int.le_ceil _
      have h' : |⌊v / r⌋| ≤ R := by exact_mod_cast h.trans hceil
      exact Finset.mem_Icc.mpr (abs_le.mp h')
    fin_cases i
    · exact hb (hU.bound_y l 0)
    · exact hb (hU.bound_y l 1)
    · exact hb (hU.bound_β l)
    · exact hb (hU.bound_γ l)
  let C := allCodes.filter fun b => ∃ l ∈ longLabels E δ, coefficientCode y β γ r l = b
  have hw : ∀ b ∈ C, ∃ l : Ω, ENNReal.ofReal δ ≤ volume (Prod.mk l ⁻¹' E) ∧
      coefficientCode y β γ r l = b := by
    intro b hb
    exact (Finset.mem_filter.mp hb).2
  refine ⟨C, ?_, fun l hl => Finset.mem_filter.mpr ⟨hmem l, l, hl, rfl⟩⟩
  have hcount := coefficient_count_of_long_witnesses hU hSlope hK hζ hr hr1 hδ C hw
  have h := (le_div_iff₀ hδ).mpr hcount
  convert h using 1 <;> ring

end
end Submission.Lib.K4CoefficientBinRegularization.Reg
