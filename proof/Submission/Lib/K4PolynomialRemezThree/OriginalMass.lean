import Mathlib
import Submission.Lib.K4PolynomialRemezThree.Comparison

/-!
Adapted from: here:o114 (session x0383).

The polynomial coefficient bound can be applied directly to an unnormalized
original law whose base marginal has a density ceiling. No image of a source
set needs to be declared measurable.
-/

namespace Submission.Lib.K4PolynomialRemezThree

open Set MeasureTheory MvPolynomial

/-- A heavy original-law entry with base density at most beta supplies the
positive real base volume needed by the coefficient comparison. -/
theorem exists_coefficient_bound_from_dominated_mass (D : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type*) [MeasurableSpace Ω]
      (μ : Measure Ω) (Z : Ω → Fin 3 → ℝ) (P : MvPolynomial (Fin 3) ℝ),
      P.totalDegree ≤ D → ∀ m β E : ℝ, 0 < m → 0 < β → m ≤ β → 0 ≤ E →
      ENNReal.ofReal m ≤ μ univ →
      (∀ U : Set (Fin 3 → ℝ), MeasurableSet U →
        μ (Z ⁻¹' U) ≤ ENNReal.ofReal β * volume U) →
      (∀ᵐ ω ∂μ, Z ω ∈ Icc (0 : Fin 3 → ℝ) 1 ∧ |eval (Z ω) P| ≤ E) →
      ∀ d, |P.coeff d| ≤ C * (32*((D:ℝ)+1)/(m/β))^(3*D) * E := by
  obtain ⟨C, hC, hbound⟩ := exists_coefficient_bound_from_base_mass D
  refine ⟨C, hC, ?_⟩
  intro Ω _ μ Z P hP m β E hm hβ hmβ hE hmass hdom htrace
  let U : Set (Fin 3 → ℝ) := Icc (0 : Fin 3 → ℝ) 1 ∩ {z | |eval z P| ≤ E}
  have hU : MeasurableSet U := measurableSet_Icc.inter
    (measurableSet_le P.continuous_eval.abs.measurable measurable_const)
  have hcover : μ univ ≤ μ (Z ⁻¹' U) := by
    apply measure_mono_ae
    filter_upwards [htrace] with ω hω
    exact fun _ => hω
  have hmU : ENNReal.ofReal m ≤ ENNReal.ofReal β * volume U :=
    hmass.trans (hcover.trans (hdom U hU))
  have hvol : ENNReal.ofReal (m/β) ≤ volume U := by
    rw [ENNReal.ofReal_div_of_pos hβ,
      ENNReal.div_le_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hβ)) ENNReal.ofReal_ne_top]
    simpa only [mul_comm] using hmU
  exact hbound P hP U (m/β) E (div_pos hm hβ) ((div_le_one hβ).mpr hmβ) hE
    inter_subset_left hvol (fun _ hz => hz.2)

end Submission.Lib.K4PolynomialRemezThree
