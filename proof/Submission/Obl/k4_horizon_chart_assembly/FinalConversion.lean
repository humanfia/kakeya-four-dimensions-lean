import Submission.Obl.k4_horizon_chart_assembly.SplitInterfaces
import Submission.Obl.k4_horizon_chart_assembly.ChartCore
import Submission.Obl.k4_horizon_chart_assembly.MassNumerics

namespace Submission.Obl.k4_horizon_chart_assembly

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- The finite atlas chart becomes exactly the frozen chart after the uniform
complexity budget is enlarged to a power of the original sample scale. -/
theorem budgetChart_as_chart {H N κ j L B : ℝ} {M D T : ℕ}
    {E : Set Incidence} {c u : Plane} {Q : Matrix (Fin 2) (Fin 2) ℝ}
    {R : MvPolynomial (Fin 4) ℝ} {A : Set Trajectory} {F : Set Incidence}
    {ex ex' : Prop} (hH : H ≤ N ^ M)
    (h : BudgetChart H D κ T j (dl N L) B E c u Q R A F ex)
    (hEx : ex → ex') : Chart N M D κ T j L B E c u Q R A F ex' :=
  rawChart_as_chart (rawChart_mono hH le_rfl h hEx)

/-- Every original event supported in unit time has finite mass under each
original probability prior. The world weights need no positive lower bound. -/
theorem original_weighted_mass_ne_top {W : ℕ} (ω : Fin W → ℝ)
    (ν : Fin W → Measure Trajectory) (E : Fin W → Set Incidence)
    (hν : ∀ γ, IsProbabilityMeasure (ν γ))
    (hunit : ∀ γ, E γ ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    (∑ γ, ENNReal.ofReal (ω γ) * ((ν γ).prod volume) (E γ)) ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro γ hγ
  haveI := hν γ
  have hmass : ((ν γ).prod volume) (E γ) ≤ 1 := by
    simpa using incidence_group_le_prior (ν γ) (hunit γ) univ
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ne_top_of_le_ne_top (by simp) hmass)

/-- The final mass floor also covers the case of an infinite selected sum. -/
theorem retained_weighted_mass {K κ : ℝ} {M S b s α : ENNReal}
    (hK : 0 < K) (hκ : 2 * K ≤ κ) (hMfin : M ≠ ⊤)
    (hM : ENNReal.ofReal K⁻¹ ≤ M)
    (hbound : M ≤ S + b + s + α * M)
    (hb : b ≤ ENNReal.ofReal (K⁻¹ / 8))
    (hs : s ≤ ENNReal.ofReal (K⁻¹ / 8)) (hα : α ≤ ENNReal.ofReal (1 / 4)) :
    ENNReal.ofReal κ⁻¹ ≤ S := by
  by_cases hS : S = ⊤
  · simp [hS]
  · exact ennreal_retained_mass_ge_inverse hK hκ hMfin hS hM hbound hb hs hα

/-- The finite density floor is identical to the physical determinant floor. -/
theorem physical_floor_eq {N κ f : ℝ} (T : ℕ) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    N ^ (-f) * ((2 : ℝ) ^ T)⁻¹ * |Q.det| / κ =
      N ^ (-f) * |Q.det| / ((2 : ℝ) ^ T * κ) := by ring

end Submission.Obl.k4_horizon_chart_assembly
