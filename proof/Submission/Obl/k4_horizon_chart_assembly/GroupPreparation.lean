import Submission.Obl.k4_horizon_chart_assembly.GroupGeometry
import Submission.Obl.k4_horizon_chart_assembly.TimeTransport

namespace Submission.Obl.k4_horizon_chart_assembly

open Set MeasureTheory
open scoped ENNReal

noncomputable section

theorem nativeGroup_measurable (P : MvPolynomial (Fin 4) ℝ) (hP : P.totalDegree ≤ 2)
    (B s : ℝ) {K H q a : ℝ} (hK : 0 ≤ K) (hH : 0 ≤ H)
    (hq : 0 < q) (ha : 0 < a) (Γ : (Fin 2 → ℤ) × ℤ) :
    MeasurableSet (nativeGroup P B K H s q a Γ) := by
  apply measurableSet_indexed_polynomialFormat (N := 110) (M := 1) (D := 4)
  intro i
  exact nativeGroup_format P hP B s hK hH hq ha Γ (by norm_num) i

theorem groupIntercept_measurable (q a s r : ℝ) (Γ : (Fin 2 → ℤ) × ℤ) :
    Measurable (groupIntercept q a s r Γ) := by
  fun_prop [groupIntercept, normalizedBlockIntercept, planarPoint, planarVelocity]

theorem groupVelocity_measurable (q r : ℝ) : Measurable (groupVelocity q r) := by
  fun_prop [groupVelocity, normalizedBlockVelocity, planarVelocity]

theorem normalizedEvent_unit_time {α : Type*} (E : Set (α × ℝ)) (s q : ℝ) :
    normalizedEvent E s q ⊆ univ ×ˢ Icc (0 : ℝ) 1 := by
  intro p hp
  exact ⟨mem_univ _, hp.1.2.1, hp.1.2.2.le⟩

/-- The original a.e. bounds give pointwise formatted eligibility at almost every
original incidence. No new conditioning of the prior is introduced. -/
theorem nativeEligible_ae (ν : Measure Trajectory) [SFinite ν]
    (E : Set Incidence) (hE : MeasurableSet E)
    (P : MvPolynomial (Fin 4) ℝ) (B K H : ℝ)
    (hbox : ∀ p ∈ E, (p.1.1 : ℝ) ≤ H ∧ ∀ e, |p.1.2 e| ≤ H)
    (hupper : ∀ᵐ l ∂ν, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖yl l t‖ + ‖vl l‖ ≤ K ∧ |MvPolynomial.eval (xl l t) P| ≤ K ∧
      |MvPolynomial.eval (xl l t) (MvPolynomial.pderiv (3 : Fin 4) P)| ≤ K * B ∧
      |MvPolynomial.eval (xl l t) (MvPolynomial.pderiv (3 : Fin 4)
        (MvPolynomial.pderiv (3 : Fin 4) P))| ≤ K * B ^ 2) :
    ∀ᵐ p ∂(ν.prod volume).restrict E, nativeEligible P B K H p.1 := by
  have hlift := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := (volume : Measure ℝ))).tendsto_ae hupper
  filter_upwards [ae_restrict_of_ae hlift, ae_restrict_mem hE] with p hp hpE
  exact nativeEligible_of_native_bounds P B K H p.1 (hbox p hpE).1 (hbox p hpE).2 hp

end
end Submission.Obl.k4_horizon_chart_assembly
