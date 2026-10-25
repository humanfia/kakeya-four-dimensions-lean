import Submission.Obl.k4_scalar_pure_multiworld_homogenization.SelectionInterface
import Submission.Obl.k4_scalar_pure_multiworld_homogenization.Shear
import Submission.Obl.k4_dyadic_crop_affine_laws.Framework.CountedDensity

/-!
# Observation densities of arbitrary sub-events

For a prior which is a finite mixture of Lebesgue pieces, the continuous base
`(t, y)` of the product law has an absolutely continuous law: at fixed time,
replacing `a₀` by `y = a₀ + t a₁` has Jacobian one (the measure-preserving chart
`chartEquiv`). Hence every restriction of the incidence law to a measurable event
has a density at every depth, namely its Radon-Nikodym derivative.
-/

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set Filter
open scoped ENNReal

/-- The continuous base of an incidence. -/
def baseOf (z : Incidence) : Fin 2 → ℝ := ![z.2, y z.1 z.2]

theorem measurable_baseOf : Measurable baseOf := by
  unfold baseOf
  apply Measurable.of_eval
  intro i
  fin_cases i
  · exact measurable_snd
  · exact measurable_y

theorem observe_fst (n r : ℝ) (z : Incidence) : (observe n r z).1 = baseOf z := rfl

/-- The base map is null-preserving on coefficient-time space. -/
theorem volume_base_preimage_null {Z : Set (Fin 2 → ℝ)} (hZ : MeasurableSet Z)
    (h0 : volume Z = 0) :
    (volume : Measure ((Fin 5 → ℝ) × ℝ))
      {q | (![q.2, q.1 0 + q.2 * q.1 1] : Fin 2 → ℝ) ∈ Z} = 0 := by
  let S : Set (Fin 6 → ℝ) := {w | (![w 0, w 1] : Fin 2 → ℝ) ∈ Z}
  have hSm : MeasurableSet S := by
    apply hZ.preimage
    apply Measurable.of_eval
    intro i
    fin_cases i
    · exact measurable_pi_apply 0
    · exact measurable_pi_apply 1
  have hpre : {q : (Fin 5 → ℝ) × ℝ | (![q.2, q.1 0 + q.2 * q.1 1] : Fin 2 → ℝ) ∈ Z} =
      chartEquiv ⁻¹' S := by
    ext q
    simp only [S, mem_ofPred_eq, mem_preimage]
    rfl
  have hjoin : join ⁻¹' S = Z ×ˢ (univ : Set (Fin 4 → ℝ)) := by
    ext q
    simp only [S, join, mem_preimage, mem_ofPred_eq, mem_prod, mem_univ, and_true]
    have : (![q.1 0, q.1 1] : Fin 2 → ℝ) = q.1 := by
      funext i
      fin_cases i <;> rfl
    simp [this]
  rw [hpre, Measure.volume_eq_prod,
    measurePreserving_chartEquiv.measure_preimage hSm.nullMeasurableSet,
    ← measurePreserving_join.measure_preimage hSm.nullMeasurableSet, hjoin,
    Measure.prod_prod, h0, zero_mul]

/-- A Lebesgue mixture prior gives null product mass to the preimage of a base null set. -/
theorem mixture_prod_base_null {n : ℕ} (h : Fin n → ℝ) (i : Fin n → ℕ)
    (B : Fin n → Set (Fin 5 → ℝ))
    {Z : Set (Fin 2 → ℝ)} (hZ : MeasurableSet Z) (h0 : volume Z = 0) :
    ((∑ j, ENNReal.ofReal (h j) • Measure.map (fun b => (i j, b))
        ((volume : Measure (Fin 5 → ℝ)).restrict (B j))).prod (volume : Measure ℝ))
      (baseOf ⁻¹' Z) = 0 := by
  have hm : MeasurableSet (baseOf ⁻¹' Z) := hZ.preimage measurable_baseOf
  rw [Measure.prod_apply hm]
  rw [lintegral_finsetSum_measure]
  apply Finset.sum_eq_zero
  intro j _
  rw [lintegral_smul_measure]
  have hfm : Measurable (fun l : Trajectory => (volume : Measure ℝ) (Prod.mk l ⁻¹' (baseOf ⁻¹' Z))) :=
    measurable_measure_prodMk_left hm
  rw [lintegral_map hfm (by fun_prop)]
  have hle : ∫⁻ b, (volume : Measure ℝ) (Prod.mk (i j, b) ⁻¹' (baseOf ⁻¹' Z))
        ∂((volume : Measure (Fin 5 → ℝ)).restrict (B j)) ≤
      ∫⁻ b, (volume : Measure ℝ) (Prod.mk (i j, b) ⁻¹' (baseOf ⁻¹' Z)) := by
    exact lintegral_mono' Measure.restrict_le_self le_rfl
  have hzero : ∫⁻ b, (volume : Measure ℝ) (Prod.mk (i j, b) ⁻¹' (baseOf ⁻¹' Z)) = 0 := by
    have hset : MeasurableSet {q : (Fin 5 → ℝ) × ℝ |
        (![q.2, q.1 0 + q.2 * q.1 1] : Fin 2 → ℝ) ∈ Z} := by
      apply hZ.preimage
      apply Measurable.of_eval
      intro k
      fin_cases k
      · exact measurable_snd
      · dsimp
        fun_prop
    calc ∫⁻ b, (volume : Measure ℝ) (Prod.mk (i j, b) ⁻¹' (baseOf ⁻¹' Z))
        = ∫⁻ b, (volume : Measure ℝ) (Prod.mk b ⁻¹' {q : (Fin 5 → ℝ) × ℝ |
            (![q.2, q.1 0 + q.2 * q.1 1] : Fin 2 → ℝ) ∈ Z}) := rfl
      _ = ((volume : Measure (Fin 5 → ℝ)).prod (volume : Measure ℝ)) {q : (Fin 5 → ℝ) × ℝ |
            (![q.2, q.1 0 + q.2 * q.1 1] : Fin 2 → ℝ) ∈ Z} := (Measure.prod_apply hset).symm
      _ = 0 := by
        rw [← Measure.volume_eq_prod]
        exact volume_base_preimage_null hZ h0
  rw [le_antisymm (hle.trans hzero.le) bot_le, smul_zero]

/-- The base law of any restriction of a Lebesgue mixture product law is absolutely
continuous. -/
theorem mixture_base_ac {n : ℕ} (h : Fin n → ℝ) (i : Fin n → ℕ)
    (B : Fin n → Set (Fin 5 → ℝ)) (S : Set Incidence) :
    (((∑ j, ENNReal.ofReal (h j) • Measure.map (fun b => (i j, b))
        ((volume : Measure (Fin 5 → ℝ)).restrict (B j))).prod (volume : Measure ℝ)).restrict S).map
      baseOf ≪ (volume : Measure (Fin 2 → ℝ)) := by
  apply Measure.AbsolutelyContinuous.mk
  intro Z hZ h0
  rw [Measure.map_apply measurable_baseOf hZ]
  apply le_antisymm _ bot_le
  calc _ ≤ ((∑ j, ENNReal.ofReal (h j) • Measure.map (fun b => (i j, b))
        ((volume : Measure (Fin 5 → ℝ)).restrict (B j))).prod (volume : Measure ℝ))
          (baseOf ⁻¹' Z) := (Measure.restrict_le_self (s := S)) _
    _ = 0 := mixture_prod_base_null h i B hZ h0

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
