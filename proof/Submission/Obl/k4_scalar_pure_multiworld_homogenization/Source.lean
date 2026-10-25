import Submission.Obl.k4_scalar_pure_multiworld_homogenization.PolynomialAveraging

noncomputable section

namespace Submission.Obl.k4_scalar_pure_multiworld_homogenization

open MeasureTheory Set
open scoped ENNReal

def chartPoint (z : Incidence) : Fin 6 → ℝ := chartEquiv (z.1.2, z.2)

def stateAt (i : ℕ) (z : Fin 6 → ℝ) : Incidence :=
  ((i, chartCoefficients z), z 0)

theorem measurable_chartPoint : Measurable chartPoint :=
  chartEquiv.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)

theorem measurable_stateAt (i : ℕ) : Measurable (stateAt i) :=
  (measurable_const.prodMk measurable_chartCoefficients).prodMk (measurable_pi_apply 0)

theorem chartPoint_stateAt (i : ℕ) (z : Fin 6 → ℝ) : chartPoint (stateAt i z) = z :=
  chartEquiv.apply_symm_apply z

def componentRegion (i : ℕ) (A : Set (Fin 5 → ℝ)) (E : Set Incidence) : Set (Fin 6 → ℝ) :=
  {z | chartCoefficients z ∈ A ∧ stateAt i z ∈ E}

theorem measurable_componentRegion (i : ℕ) {A : Set (Fin 5 → ℝ)}
    (hA : MeasurableSet A) {E : Set Incidence} (hE : MeasurableSet E) :
    MeasurableSet (componentRegion i A E) :=
  (hA.preimage measurable_chartCoefficients).inter (hE.preimage (measurable_stateAt i))

def sourceDensity {m : ℕ} (c : Fin m → ℝ) (i : Fin m → ℕ)
    (A : Fin m → Set (Fin 5 → ℝ)) (E : Set Incidence) (z : Fin 6 → ℝ) : ENNReal :=
  ∑ j, ENNReal.ofReal (c j) * (componentRegion (i j) (A j) E).indicator 1 z

theorem measurable_sourceDensity {m : ℕ} (c : Fin m → ℝ) (i : Fin m → ℕ)
    {A : Fin m → Set (Fin 5 → ℝ)} (hA : ∀ j, MeasurableSet (A j))
    {E : Set Incidence} (hE : MeasurableSet E) : Measurable (sourceDensity c i A E) := by
  unfold sourceDensity
  exact Finset.measurable_sum _ fun j _ => measurable_const.mul
    (measurable_one.indicator (measurable_componentRegion (i j) (hA j) hE))

/-- The scalar incidence law has its finite-mixture density in chart coordinates. -/
theorem map_chart_restrict {m : ℕ} (c : Fin m → ℝ) (i : Fin m → ℕ)
    {A : Fin m → Set (Fin 5 → ℝ)} (hA : ∀ j, MeasurableSet (A j))
    {E : Set Incidence} (hE : MeasurableSet E) :
    Measure.map chartPoint (((∑ j, ENNReal.ofReal (c j) •
      Measure.map (fun b => (i j, b)) ((volume : Measure (Fin 5 → ℝ)).restrict (A j))).prod
        (volume : Measure ℝ)).restrict E) =
      volume.withDensity (sourceDensity c i A E) := by
  ext B hB
  rw [Measure.map_apply measurable_chartPoint hB,
    Measure.restrict_apply (measurable_chartPoint hB), withDensity_apply _ hB]
  rw [← Measure.sum_fintype, Measure.prod_sum_left, Measure.sum_fintype,
    Measure.finsetSum_apply]
  simp only [sourceDensity]
  rw [lintegral_finsetSum (s := Finset.univ)
    (f := fun j z => ENNReal.ofReal (c j) * (componentRegion (i j) (A j) E).indicator 1 z)
    (fun j _ => measurable_const.mul
      (measurable_one.indicator (measurable_componentRegion (i j) (hA j) hE)))]
  apply Finset.sum_congr rfl
  intro j _
  have htag : Measurable (fun b : Fin 5 → ℝ => (i j, b)) := by fun_prop
  have htagTime : Measurable (Prod.map (fun b : Fin 5 → ℝ => (i j, b)) (id : ℝ → ℝ)) :=
    htag.prodMap measurable_id
  have hZ : MeasurableSet (chartPoint ⁻¹' B ∩ E) := (measurable_chartPoint hB).inter hE
  rw [Measure.prod_smul_left, Measure.smul_apply, smul_eq_mul,
    lintegral_const_mul _ (measurable_one.indicator
      (measurable_componentRegion (i j) (hA j) hE))]
  congr 1
  rw [← Measure.map_id (μ := (volume : Measure ℝ)),
    Measure.map_prod_map _ _ htag measurable_id,
    Measure.map_apply htagTime hZ, Measure.restrict_prod_eq_prod_univ,
    Measure.restrict_apply (htagTime hZ),
    ← measurePreserving_unshear.measure_preimage
      ((htagTime hZ).inter ((hA j).prod MeasurableSet.univ)).nullMeasurableSet,
    lintegral_indicator_one (measurable_componentRegion (i j) (hA j) hE),
    Measure.restrict_apply (measurable_componentRegion (i j) (hA j) hE)]
  congr 1
  ext z
  have hstate : Prod.map (fun b : Fin 5 → ℝ => (i j, b)) (id : ℝ → ℝ) (unshear z) =
      stateAt (i j) z := rfl
  simp only [mem_preimage, mem_inter_iff, mem_prod, mem_univ, and_true,
    componentRegion, mem_ofPred_eq, hstate, chartPoint_stateAt]
  change ((z ∈ B ∧ stateAt (i j) z ∈ E) ∧ chartCoefficients z ∈ A j) ↔ _
  tauto

def eventFiber (E : Set Incidence) (i : ℕ) : Set (Fin 6 → ℝ) :=
  {b | ((i, fun e : Fin 5 => b e.castSucc), b 5) ∈ E}

theorem eventFiber_eventPoint (E : Set Incidence) (i : ℕ) (z : Fin 6 → ℝ) :
    eventPoint z ∈ eventFiber E i ↔ stateAt i z ∈ E := by
  simp only [eventFiber, mem_ofPred_eq, eventPoint_last, eventPoint, Fin.snoc_castSucc]
  rfl

theorem sourceDensity_ofReal {m : ℕ} (c : Fin m → ℝ) (hc : ∀ j, 0 ≤ c j)
    (i : Fin m → ℕ) (A : Fin m → Set (Fin 5 → ℝ)) (E : Set Incidence) (z : Fin 6 → ℝ) :
    sourceDensity c i A E z = ENNReal.ofReal
      (∑ j, scalarComponentDensity (c j) (A j) (eventFiber E (i j)) z) := by
  classical
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ =>
    (scalarComponentDensity_bound (hc j) _ _ z).1)]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : chartCoefficients z ∈ A j ∧ stateAt (i j) z ∈ E
  · simp [sourceDensity, scalarComponentDensity, eventFiber_eventPoint, componentRegion, h]
  · simp [sourceDensity, scalarComponentDensity, eventFiber_eventPoint, componentRegion, h]

end Submission.Obl.k4_scalar_pure_multiworld_homogenization
