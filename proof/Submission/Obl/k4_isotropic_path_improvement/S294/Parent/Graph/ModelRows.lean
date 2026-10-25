-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Graph.ModelRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Graph/ModelRows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Physical velocity rows on a `Qualification.PhysicalModel`
(seven coefficients per original line: quadratic signal `c0 + c1 t + c2 t²`,
base `(t, c3 + c4 t, c5 + c6 t)`). The coefficient table is cut off outside
the model's assignment; nothing changes on the model's events.

Output, in the model's own terms: a row on the literal fine physical codes
`modelCode` with `|(signal l)'(t) - Σ row(code)_j · velocity_j| ≤ 80 K⁷ liftRho`
on a retained subset of the current events (the graph estimate consumed by
`Qualification.PhysicalModel.physical_native_qualification`).
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.CoefficientRows
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.Interface

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open Submission.Obl.k4_initial_horizon_bound
open scoped ENNReal

noncomputable section

open Classical in
/-- The coefficient table of a physical model, zero off its assignment. -/
def modelCoefficients (pm : Qualification.PhysicalModel) (l : Ln) : Fin 7 → ℝ :=
  if l ∈ pm.assigned then pm.scalarCoefficients l else 0

theorem measurable_modelCoefficients (pm : Qualification.PhysicalModel) :
    Measurable (modelCoefficients pm) := by
  classical
  unfold modelCoefficients
  exact Measurable.ite pm.measurable_assigned pm.measurable_scalarCoefficients measurable_const

theorem modelCoefficients_of_mem (pm : Qualification.PhysicalModel) {l : Ln}
    (hl : l ∈ pm.assigned) : modelCoefficients pm l = pm.scalarCoefficients l := by
  unfold modelCoefficients
  exact if_pos hl

/-- The fine physical code of an incidence of the model: `baseMesh` in time
and in the two base coordinates, `hidden` in the signal. -/
def modelCode (pm : Qualification.PhysicalModel) (baseMesh hidden : ℝ) (z : Ev) : Fin 4 → ℤ :=
  coefficientGridCode (modelCoefficients pm) baseMesh hidden z

theorem measurable_modelCode (pm : Qualification.PhysicalModel) (baseMesh hidden : ℝ) :
    Measurable (modelCode pm baseMesh hidden) :=
  measurable_coefficientGridCode (measurable_modelCoefficients pm) baseMesh hidden

/-- On an assigned line the code reads the literal time, base and signal. -/
theorem modelCode_apply (pm : Qualification.PhysicalModel) (baseMesh hidden : ℝ) {z : Ev}
    (hz : z.1 ∈ pm.assigned) :
    modelCode pm baseMesh hidden z = fun j =>
      ⌊(![z.2, pm.position z.1 1 + z.2 * pm.velocity z.1 1,
          pm.position z.1 2 + z.2 * pm.velocity z.1 2, pm.signalValue z.1 z.2] : Fin 4 → ℝ) j /
        (if j = 3 then hidden else baseMesh)⌋ := by
  funext j
  simp only [modelCode, coefficientGridCode, modelCoefficients_of_mem pm hz]
  congr 2
  fin_cases j <;>
    simp [coefficientPhysical, Qualification.PhysicalModel.position,
      Qualification.PhysicalModel.velocity, Qualification.PhysicalModel.signalValue,
      Qualification.Jets2.zy, Qualification.Jets2.zx] <;> ring

theorem coefficientBase_model (pm : Qualification.PhysicalModel) {l : Ln}
    (hl : l ∈ pm.assigned) :
    coefficientBase (modelCoefficients pm l) = WithLp.toLp 2 (pm.velocity l) := by
  rw [modelCoefficients_of_mem pm hl]
  unfold coefficientBase
  congr 1
  funext j
  fin_cases j <;> rfl

theorem model_jets (pm : Qualification.PhysicalModel) {H : ℝ} (hH : 1 ≤ H)
    (hjets : ∀ l ∈ pm.assigned, |pm.scalarCoefficients l 1| ≤ H ∧
      |pm.scalarCoefficients l 2| ≤ H ∧ |pm.scalarCoefficients l 4| ≤ H ∧
        |pm.scalarCoefficients l 6| ≤ H) (l : Ln) :
    |modelCoefficients pm l 1| ≤ H ∧ |modelCoefficients pm l 2| ≤ H ∧
      |modelCoefficients pm l 4| ≤ H ∧ |modelCoefficients pm l 6| ≤ H := by
  by_cases hl : l ∈ pm.assigned
  · rw [modelCoefficients_of_mem pm hl]
    exact hjets l hl
  · have h0 : modelCoefficients pm l = 0 := by
      unfold modelCoefficients
      exact if_neg hl
    have hH0 : (0 : ℝ) ≤ H := zero_le_one.trans hH
    simp only [h0, Pi.zero_apply, abs_zero]
    exact ⟨hH0, hH0, hH0, hH0⟩

/-- The jets of a model are bounded by its slack. -/
theorem model_jets_of_slack (pm : Qualification.PhysicalModel) :
    ∀ l ∈ pm.assigned, |pm.scalarCoefficients l 1| ≤ max 1 (17 * pm.slack) ∧
      |pm.scalarCoefficients l 2| ≤ max 1 (17 * pm.slack) ∧
      |pm.scalarCoefficients l 4| ≤ max 1 (17 * pm.slack) ∧
      |pm.scalarCoefficients l 6| ≤ max 1 (17 * pm.slack) := by
  intro l hl
  exact ⟨(pm.scalar_coefficients_bound l hl 1).trans (le_max_right _ _),
    (pm.scalar_coefficients_bound l hl 2).trans (le_max_right _ _),
    (pm.scalar_coefficients_bound l hl 4).trans (le_max_right _ _),
    (pm.scalar_coefficients_bound l hl 6).trans (le_max_right _ _)⟩

/-- Earlier coarse-duration witnesses for the model, against the unchanged
line law (x1027's `exists_coefficient_coarse_duration_source`). -/
theorem model_coarse_durations (pm : Qualification.PhysicalModel) {H : ℝ} (hH : 1 ≤ H)
    (hjets : ∀ l ∈ pm.assigned, |pm.scalarCoefficients l 1| ≤ H ∧
      |pm.scalarCoefficients l 2| ≤ H ∧ |pm.scalarCoefficients l 4| ≤ H ∧
        |pm.scalarCoefficients l 6| ≤ H)
    (ν : Measure Ln) [SFinite ν] {coarse lossRate : ℝ} (hcoarse : 0 < coarse)
    (hcoarse1 : coarse ≤ 1) (hRate : 0 ≤ lossRate)
    (E : Set Ev) (hE : MeasurableSet E) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    ∃ keep : Set Ev, MeasurableSet keep ∧ keep ⊆ E ∧
      (ν.prod volume) (E \ keep) ≤ ENNReal.ofReal (5 * lossRate * (6 * H + 5) ^ 4) * ν univ ∧
      (∀ z ∈ keep, ENNReal.ofReal (lossRate * coarse) ≤
        incidenceDuration (E ∩ modelCode pm coarse coarse ⁻¹'
          {modelCode pm coarse coarse z}) z.1) ∧
      ∀ q : Fin 4 → ℤ,
        ENNReal.ofReal (lossRate * coarse) *
            ν {l | ENNReal.ofReal (lossRate * coarse) ≤
              incidenceDuration (E ∩ modelCode pm coarse coarse ⁻¹' {q}) l} ≤
          (ν.prod volume) (E ∩ modelCode pm coarse coarse ⁻¹' {q}) :=
  exists_coefficient_coarse_duration_source ν (modelCoefficients pm)
    (measurable_modelCoefficients pm) hH hcoarse hcoarse1 hRate (model_jets pm hH hjets)
    E hE hunit

/-- **Physical velocity rows of a physical model.** -/
theorem model_velocity_rows (pm : Qualification.PhysicalModel) {H : ℝ} (hH : 1 ≤ H)
    (hjets : ∀ l ∈ pm.assigned, |pm.scalarCoefficients l 1| ≤ H ∧
      |pm.scalarCoefficients l 2| ≤ H ∧ |pm.scalarCoefficients l 4| ≤ H ∧
        |pm.scalarCoefficients l 6| ≤ H)
    (ν : Measure Ln) [IsFiniteMeasure ν]
    (earlier current : Set Ev) (hearlier : MeasurableSet earlier)
    (hearlierE : earlier ⊆ pm.event) (hcurrent : MeasurableSet current)
    (hcurrentE : current ⊆ pm.event)
    {baseMesh hidden coarse : ℝ} (bs hs : ℕ)
    (hbaseDy : coarse = baseMesh * (2 : ℝ) ^ bs) (hhidDy : coarse = hidden * (2 : ℝ) ^ hs)
    {K lossRate liftRho baseRho fraction baseFraction dimension ε : ℝ}
    (hK : 6 * H ≤ K) (hbase : 0 < baseMesh) (hbaseHidden : baseMesh ≤ hidden)
    (hshape : coarse = hidden ^ ((2 : ℝ) / 3)) (hRate : 0 < lossRate)
    (hRateK : lossRate⁻¹ ≤ K) (hlift : 0 < liftRho) (hbaseRho : 0 ≤ baseRho)
    (hfraction : 0 < fraction) (hfrac : fraction < baseFraction) (hε : 0 ≤ ε)
    (hquad : 8 * K * coarse ^ 2 < hidden) (hdir : 32 * K * coarse ≤ liftRho / 2)
    (hconditioned : 1 ≤ K * baseRho ^ 3) (hsmall : 36 * K ^ 3 * (K * liftRho) ≤ 1)
    (hbudget : 256 * curvatureRowConstant ^ 3 * K ^ 9 * hidden ^ ((1 - dimension) / 3) ≤
      (fraction * liftRho / 4) ^ 4 * ε ^ 4)
    (C : Finset (Fin 4 → ℤ)) (hC : ∀ z ∈ current, modelCode pm coarse coarse z ∈ C)
    (hcount : ∀ q ∈ C, ∃ S : Finset (Fin 4 → ℤ), S.Nonempty ∧
      (S.card : ℝ) ≤ K * (coarse / baseMesh) ^ 3 * (coarse / hidden) ^ dimension ∧
      ∀ z ∈ current, modelCode pm coarse coarse z = q → modelCode pm baseMesh hidden z ∈ S)
    (hlong : ∀ z ∈ current, ENNReal.ofReal (lossRate * coarse) ≤
      incidenceDuration (earlier ∩ modelCode pm coarse coarse ⁻¹'
        {modelCode pm coarse coarse z}) z.1)
    (hbroad : ∀ label (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ V < 3 →
      baseFraction * (ν.prod volume).real (current ∩ modelCode pm baseMesh hidden ⁻¹' {label}) ≤
        (ν.prod volume).real (current ∩ modelCode pm baseMesh hidden ⁻¹' {label} ∩
          {z | baseRho ≤ Metric.infDist (WithLp.toLp 2 (pm.velocity z.1) :
            EuclideanSpace ℝ (Fin 3)) (V : Set _)})) :
    ∃ (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (retained : Set Ev),
      Measurable row ∧ MeasurableSet retained ∧ retained ⊆ current ∧
      (∀ a j, |row a j| ≤ 28 * K ^ 6) ∧
      (ν.prod volume).real current ≤ (ν.prod volume).real retained +
        ε * (ν.prod volume).real earlier + fraction * (ν.prod volume).real current ∧
      ∀ z ∈ retained, |(pm.signal z.1).derivative.eval z.2 -
          ∑ j, row (modelCode pm baseMesh hidden z) j * pm.velocity z.1 j| ≤
        80 * K ^ 7 * liftRho := by
  have hbroad' : ∀ label (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))),
      Module.finrank ℝ V < 3 →
      baseFraction * (ν.prod volume).real
          (current ∩ coefficientGridCode (modelCoefficients pm) baseMesh hidden ⁻¹' {label}) ≤
        (ν.prod volume).real
          (current ∩ coefficientGridCode (modelCoefficients pm) baseMesh hidden ⁻¹' {label} ∩
            {z | baseRho ≤ Metric.infDist (coefficientBase (modelCoefficients pm z.1))
              (V : Set _)}) := by
    intro label V hV
    have hset : current ∩ coefficientGridCode (modelCoefficients pm) baseMesh hidden ⁻¹' {label} ∩
        {z | baseRho ≤ Metric.infDist (coefficientBase (modelCoefficients pm z.1)) (V : Set _)} =
        current ∩ modelCode pm baseMesh hidden ⁻¹' {label} ∩
          {z | baseRho ≤ Metric.infDist (WithLp.toLp 2 (pm.velocity z.1) :
            EuclideanSpace ℝ (Fin 3)) (V : Set _)} := by
      ext z
      simp only [mem_inter_iff, mem_setOf_eq]
      constructor
      · rintro ⟨⟨hz, hl⟩, hd⟩
        refine ⟨⟨hz, hl⟩, ?_⟩
        rwa [← coefficientBase_model pm (pm.event_assignment z (hcurrentE hz))]
      · rintro ⟨⟨hz, hl⟩, hd⟩
        refine ⟨⟨hz, hl⟩, ?_⟩
        rwa [coefficientBase_model pm (pm.event_assignment z (hcurrentE hz))]
    rw [hset]
    exact hbroad label V hV
  obtain ⟨row, retained, hrow, hret, hsub, hbound, hloss, hfit⟩ :=
    coefficient_velocity_rows ν (modelCoefficients pm) (measurable_modelCoefficients pm)
      earlier current hearlier (hearlierE.trans pm.event_unit_time) hcurrent
      (hcurrentE.trans pm.event_unit_time) bs hs hbaseDy hhidDy hH (model_jets pm hH hjets) hK
      hbase hbaseHidden hshape hRate hRateK hlift hbaseRho hfraction hfrac hε hquad hdir
      hconditioned hsmall hbudget C hC hcount hlong hbroad'
  refine ⟨row, retained, hrow, hret, hsub, hbound, hloss, ?_⟩
  intro z hz
  have hl : z.1 ∈ pm.assigned := pm.event_assignment z (hcurrentE (hsub hz))
  have hh := hfit z hz
  rw [modelCoefficients_of_mem pm hl] at hh
  have hderiv := pm.scalar_x_derivative z.1 z.2
  rw [← hderiv, Fin.sum_univ_three]
  have hv1 : pm.velocity z.1 1 = pm.scalarCoefficients z.1 4 := rfl
  have hv2 : pm.velocity z.1 2 = pm.scalarCoefficients z.1 6 := rfl
  have hv0 : pm.velocity z.1 0 = 1 := rfl
  rw [hv0, hv1, hv2]
  have heq : pm.scalarCoefficients z.1 1 + 2 * pm.scalarCoefficients z.1 2 * z.2 -
      (row (modelCode pm baseMesh hidden z) 0 * 1 +
        row (modelCode pm baseMesh hidden z) 1 * pm.scalarCoefficients z.1 4 +
        row (modelCode pm baseMesh hidden z) 2 * pm.scalarCoefficients z.1 6) =
      (pm.scalarCoefficients z.1 1 + 2 * pm.scalarCoefficients z.1 2 * z.2) -
        (row (coefficientGridCode (modelCoefficients pm) baseMesh hidden z) 0 +
          row (coefficientGridCode (modelCoefficients pm) baseMesh hidden z) 1 *
            pm.scalarCoefficients z.1 4 +
          row (coefficientGridCode (modelCoefficients pm) baseMesh hidden z) 2 *
            pm.scalarCoefficients z.1 6) := by
    simp only [modelCode, mul_one]
  rw [heq]
  exact hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
