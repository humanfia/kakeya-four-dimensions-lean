/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarCollisionMeasureModel.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarCollisionMeasureModel.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarFrozenCollisions
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCollisionCellCaps
import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCellMass
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.Floor

/-! Actual original scalar collisions and their derived grid ceilings. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open scoped BigOperators

noncomputable def scalarCollisionPairCeiling (p K d C error : ℝ) : ℝ :=
  (C * p ^ (1 + d)) * (C * ((2 * (error + 6 * K + 2 * K ^ 2) + 1) * p) ^ (1 + d))

theorem scalarCollisionPairCeiling_pos {p K d C error : ℝ}
    (hp : 0 < p) (hK : 1 ≤ K) (hC : 0 < C) (he : 0 ≤ error) :
    0 < scalarCollisionPairCeiling p K d C error := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  unfold scalarCollisionPairCeiling
  positivity

structure OriginalScalarCollisionModel {Λ : Type*} [MeasurableSpace Λ]
    (ν : Measure Λ) (p K d C error : ℝ) where
  labels : Set Λ
  velocity : Λ → ℝ
  startValue : Λ → ℝ
  velocity_measurable : Measurable velocity
  startValue_measurable : Measurable startValue
  row : ℝ → ℝ
  slopeGraph : ℝ → ℝ
  row_zero : row 0 = 0
  row_compare : ∀ x y, |row x - row y| ≤ |x - y|
  slope_compare : ∀ x y, |slopeGraph x - slopeGraph y| ≤ K * |x - y|
  coordinate_bound : ∀ l ∈ labels, |velocity l| ≤ K ∧ |slopeGraph (velocity l)| ≤ K
  scalarSupport : Set ℝ
  start_support : ∀ l ∈ labels, startValue l ∈ scalarSupport
  timeGrid : Finset ℤ
  velocityGrid : Finset ℤ
  velocity_cover : ∀ l ∈ labels, ⌊velocity l / p⌋ ∈ velocityGrid
  velocity_witness : ∀ j ∈ velocityGrid, ∃ l ∈ labels, ⌊velocity l / p⌋ = j
  startBin : ℤ
  pairEvent : Set (ℝ × (Λ × Λ))
  pair_measurable : MeasurableSet pairEvent
  time_cover : ∀ q ∈ pairEvent, ⌊q.1 / p⌋ ∈ timeGrid
  pair_geometry : ∀ q ∈ pairEvent, |q.1| ≤ 1 ∧ q.2.1 ∈ labels ∧ q.2.2 ∈ labels ∧
    ⌊startValue q.2.1 / p⌋ = startBin ∧
    |q.1 * (slopeGraph (velocity q.2.1) - slopeGraph (velocity q.2.2)) +
      row q.1 * (velocity q.2.1 - velocity q.2.2) - (startValue q.2.2 - startValue q.2.1)| ≤ error * p
  joint_cap : ∀ a b r : ℝ, p ≤ r →
    ν.real {l | l ∈ labels ∧ velocity l ∈ Icc a (a + r) ∧ startValue l ∈ Icc b (b + r)} ≤ C * r ^ (1 + d)

namespace OriginalScalarCollisionModel

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} [IsFiniteMeasure ν]
  {p K d C error : ℝ} (D : OriginalScalarCollisionModel ν p K d C error)

noncomputable def tupleCode (q : ℝ × (Λ × Λ)) : ℤ × ℤ × ℤ :=
  (⌊q.1 / p⌋, ⌊D.velocity q.2.1 / p⌋, ⌊D.velocity q.2.2 / p⌋)

theorem tupleCode_measurable : Measurable D.tupleCode :=
  (Int.measurable_floor.comp (measurable_fst.div_const p)).prodMk
    ((Int.measurable_floor.comp ((D.velocity_measurable.comp measurable_snd.fst).div_const p)).prodMk
      (Int.measurable_floor.comp ((D.velocity_measurable.comp measurable_snd.snd).div_const p)))

theorem tupleCode_cover : ∀ q ∈ D.pairEvent, D.tupleCode q ∈ D.timeGrid ×ˢ (D.velocityGrid ×ˢ D.velocityGrid) := by
  intro q hq
  have hg := D.pair_geometry q hq
  exact Finset.mem_product.mpr ⟨D.time_cover q hq, Finset.mem_product.mpr
    ⟨D.velocity_cover _ hg.2.1, D.velocity_cover _ hg.2.2.1⟩⟩

theorem pair_cell_cap (hp : 0 < p) (hK : 1 ≤ K) (hC : 0 ≤ C) (he : 0 ≤ error)
    (u : ℝ) (j j' : ℤ) :
    (ν.prod ν).real {q : Λ × Λ | (u, q) ∈ D.pairEvent ∧
      ⌊D.velocity q.1 / p⌋ = j ∧ ⌊D.velocity q.2 / p⌋ = j'} ≤
      scalarCollisionPairCeiling p K d C error := by
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  let R := error + 6 * K + 2 * K ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  apply original_pair_collision_cell_cap ν D.labels D.velocity D.startValue hC hp hR D.joint_cap
    (D := u * (D.slopeGraph (p * j) - D.slopeGraph (p * j')) + D.row u * (p * j - p * j'))
  intro q hq
  obtain ⟨hu, hl, hl', hz, hactual⟩ := D.pair_geometry (u, q) hq.1
  have hv := mesh_lower_endpoint hp hq.2.1
  have hv' := mesh_lower_endpoint hp hq.2.2
  have hbin := mesh_lower_endpoint hp hz
  have hfreeze := scalar_dot_freeze hK hp.le D.row_zero D.row_compare D.slope_compare
    (u := u) (t := u) (by simpa only [sub_self, abs_zero] using hp.le) hu
    (D.coordinate_bound _ hl).1 (D.coordinate_bound _ hl').1
    (D.coordinate_bound _ hl).2 (D.coordinate_bound _ hl').2 hv.2.le hv'.2.le
  have hrelation := (frozen_scalar_collision_relation hactual hfreeze hbin.2.le).1
  exact ⟨hl, hl', hv.1, hv'.1, hbin.1, by simpa only [R, add_assoc] using hrelation⟩

theorem pair_section_cap (hp : 0 < p) (hK : 1 ≤ K) (hC : 0 ≤ C) (he : 0 ≤ error)
    (u : ℝ) : (ν.prod ν).real (Prod.mk u ⁻¹' D.pairEvent) ≤
      (D.velocityGrid.card : ℝ) ^ 2 * scalarCollisionPairCeiling p K d C error := by
  classical
  let code : Λ × Λ → ℤ × ℤ := fun q => (⌊D.velocity q.1 / p⌋, ⌊D.velocity q.2 / p⌋)
  have hcover : ∀ q ∈ Prod.mk u ⁻¹' D.pairEvent, code q ∈ D.velocityGrid ×ˢ D.velocityGrid := by
    intro q hq
    have hg := D.pair_geometry (u, q) hq
    exact Finset.mem_product.mpr ⟨D.velocity_cover _ hg.2.1, D.velocity_cover _ hg.2.2.1⟩
  calc
    _ ≤ ∑ b ∈ D.velocityGrid ×ˢ D.velocityGrid,
        (ν.prod ν).real ((Prod.mk u ⁻¹' D.pairEvent) ∩ code ⁻¹' {b}) :=
      original_mass_le_sum_cells _ _ code _ (Filter.Eventually.of_forall hcover)
    _ ≤ ∑ _b ∈ D.velocityGrid ×ˢ D.velocityGrid, scalarCollisionPairCeiling p K d C error := by
      apply Finset.sum_le_sum
      intro b hb
      have hset : (Prod.mk u ⁻¹' D.pairEvent) ∩ code ⁻¹' {b} =
          {q : Λ × Λ | (u, q) ∈ D.pairEvent ∧ ⌊D.velocity q.1 / p⌋ = b.1 ∧ ⌊D.velocity q.2 / p⌋ = b.2} := by
        ext q
        rcases b with ⟨j, j'⟩
        simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_setOf_eq, code, Prod.mk.injEq]
      rw [hset]
      exact D.pair_cell_cap hp hK hC he u b.1 b.2
    _ = _ := by simp [Finset.card_product, pow_two]

end OriginalScalarCollisionModel

theorem original_time_grid_cap (μ : Measure ℝ) (hμ : μ ≤ volume)
    {p : ℝ} (hp : 0 < p) (k : ℤ) :
    μ {u : ℝ | ⌊u / p⌋ = k} ≤ ENNReal.ofReal p := by
  calc
    _ ≤ volume {u : ℝ | ⌊u / p⌋ = k} := hμ _
    _ ≤ volume (Icc (p * k) (p * k + p)) :=
      measure_mono (fun u hu => (mesh_lower_endpoint hp hu).1)
    _ = _ := by rw [Real.volume_Icc]; congr 1; ring

namespace OriginalScalarCollisionModel

variable {Λ : Type*} [MeasurableSpace Λ] {ν : Measure Λ} [IsFiniteMeasure ν]
  {p K d C error : ℝ} (D : OriginalScalarCollisionModel ν p K d C error)

theorem tuple_cell_cap (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≤ volume)
    (hp : 0 < p) (hK : 1 ≤ K) (hC : 0 ≤ C) (he : 0 ≤ error) (q : ℤ × ℤ × ℤ) :
    (μ.prod (ν.prod ν)).real (D.pairEvent ∩ D.tupleCode ⁻¹' {q}) ≤
      scalarCollisionPairCeiling p K d C error * p := by
  let V : Set ℝ := {u | ⌊u / p⌋ = q.1}
  have hV : MeasurableSet V := measurableSet_eq_fun
    (Int.measurable_floor.comp (measurable_id.div_const p)) measurable_const
  have hEvent : MeasurableSet (D.pairEvent ∩ D.tupleCode ⁻¹' {q}) :=
    D.pair_measurable.inter (D.tupleCode_measurable (MeasurableSet.singleton q))
  have hsub : D.pairEvent ∩ D.tupleCode ⁻¹' {q} ⊆ V ×ˢ univ := by
    intro r hr
    exact ⟨congrArg Prod.fst hr.2, mem_univ _⟩
  have hKpos : 0 < K := zero_lt_one.trans_le hK
  have hcap0 : 0 ≤ scalarCollisionPairCeiling p K d C error := by
    unfold scalarCollisionPairCeiling
    positivity
  have hcap : ∀ u ∈ V,
      (ν.prod ν).real (Prod.mk u ⁻¹' (D.pairEvent ∩ D.tupleCode ⁻¹' {q})) ≤
        scalarCollisionPairCeiling p K d C error := by
    intro u hu
    have hcell : Prod.mk u ⁻¹' (D.pairEvent ∩ D.tupleCode ⁻¹' {q}) ⊆
        {r : Λ × Λ | (u, r) ∈ D.pairEvent ∧
          ⌊D.velocity r.1 / p⌋ = q.2.1 ∧ ⌊D.velocity r.2 / p⌋ = q.2.2} := by
      intro r hr
      exact ⟨hr.1, congrArg (fun c : ℤ × ℤ × ℤ => c.2.1) hr.2,
        congrArg (fun c : ℤ × ℤ × ℤ => c.2.2) hr.2⟩
    exact (measureReal_mono hcell).trans (D.pair_cell_cap hp hK hC he u q.2.1 q.2.2)
  have hVcap : μ.real V ≤ p := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (original_time_grid_cap μ hμ hp q.1)
    simpa only [Measure.real, V, ENNReal.toReal_ofReal hp.le] using h
  exact (original_spacetime_cell_cap μ (ν.prod ν) hEvent hV hsub hcap0 hcap).trans
    (mul_le_mul_of_nonneg_left hVcap hcap0)

theorem frozen_dot_support (hp : 0 < p) (hK : 1 ≤ K)
    (q : ℝ × (Λ × Λ)) (hq : q ∈ D.pairEvent) {t : ℝ}
    (hindex : ⌊t / p⌋ = ⌊q.1 / p⌋) (ht : |t| ≤ 1) :
    ∃ s ∈ D.scalarSupport,
      |t * (D.slopeGraph (p * (⌊D.velocity q.2.1 / p⌋ : ℤ)) -
          D.slopeGraph (p * (⌊D.velocity q.2.2 / p⌋ : ℤ))) +
        D.row t * (p * (⌊D.velocity q.2.1 / p⌋ : ℤ) - p * (⌊D.velocity q.2.2 / p⌋ : ℤ)) -
          (s + -(p * D.startBin))| ≤ (error + 6 * K + 2 * K ^ 2 + 1) * p := by
  obtain ⟨hu, hl, hl', hz, hactual⟩ := D.pair_geometry q hq
  have hv := mesh_lower_endpoint hp (x := D.velocity q.2.1) rfl
  have hv' := mesh_lower_endpoint hp (x := D.velocity q.2.2) rfl
  have hbin := mesh_lower_endpoint hp hz
  have hfreeze := scalar_dot_freeze hK hp.le D.row_zero D.row_compare D.slope_compare
    (same_mesh_cell_close hp hindex.symm) ht
    (D.coordinate_bound _ hl).1 (D.coordinate_bound _ hl').1
    (D.coordinate_bound _ hl).2 (D.coordinate_bound _ hl').2 hv.2.le hv'.2.le
  refine ⟨D.startValue q.2.2, D.start_support _ hl', ?_⟩
  simpa only [sub_eq_add_neg, add_assoc] using
    (frozen_scalar_collision_relation hactual hfreeze hbin.2.le).2

end OriginalScalarCollisionModel

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
