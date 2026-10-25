import Mathlib

/-!
Adapted from: here:o049

Original proof developed by session x0147 in
Submission/Obl/k4_cap_class_terminal_charts/BlockMarginals.lean.
-/

namespace Submission.Lib.K4FinitePlankAtlases

open MeasureTheory Set

/-- The original selected trajectory law inside one block, divided only by the
block duration. It is never conditioned on success or on a trajectory packet. -/
noncomputable def blockIncidenceMarginal {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (E : Set (α × ℝ)) (s q : ℝ) : Measure α :=
  (1 / q).toNNReal • Measure.map Prod.fst
    ((ν.prod volume).restrict (E ∩ (univ ×ˢ Ico s (s + q))))

theorem blockInterval_volume (s q : ℝ) : volume (Ico s (s + q)) = ENNReal.ofReal q := by
  rw [Real.volume_Ico]
  congr 1
  ring

private theorem block_rectangle_ne_top {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (s q : ℝ) :
    (ν.prod volume) (univ ×ˢ Ico s (s + q)) ≠ ⊤ := by
  rw [Measure.prod_prod, blockInterval_volume]
  exact ENNReal.mul_ne_top (measure_ne_top ν _) ENNReal.ofReal_ne_top

/-- The block marginal is a finite law before any geometric selection. -/
theorem blockIncidenceMarginal_finite {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (E : Set (α × ℝ)) (s q : ℝ) :
    IsFiniteMeasure (blockIncidenceMarginal ν E s q) := by
  letI : IsFiniteMeasure ((ν.prod volume).restrict (E ∩ (univ ×ˢ Ico s (s + q)))) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact (measure_mono inter_subset_right).trans_lt
      (lt_top_iff_ne_top.mpr (block_rectangle_ne_top ν s q))
  unfold blockIncidenceMarginal
  infer_instance

/-- This is exactly the unnormalized original incidence mass per unit block
time, with the old prior retained. -/
theorem blockIncidenceMarginal_real {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (E : Set (α × ℝ)) (s : ℝ) {q : ℝ} (hq : 0 < q)
    (A : Set α) (hA : MeasurableSet A) :
    (blockIncidenceMarginal ν E s q).real A =
      (ν.prod volume).real (E ∩ (A ×ˢ Ico s (s + q))) / q := by
  unfold blockIncidenceMarginal
  rw [measureReal_nnreal_smul_apply, Real.coe_toNNReal _ (by positivity)]
  simp only [measureReal_def]
  rw [Measure.map_apply measurable_fst hA, Measure.restrict_apply (measurable_fst hA)]
  have heq : Prod.fst ⁻¹' A ∩ (E ∩ (univ ×ˢ Ico s (s + q))) =
      E ∩ (A ×ˢ Ico s (s + q)) := by
    ext p
    simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, true_and]
    tauto
  rw [heq]
  ring

/-- All block marginals keep the original prior budget, even for a highly
nonuniform success fraction. -/
theorem blockIncidenceMarginal_mass_le {α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsFiniteMeasure ν] (E : Set (α × ℝ)) (s : ℝ)
    {q : ℝ} (hq : 0 < q) :
    (blockIncidenceMarginal ν E s q).real univ ≤ ν.real univ := by
  rw [blockIncidenceMarginal_real ν E s hq univ MeasurableSet.univ]
  apply (div_le_iff₀ hq).mpr
  have h := measureReal_mono (μ := ν.prod volume)
    (show E ∩ (univ ×ˢ Ico s (s + q)) ⊆ univ ×ˢ Ico s (s + q) from inter_subset_right)
    (block_rectangle_ne_top ν s q)
  have hrect : (ν.prod volume).real (univ ×ˢ Ico s (s + q)) = ν.real univ * q := by
    simp only [measureReal_def, Measure.prod_prod, ENNReal.toReal_mul,
      blockInterval_volume, ENNReal.toReal_ofReal hq.le]
  rw [hrect] at h
  exact h

/-- Every atlas floor for this law is already a true original-incidence floor. -/
theorem blockIncidenceMarginal_floor_iff {α : Type*} [MeasurableSpace α]
    (ν : Measure α) (E : Set (α × ℝ)) (s : ℝ) {q ρ : ℝ} (hq : 0 < q)
    (A : Set α) (hA : MeasurableSet A) :
    ρ ≤ (blockIncidenceMarginal ν E s q).real A ↔
      q * ρ ≤ (ν.prod volume).real (E ∩ (A ×ˢ Ico s (s + q))) := by
  rw [blockIncidenceMarginal_real ν E s hq A hA]
  simpa only [mul_comm] using (le_div_iff₀ hq)

end Submission.Lib.K4FinitePlankAtlases
