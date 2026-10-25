/-
Adapted from LOT tree oai_074_kakeya_four_dimensions, obligation o229,
session x0953, commit 0550557e0ee631cdb80af3bce6af2b9797c55f37, file
Submission/Lib/K4ScalarJets/ScalarFiniteCellRestriction.lean.
Original o078/x0260 and support-module attributions are retained below.
-/

/-
Adapted from: here:o078
Workspace source: Submission/Obl/k4_scalar_exact_angular_packets/ScalarFiniteCellRestriction.lean, as present on o078/x0260 at 100cb70f4e2bc558030ccb66635bad5348c6f54c.
The original proof and any original attribution comments are preserved below.
-/

import Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarCellMass

/-! Assemble original trajectory restrictions chosen separately in finite time cells. -/

namespace Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar

open MeasureTheory Set
open scoped BigOperators

theorem original_finite_time_cell_restriction {Λ Θ ι : Type*}
    [MeasurableSpace Λ] [MeasurableSpace Θ] [Fintype ι]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (ν : Measure Λ) [IsFiniteMeasure ν] (μ : Measure Θ) [IsFiniteMeasure μ]
    {E : Set (Λ × Θ)} (hE : MeasurableSet E) (code : Θ → ι) (hcode : Measurable code)
    (A : ι → Set Λ) (hA : ∀ i, MeasurableSet (A i)) {α : ℝ}
    (hselect : ∀ i, α * (ν.prod μ).real (E ∩ (fun q => code q.2) ⁻¹' {i}) ≤
      (ν.prod μ).real ((E ∩ (fun q => code q.2) ⁻¹' {i}) ∩ (A i ×ˢ univ))) :
    ∃ R : Set (Λ × Θ), MeasurableSet R ∧ R ⊆ E ∧
      α * (ν.prod μ).real E ≤ (ν.prod μ).real R ∧
      ∀ q ∈ R, q.1 ∈ A (code q.2) := by
  classical
  let P : Set (Λ × Θ) := ⋃ i : ι, A i ×ˢ (code ⁻¹' {i})
  let R := E ∩ P
  have hP : MeasurableSet P := MeasurableSet.iUnion (fun i =>
    (hA i).prod (hcode (MeasurableSet.singleton i)))
  have hRm : MeasurableSet R := hE.inter hP
  have hmem q : q ∈ P ↔ q.1 ∈ A (code q.2) := by
    constructor
    · intro hq
      obtain ⟨i, hi⟩ := mem_iUnion.mp hq
      exact hi.2 ▸ hi.1
    · intro hq
      exact mem_iUnion.mpr ⟨code q.2, hq, rfl⟩
  have hcell i : R ∩ (fun q => code q.2) ⁻¹' {i} =
      (E ∩ (fun q => code q.2) ⁻¹' {i}) ∩ (A i ×ˢ univ) := by
    ext q
    constructor
    · intro hq
      exact ⟨⟨hq.1.1, hq.2⟩, hq.2 ▸ (hmem q).mp hq.1.2, mem_univ _⟩
    · intro hq
      have hi : code q.2 = i := hq.1.2
      exact ⟨⟨hq.1.1, (hmem q).mpr (by simpa only [hi] using hq.2.1)⟩, hq.1.2⟩
  have hcm : Measurable (fun q : Λ × Θ => code q.2) := hcode.comp measurable_snd
  have hmassE := sum_original_code_masses (ν.prod μ) hE hcm Finset.univ (fun _ _ => Finset.mem_univ _)
  have hmassR := sum_original_code_masses (ν.prod μ) hRm hcm Finset.univ (fun _ _ => Finset.mem_univ _)
  refine ⟨R, hRm, inter_subset_left, ?_, fun q hq => (hmem q).mp hq.2⟩
  calc
    _ = ∑ i : ι, α * (ν.prod μ).real (E ∩ (fun q => code q.2) ⁻¹' {i}) := by
      rw [← Finset.mul_sum, hmassE]
    _ ≤ ∑ i : ι, (ν.prod μ).real (R ∩ (fun q => code q.2) ⁻¹' {i}) :=
      Finset.sum_le_sum (fun i _ => by rw [hcell]; exact hselect i)
    _ = _ := hmassR

end Submission.Obl.k4_scalar_normal_first_jet.Backend.ScalarPlanar
