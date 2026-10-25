-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Graph.PhysicalAssembly, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Graph/PhysicalAssembly.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Assembly of coarse-cell physical rows into one row on the
literal fine physical codes. Follows `assemble_original_velocity_rows`
(this LOT tree, o265, session x0943, Broad/Source/OriginalRowAssembly.lean)
in the frame-free model; the coarse cell is a function of the fine code by
dyadic nesting, and earlier coarse masses sum before any normalization.
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.PhysicalRows
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PhysicalCodeCoarsening
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoarseSelectionMass

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 600000

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open scoped ENNReal

noncomputable section

variable {X : Type} [MeasurableSpace X]

/-- Dyadic rectangular fine cells lie in one coarse cube. -/
theorem nativeCoarseCode_eq_coarsen (P0 : MvPolynomial (Fin 4) ℝ) (p v : X → Fin 4 → ℝ)
    {baseMesh hidden coarse : ℝ} (bs hs : ℕ)
    (hbaseDy : coarse = baseMesh * (2 : ℝ) ^ bs) (hhidDy : coarse = hidden * (2 : ℝ) ^ hs)
    (z : X × ℝ) :
    nativeCoarseCode P0 p v coarse z =
      coarsenPhysicalCode bs hs (physCode P0 p v baseMesh hidden z) := by
  funext j
  dsimp only [coarsenPhysicalCode, nativeCoarseCode, physCode]
  by_cases hj : j = 3
  · simp only [ite_eq_left hj]
    rw [hhidDy, div_mul_eq_div_div, Submission.Lib.K4XInterface.floor_div_two_pow]
  · simp only [ite_eq_right hj]
    rw [hbaseDy, div_mul_eq_div_div, Submission.Lib.K4XInterface.floor_div_two_pow]

theorem prod_unit_finite (ν : Measure X) [IsFiniteMeasure ν] {S : Set (X × ℝ)}
    (hS : S ⊆ univ ×ˢ Icc (0 : ℝ) 1) : (ν.prod volume) S < ⊤ := by
  calc (ν.prod volume) S ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hS
    _ = ν univ * volume (Icc (0 : ℝ) 1) := Measure.prod_prod _ _
    _ < ⊤ := by
      rw [Real.volume_Icc]
      exact ENNReal.mul_lt_top (measure_lt_top ν univ) ENNReal.ofReal_lt_top

/-- Coarse-cell rows assemble into one measurable row on fine codes. -/
theorem physical_velocity_rows_assembly (ν : Measure X) [IsFiniteMeasure ν]
    (P0 : MvPolynomial (Fin 4) ℝ) (p v : X → Fin 4 → ℝ) (hpm : Measurable p) (hvm : Measurable v)
    (scalar : X × ℝ → ℝ)
    (earlier current : Set (X × ℝ)) (hearlier : MeasurableSet earlier)
    (hearlierUnit : earlier ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hcurrent : MeasurableSet current) (hcurrentUnit : current ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {baseMesh hidden coarse : ℝ} (bs hs : ℕ)
    (hbaseDy : coarse = baseMesh * (2 : ℝ) ^ bs) (hhidDy : coarse = hidden * (2 : ℝ) ^ hs)
    (C : Finset (Fin 4 → ℤ)) (hC : ∀ z ∈ current, nativeCoarseCode P0 p v coarse z ∈ C)
    {rowBound fitError ε fraction : ℝ} (hrowBound : 0 ≤ rowBound) (hε : 0 ≤ ε)
    (hcells : ∀ q ∈ C, ∃ rowq : (Fin 4 → ℤ) → Fin 3 → ℝ, (∀ c j, |rowq c j| ≤ rowBound) ∧
      ∃ keptq : Set (X × ℝ), MeasurableSet keptq ∧
        keptq ⊆ coarseCellSource P0 p v coarse current q ∧
        (ν.prod volume).real (coarseCellSource P0 p v coarse current q) ≤
          (ν.prod volume).real keptq +
            ε * (ν.prod volume).real (coarseCellSource P0 p v coarse earlier q) +
            fraction * (ν.prod volume).real (coarseCellSource P0 p v coarse current q) ∧
        ∀ z ∈ keptq, |scalar z -
          ∑ j : Fin 3, rowq (physCode P0 p v baseMesh hidden z) j * v z.1 j.castSucc| ≤ fitError) :
    ∃ (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (retained : Set (X × ℝ)),
      Measurable row ∧ MeasurableSet retained ∧ retained ⊆ current ∧
      (∀ c j, |row c j| ≤ rowBound) ∧
      (ν.prod volume).real current ≤ (ν.prod volume).real retained +
        ε * (ν.prod volume).real earlier + fraction * (ν.prod volume).real current ∧
      ∀ z ∈ retained, |scalar z -
        ∑ j : Fin 3, row (physCode P0 p v baseMesh hidden z) j * v z.1 j.castSucc| ≤ fitError := by
  classical
  have hcurve := measurable_physCurve P0 p v hpm hvm
  have hstate := measurable_nativeCoarseCode P0 p v hcurve coarse
  choose! rows hrows kept hkept hkeptSub hloss hfit using hcells
  let μ := (ν.prod volume).restrict current
  let ρ := (ν.prod volume).restrict earlier
  have hμfin : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ]; exact prod_unit_finite ν hcurrentUnit⟩
  have hρfin : IsFiniteMeasure ρ := ⟨by
    rw [Measure.restrict_apply_univ]; exact prod_unit_finite ν hearlierUnit⟩
  have hcell (q : Fin 4 → ℤ) : MeasurableSet (nativeCoarseCode P0 p v coarse ⁻¹' {q}) :=
    hstate (measurableSet_singleton q)
  have hμcell (q : Fin 4 → ℤ) : μ.real (nativeCoarseCode P0 p v coarse ⁻¹' {q}) =
      (ν.prod volume).real (coarseCellSource P0 p v coarse current q) := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply (hcell q), inter_comm]
    rfl
  have hρcell (q : Fin 4 → ℤ) : ρ.real (nativeCoarseCode P0 p v coarse ⁻¹' {q}) =
      (ν.prod volume).real (coarseCellSource P0 p v coarse earlier q) := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply (hcell q), inter_comm]
    rfl
  have hμkept (q : Fin 4 → ℤ) (hq : q ∈ C) : μ.real (kept q) = (ν.prod volume).real (kept q) := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply (hkept q hq),
      inter_eq_left.mpr (fun z hz => (hkeptSub q hq hz).1)]
  have hcover : ∀ᵐ z ∂μ, nativeCoarseCode P0 p v coarse z ∈ C := by
    filter_upwards [ae_restrict_mem hcurrent] with z hz
    exact hC z hz
  have hsel : ∀ q ∈ C, kept q ⊆ nativeCoarseCode P0 p v coarse ⁻¹' {q} :=
    fun q hq z hz => (hkeptSub q hq hz).2
  have hlocal : ∀ q ∈ C, μ.real (nativeCoarseCode P0 p v coarse ⁻¹' {q}) ≤ μ.real (kept q) +
      ε * ρ.real (nativeCoarseCode P0 p v coarse ⁻¹' {q}) +
        fraction * μ.real (nativeCoarseCode P0 p v coarse ⁻¹' {q}) := by
    intro q hq
    rw [hμcell, hρcell, hμkept q hq]
    exact hloss q hq
  obtain ⟨hunion, hmass⟩ := finite_partition_relative_selection μ ρ
    (nativeCoarseCode P0 p v coarse) hstate C hcover kept hkept hsel hε hlocal
  let retained := ⋃ q ∈ C, kept q
  have hretSub : retained ⊆ current := by
    intro z hz
    obtain ⟨q, hz⟩ := mem_iUnion.mp hz
    obtain ⟨hq, hz⟩ := mem_iUnion.mp hz
    exact (hkeptSub q hq hz).1
  let row : (Fin 4 → ℤ) → Fin 3 → ℝ := fun c =>
    if coarsenPhysicalCode bs hs c ∈ C then rows (coarsenPhysicalCode bs hs c) c else 0
  refine ⟨row, retained, measurable_of_countable _, hunion, hretSub, ?_, ?_, ?_⟩
  · intro c j
    dsimp only [row]
    split_ifs with hc
    · exact hrows _ hc c j
    · simpa only [Pi.zero_apply, abs_zero] using hrowBound
  · have hμu : μ.real univ = (ν.prod volume).real current := by
      rw [measureReal_def, measureReal_def, Measure.restrict_apply_univ]
    have hρu : ρ.real univ = (ν.prod volume).real earlier := by
      rw [measureReal_def, measureReal_def, Measure.restrict_apply_univ]
    have hμr : μ.real retained = (ν.prod volume).real retained := by
      rw [measureReal_def, measureReal_def, Measure.restrict_apply hunion,
        inter_eq_left.mpr hretSub]
    rw [← hμu, ← hρu, ← hμr]
    exact hmass
  · intro z hz
    obtain ⟨q, hz⟩ := mem_iUnion.mp hz
    obtain ⟨hq, hz⟩ := mem_iUnion.mp hz
    have hcz : coarsenPhysicalCode bs hs (physCode P0 p v baseMesh hidden z) = q := by
      rw [← nativeCoarseCode_eq_coarsen P0 p v bs hs hbaseDy hhidDy z]
      exact (hkeptSub q hq hz).2
    have hrow : row (physCode P0 p v baseMesh hidden z) =
        rows q (physCode P0 p v baseMesh hidden z) := by
      simp only [row, hcz, ite_eq_left hq]
    rw [hrow]
    exact hfit q hq z hz

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
