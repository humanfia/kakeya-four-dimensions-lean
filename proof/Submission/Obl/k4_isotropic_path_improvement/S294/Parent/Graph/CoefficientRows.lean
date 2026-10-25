-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Graph.CoefficientRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Graph/CoefficientRows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Physical velocity rows for an arbitrary table of seven
trajectory coefficients `c` (signal `c0 + c1 t + c2 t²`, base `(t, c3 + c4 t,
c5 + c6 t)`), under any finite line law, assembled over coarse cubes.

Per cube the rows are `Jets2.coefficient_duration_rows` (this LOT tree, o265,
session x1027, ported in `ParentSource/Broad/Source/Jets2/DurationRows.lean`):
only the jets `c1, c2, c4, c6` are bounded, intercepts are arbitrary. The
assembly over cubes follows `physical_velocity_rows_assembly`.
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2.DurationRows
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.PhysicalAssembly

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 600000

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.Jets2
open Submission.Obl.k4_initial_horizon_bound
open scoped ENNReal

noncomputable section

variable {Λ : Type} [MeasurableSpace Λ]

/-- Dyadic fine coefficient cells lie in one coarse cube. -/
theorem coefficientGridCode_coarse_eq_coarsen (c : Λ → Fin 7 → ℝ)
    {baseMesh hidden coarse : ℝ} (bs hs : ℕ)
    (hbaseDy : coarse = baseMesh * (2 : ℝ) ^ bs) (hhidDy : coarse = hidden * (2 : ℝ) ^ hs)
    (z : Λ × ℝ) :
    coefficientGridCode c coarse coarse z =
      coarsenPhysicalCode bs hs (coefficientGridCode c baseMesh hidden z) := by
  funext j
  dsimp only [coarsenPhysicalCode, coefficientGridCode]
  simp only [ite_self]
  by_cases hj : j = 3
  · simp only [ite_eq_left hj]
    rw [hhidDy, div_mul_eq_div_div, Submission.Lib.K4XInterface.floor_div_two_pow]
  · simp only [ite_eq_right hj]
    rw [hbaseDy, div_mul_eq_div_div, Submission.Lib.K4XInterface.floor_div_two_pow]

/-- The rows of one coarse cube. The bad broad mass is charged to the
EARLIER cube mass; the fractional loss to the current cube mass. -/
theorem coefficient_cell_rows (ν : Measure Λ) [IsFiniteMeasure ν]
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (earlier current : Set (Λ × ℝ)) (hearlier : MeasurableSet earlier)
    (hearlierUnit : earlier ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hcurrent : MeasurableSet current) (hcurrentUnit : current ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {coarse : ℝ} (hcoarse : 0 < coarse) (q : Fin 4 → ℤ)
    {H K baseMesh hidden lossRate liftRho baseRho fraction baseFraction dimension ε : ℝ}
    (hH : 1 ≤ H) (hjets : ∀ l, |c l 1| ≤ H ∧ |c l 2| ≤ H ∧ |c l 4| ≤ H ∧ |c l 6| ≤ H)
    (hK : 6 * H ≤ K) (hbase : 0 < baseMesh) (hbaseHidden : baseMesh ≤ hidden)
    (hshape : coarse = hidden ^ ((2 : ℝ) / 3)) (hRate : 0 < lossRate)
    (hRateK : lossRate⁻¹ ≤ K) (hlift : 0 < liftRho) (hbaseRho : 0 ≤ baseRho)
    (hfraction : 0 < fraction) (hfrac : fraction < baseFraction) (hε : 0 ≤ ε)
    (hquad : 8 * K * coarse ^ 2 < hidden) (hdir : 32 * K * coarse ≤ liftRho / 2)
    (hconditioned : 1 ≤ K * baseRho ^ 3) (hsmall : 36 * K ^ 3 * (K * liftRho) ≤ 1)
    (hbudget : 256 * curvatureRowConstant ^ 3 * K ^ 9 * hidden ^ ((1 - dimension) / 3) ≤
      (fraction * liftRho / 4) ^ 4 * ε ^ 4)
    (S : Finset (Fin 4 → ℤ)) (hS : S.Nonempty)
    (hcount : (S.card : ℝ) ≤ K * (coarse / baseMesh) ^ 3 * (coarse / hidden) ^ dimension)
    (hcover : ∀ z ∈ current ∩ coefficientGridCode c coarse coarse ⁻¹' {q},
      coefficientGridCode c baseMesh hidden z ∈ S)
    (hlong : ∀ z ∈ current ∩ coefficientGridCode c coarse coarse ⁻¹' {q},
      ENNReal.ofReal (lossRate * coarse) ≤
        incidenceDuration (earlier ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) z.1)
    (hbroad : ∀ label (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ V < 3 →
      baseFraction * (((ν.prod volume).restrict
          (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q})).restrict
            (coefficientGridCode c baseMesh hidden ⁻¹' {label})).real univ ≤
        (((ν.prod volume).restrict
          (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q})).restrict
            (coefficientGridCode c baseMesh hidden ⁻¹' {label})).real
          {z | baseRho ≤ Metric.infDist (coefficientBase (c z.1)) (V : Set _)}) :
    ∃ row : (Fin 4 → ℤ) → Fin 3 → ℝ, Measurable row ∧ (∀ a j, |row a j| ≤ 28 * K ^ 6) ∧
      ∃ kept : Set (Λ × ℝ), MeasurableSet kept ∧
        kept ⊆ current ∩ coefficientGridCode c coarse coarse ⁻¹' {q} ∧
        (ν.prod volume).real (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) ≤
          (ν.prod volume).real kept +
            ε * (ν.prod volume).real (earlier ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) +
            fraction * (ν.prod volume).real
              (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) ∧
        ∀ z ∈ kept, |(c z.1 1 + 2 * c z.1 2 * z.2) -
          (row (coefficientGridCode c baseMesh hidden z) 0 +
            row (coefficientGridCode c baseMesh hidden z) 1 * c z.1 4 +
            row (coefficientGridCode c baseMesh hidden z) 2 * c z.1 6)| ≤
          80 * K ^ 7 * liftRho := by
  classical
  have hfine : Measurable (coefficientGridCode c baseMesh hidden) :=
    measurable_coefficientGridCode hc baseMesh hidden
  have hcoarseM : Measurable (coefficientGridCode c coarse coarse) :=
    measurable_coefficientGridCode hc coarse coarse
  set src := current ∩ coefficientGridCode c coarse coarse ⁻¹' {q} with hsrcDef
  have hsrc : MeasurableSet src := hcurrent.inter (hcoarseM (measurableSet_singleton q))
  have hsrcUnit : src ⊆ univ ×ˢ Icc (0 : ℝ) 1 := fun z hz => hcurrentUnit hz.1
  obtain ⟨n, hn, hncard, code, cell, hcode, hinj, hcellS, hvalid, hlaws⟩ :=
    finite_state_enumeration_with_laws (coefficientGridCode c baseMesh hidden) hfine S hS
  let μ := (ν.prod volume).restrict src
  have hcovae : ∀ᵐ z ∂μ, coefficientGridCode c baseMesh hidden z ∈ S := by
    filter_upwards [ae_restrict_mem hsrc] with z hz
    exact hcover z hz
  have hbroadEnum : ∀ i, cellBroad μ code
      (fun z => coefficientBase (c z.1)) baseRho baseFraction i := by
    intro i V hV
    rw [hlaws μ hcovae i]
    exact hbroad (cell i) V hV
  have hcountn : (n : ℝ) ≤ K * (coarse / baseMesh) ^ 3 * (coarse / hidden) ^ dimension :=
    (Nat.cast_le.mpr hncard).trans hcount
  obtain ⟨row, kept, hrow, hkept, hsub, hbound, hloss, hfit⟩ :=
    coefficient_duration_rows ν c hc earlier src hearlier hearlierUnit hsrc hsrcUnit hcoarse q
      hH hjets hK hbase hbaseHidden hshape hRate hRateK hlift hbaseRho hfraction hfrac hε hquad
      hdir hconditioned hsmall hbudget cell hinj code hcode hcountn
      (fun z hz => hvalid z (hcover z hz)) (fun z hz => hz.2) hlong hbroadEnum
  refine ⟨row, hrow, hbound, kept, hkept, hsub, ?_, hfit⟩
  have hμfin : IsFiniteMeasure μ :=
    ⟨by rw [Measure.restrict_apply_univ]; exact prod_unit_finite ν hsrcUnit⟩
  have hsplit : μ.real kept + μ.real keptᶜ = μ.real univ := measureReal_add_measureReal_compl hkept
  have hμk : μ.real kept = (ν.prod volume).real kept := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply hkept, inter_eq_left.mpr hsub]
  have hμu : μ.real univ = (ν.prod volume).real src := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply_univ]
  have hρ : ((ν.prod volume).restrict earlier).real (coefficientGridCode c coarse coarse ⁻¹' {q}) =
      (ν.prod volume).real (earlier ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) := by
    rw [measureReal_def, measureReal_def,
      Measure.restrict_apply (hcoarseM (measurableSet_singleton q)), inter_comm]
  rw [hρ] at hloss
  change μ.real keptᶜ ≤ _ + fraction * μ.real univ at hloss
  rw [← hμk, ← hμu]
  linarith only [hsplit, hloss]

/-- Coarse-cube rows assemble into one measurable row on fine codes. -/
theorem coefficient_rows_assembly (ν : Measure Λ) [IsFiniteMeasure ν]
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (earlier current : Set (Λ × ℝ)) (hearlier : MeasurableSet earlier)
    (hearlierUnit : earlier ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hcurrent : MeasurableSet current) (hcurrentUnit : current ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {baseMesh hidden coarse : ℝ} (bs hs : ℕ)
    (hbaseDy : coarse = baseMesh * (2 : ℝ) ^ bs) (hhidDy : coarse = hidden * (2 : ℝ) ^ hs)
    (C : Finset (Fin 4 → ℤ)) (hC : ∀ z ∈ current, coefficientGridCode c coarse coarse z ∈ C)
    {rowBound fitError ε fraction : ℝ} (hrowBound : 0 ≤ rowBound) (hε : 0 ≤ ε)
    (hcells : ∀ q ∈ C, ∃ rowq : (Fin 4 → ℤ) → Fin 3 → ℝ, (∀ a j, |rowq a j| ≤ rowBound) ∧
      ∃ keptq : Set (Λ × ℝ), MeasurableSet keptq ∧
        keptq ⊆ current ∩ coefficientGridCode c coarse coarse ⁻¹' {q} ∧
        (ν.prod volume).real (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) ≤
          (ν.prod volume).real keptq +
            ε * (ν.prod volume).real (earlier ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) +
            fraction * (ν.prod volume).real
              (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) ∧
        ∀ z ∈ keptq, |(c z.1 1 + 2 * c z.1 2 * z.2) -
          (rowq (coefficientGridCode c baseMesh hidden z) 0 +
            rowq (coefficientGridCode c baseMesh hidden z) 1 * c z.1 4 +
            rowq (coefficientGridCode c baseMesh hidden z) 2 * c z.1 6)| ≤ fitError) :
    ∃ (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (retained : Set (Λ × ℝ)),
      Measurable row ∧ MeasurableSet retained ∧ retained ⊆ current ∧
      (∀ a j, |row a j| ≤ rowBound) ∧
      (ν.prod volume).real current ≤ (ν.prod volume).real retained +
        ε * (ν.prod volume).real earlier + fraction * (ν.prod volume).real current ∧
      ∀ z ∈ retained, |(c z.1 1 + 2 * c z.1 2 * z.2) -
          (row (coefficientGridCode c baseMesh hidden z) 0 +
            row (coefficientGridCode c baseMesh hidden z) 1 * c z.1 4 +
            row (coefficientGridCode c baseMesh hidden z) 2 * c z.1 6)| ≤ fitError := by
  classical
  have hstate : Measurable (coefficientGridCode c coarse coarse) :=
    measurable_coefficientGridCode hc coarse coarse
  choose! rows hrows kept hkept hkeptSub hloss hfit using hcells
  let μ := (ν.prod volume).restrict current
  let ρ := (ν.prod volume).restrict earlier
  have hμfin : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ]; exact prod_unit_finite ν hcurrentUnit⟩
  have hρfin : IsFiniteMeasure ρ := ⟨by
    rw [Measure.restrict_apply_univ]; exact prod_unit_finite ν hearlierUnit⟩
  have hcell (q : Fin 4 → ℤ) : MeasurableSet (coefficientGridCode c coarse coarse ⁻¹' {q}) :=
    hstate (measurableSet_singleton q)
  have hμcell (q : Fin 4 → ℤ) : μ.real (coefficientGridCode c coarse coarse ⁻¹' {q}) =
      (ν.prod volume).real (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply (hcell q), inter_comm]
  have hρcell (q : Fin 4 → ℤ) : ρ.real (coefficientGridCode c coarse coarse ⁻¹' {q}) =
      (ν.prod volume).real (earlier ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply (hcell q), inter_comm]
  have hμkept (q : Fin 4 → ℤ) (hq : q ∈ C) :
      μ.real (kept q) = (ν.prod volume).real (kept q) := by
    rw [measureReal_def, measureReal_def, Measure.restrict_apply (hkept q hq),
      inter_eq_left.mpr (fun z hz => (hkeptSub q hq hz).1)]
  have hcover : ∀ᵐ z ∂μ, coefficientGridCode c coarse coarse z ∈ C := by
    filter_upwards [ae_restrict_mem hcurrent] with z hz
    exact hC z hz
  have hsel : ∀ q ∈ C, kept q ⊆ coefficientGridCode c coarse coarse ⁻¹' {q} :=
    fun q hq z hz => (hkeptSub q hq hz).2
  have hlocal : ∀ q ∈ C, μ.real (coefficientGridCode c coarse coarse ⁻¹' {q}) ≤
      μ.real (kept q) + ε * ρ.real (coefficientGridCode c coarse coarse ⁻¹' {q}) +
        fraction * μ.real (coefficientGridCode c coarse coarse ⁻¹' {q}) := by
    intro q hq
    rw [hμcell, hρcell, hμkept q hq]
    exact hloss q hq
  obtain ⟨hunion, hmass⟩ := finite_partition_relative_selection μ ρ
    (coefficientGridCode c coarse coarse) hstate C hcover kept hkept hsel hε hlocal
  let retained := ⋃ q ∈ C, kept q
  have hretSub : retained ⊆ current := by
    intro z hz
    obtain ⟨q, hz⟩ := mem_iUnion.mp hz
    obtain ⟨hq, hz⟩ := mem_iUnion.mp hz
    exact (hkeptSub q hq hz).1
  let row : (Fin 4 → ℤ) → Fin 3 → ℝ := fun a =>
    if coarsenPhysicalCode bs hs a ∈ C then rows (coarsenPhysicalCode bs hs a) a else 0
  refine ⟨row, retained, measurable_of_countable _, hunion, hretSub, ?_, ?_, ?_⟩
  · intro a j
    dsimp only [row]
    split_ifs with ha
    · exact hrows _ ha a j
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
    have hcz : coarsenPhysicalCode bs hs (coefficientGridCode c baseMesh hidden z) = q := by
      rw [← coefficientGridCode_coarse_eq_coarsen c bs hs hbaseDy hhidDy z]
      exact (hkeptSub q hq hz).2
    have hrow : row (coefficientGridCode c baseMesh hidden z) =
        rows q (coefficientGridCode c baseMesh hidden z) := by
      simp only [row, hcz, ite_eq_left hq]
    rw [hrow]
    exact hfit q hq z hz

/-- Per-label breadth of the current events gives the per-cube form. -/
theorem coefficient_cell_broad (ν : Measure Λ) (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (current : Set (Λ × ℝ)) (hcurrent : MeasurableSet current)
    {baseMesh hidden coarse : ℝ} (bs hs : ℕ)
    (hbaseDy : coarse = baseMesh * (2 : ℝ) ^ bs) (hhidDy : coarse = hidden * (2 : ℝ) ^ hs)
    {baseRho baseFraction : ℝ} (hbf : 0 ≤ baseFraction)
    (hbroad : ∀ label (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ V < 3 →
      baseFraction *
          (ν.prod volume).real (current ∩ coefficientGridCode c baseMesh hidden ⁻¹' {label}) ≤
        (ν.prod volume).real (current ∩ coefficientGridCode c baseMesh hidden ⁻¹' {label} ∩
          {z | baseRho ≤ Metric.infDist (coefficientBase (c z.1)) (V : Set _)}))
    (q label : Fin 4 → ℤ) (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)))
    (hV : Module.finrank ℝ V < 3) :
    baseFraction * (((ν.prod volume).restrict
        (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q})).restrict
          (coefficientGridCode c baseMesh hidden ⁻¹' {label})).real univ ≤
      (((ν.prod volume).restrict
        (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q})).restrict
          (coefficientGridCode c baseMesh hidden ⁻¹' {label})).real
        {z | baseRho ≤ Metric.infDist (coefficientBase (c z.1)) (V : Set _)} := by
  have hfineM := measurable_coefficientGridCode hc baseMesh hidden
  have hcoarseM := measurable_coefficientGridCode hc coarse coarse
  have hA : MeasurableSet (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) :=
    hcurrent.inter (hcoarseM (measurableSet_singleton q))
  have hB : MeasurableSet (coefficientGridCode c baseMesh hidden ⁻¹' {label}) :=
    hfineM (measurableSet_singleton label)
  have key (t : Set (Λ × ℝ)) : (((ν.prod volume).restrict
      (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q})).restrict
        (coefficientGridCode c baseMesh hidden ⁻¹' {label})) t =
      (ν.prod volume) (t ∩ coefficientGridCode c baseMesh hidden ⁻¹' {label} ∩
        (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q})) := by
    rw [Measure.restrict_apply' hB, Measure.restrict_apply' hA]
  simp only [measureReal_def, key]
  by_cases hql : coarsenPhysicalCode bs hs label = q
  · have hset (t : Set (Λ × ℝ)) : t ∩ coefficientGridCode c baseMesh hidden ⁻¹' {label} ∩
        (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) =
          current ∩ coefficientGridCode c baseMesh hidden ⁻¹' {label} ∩ t := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff]
      constructor
      · rintro ⟨⟨ht, hl⟩, hcur, -⟩
        exact ⟨⟨hcur, hl⟩, ht⟩
      · rintro ⟨⟨hcur, hl⟩, ht⟩
        refine ⟨⟨ht, hl⟩, hcur, ?_⟩
        rw [coefficientGridCode_coarse_eq_coarsen c bs hs hbaseDy hhidDy z, hl, hql]
    rw [hset, hset, inter_univ]
    simpa only [measureReal_def] using hbroad label V hV
  · have hset (t : Set (Λ × ℝ)) : t ∩ coefficientGridCode c baseMesh hidden ⁻¹' {label} ∩
        (current ∩ coefficientGridCode c coarse coarse ⁻¹' {q}) = ∅ := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, mem_empty_iff_false,
        iff_false, not_and]
      rintro ⟨-, hl⟩ - hq
      apply hql
      rw [← hl, ← coefficientGridCode_coarse_eq_coarsen c bs hs hbaseDy hhidDy z, hq]
    rw [hset, hset, measure_empty, ENNReal.toReal_zero, mul_zero]

/-- **Physical velocity rows of a coefficient table.** Inputs per coarse
cube: a finite fine-code table with the hereditary count, the earlier
duration witnesses, and per-fine-cell velocity breadth; plus the numerical
scale relations. The fit is `|ż - row(code)·(1, c4, c6)| ≤ 80 K⁷ liftRho`
on a retained subset of the current events, with loss charged to the
earlier mass and to a fraction of the current mass. -/
theorem coefficient_velocity_rows (ν : Measure Λ) [IsFiniteMeasure ν]
    (c : Λ → Fin 7 → ℝ) (hc : Measurable c)
    (earlier current : Set (Λ × ℝ)) (hearlier : MeasurableSet earlier)
    (hearlierUnit : earlier ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hcurrent : MeasurableSet current) (hcurrentUnit : current ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {baseMesh hidden coarse : ℝ} (bs hs : ℕ)
    (hbaseDy : coarse = baseMesh * (2 : ℝ) ^ bs) (hhidDy : coarse = hidden * (2 : ℝ) ^ hs)
    {H K lossRate liftRho baseRho fraction baseFraction dimension ε : ℝ}
    (hH : 1 ≤ H) (hjets : ∀ l, |c l 1| ≤ H ∧ |c l 2| ≤ H ∧ |c l 4| ≤ H ∧ |c l 6| ≤ H)
    (hK : 6 * H ≤ K) (hbase : 0 < baseMesh) (hbaseHidden : baseMesh ≤ hidden)
    (hshape : coarse = hidden ^ ((2 : ℝ) / 3)) (hRate : 0 < lossRate)
    (hRateK : lossRate⁻¹ ≤ K) (hlift : 0 < liftRho) (hbaseRho : 0 ≤ baseRho)
    (hfraction : 0 < fraction) (hfrac : fraction < baseFraction) (hε : 0 ≤ ε)
    (hquad : 8 * K * coarse ^ 2 < hidden) (hdir : 32 * K * coarse ≤ liftRho / 2)
    (hconditioned : 1 ≤ K * baseRho ^ 3) (hsmall : 36 * K ^ 3 * (K * liftRho) ≤ 1)
    (hbudget : 256 * curvatureRowConstant ^ 3 * K ^ 9 * hidden ^ ((1 - dimension) / 3) ≤
      (fraction * liftRho / 4) ^ 4 * ε ^ 4)
    (C : Finset (Fin 4 → ℤ)) (hC : ∀ z ∈ current, coefficientGridCode c coarse coarse z ∈ C)
    (hcount : ∀ q ∈ C, ∃ S : Finset (Fin 4 → ℤ), S.Nonempty ∧
      (S.card : ℝ) ≤ K * (coarse / baseMesh) ^ 3 * (coarse / hidden) ^ dimension ∧
      ∀ z ∈ current, coefficientGridCode c coarse coarse z = q →
        coefficientGridCode c baseMesh hidden z ∈ S)
    (hlong : ∀ z ∈ current, ENNReal.ofReal (lossRate * coarse) ≤
      incidenceDuration (earlier ∩ coefficientGridCode c coarse coarse ⁻¹'
        {coefficientGridCode c coarse coarse z}) z.1)
    (hbroad : ∀ label (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ V < 3 →
      baseFraction *
          (ν.prod volume).real (current ∩ coefficientGridCode c baseMesh hidden ⁻¹' {label}) ≤
        (ν.prod volume).real (current ∩ coefficientGridCode c baseMesh hidden ⁻¹' {label} ∩
          {z | baseRho ≤ Metric.infDist (coefficientBase (c z.1)) (V : Set _)})) :
    ∃ (row : (Fin 4 → ℤ) → Fin 3 → ℝ) (retained : Set (Λ × ℝ)),
      Measurable row ∧ MeasurableSet retained ∧ retained ⊆ current ∧
      (∀ a j, |row a j| ≤ 28 * K ^ 6) ∧
      (ν.prod volume).real current ≤ (ν.prod volume).real retained +
        ε * (ν.prod volume).real earlier + fraction * (ν.prod volume).real current ∧
      ∀ z ∈ retained, |(c z.1 1 + 2 * c z.1 2 * z.2) -
          (row (coefficientGridCode c baseMesh hidden z) 0 +
            row (coefficientGridCode c baseMesh hidden z) 1 * c z.1 4 +
            row (coefficientGridCode c baseMesh hidden z) 2 * c z.1 6)| ≤
        80 * K ^ 7 * liftRho := by
  have hK0 : 0 ≤ K := by linarith
  have hcoarse : 0 < coarse := by
    rw [hshape]; exact Real.rpow_pos_of_pos (hbase.trans_le hbaseHidden) _
  apply coefficient_rows_assembly ν c hc earlier current hearlier hearlierUnit hcurrent
    hcurrentUnit bs hs hbaseDy hhidDy C hC (by positivity : 0 ≤ 28 * K ^ 6) hε
  intro q hq
  obtain ⟨S, hS, hcard, hcov⟩ := hcount q hq
  obtain ⟨row, hrow, hbound, kept, hkept, hsub, hloss, hfit⟩ :=
    coefficient_cell_rows ν c hc earlier current hearlier hearlierUnit hcurrent hcurrentUnit
      hcoarse q hH hjets hK hbase hbaseHidden hshape hRate hRateK hlift hbaseRho hfraction hfrac
      hε hquad hdir hconditioned hsmall hbudget S hS hcard (fun z hz => hcov z hz.1 hz.2)
      (fun z hz => by
        have hh := hlong z hz.1
        have hzq : coefficientGridCode c coarse coarse z = q := hz.2
        rwa [hzq] at hh)
      (fun label V hV => coefficient_cell_broad ν c hc current hcurrent bs hs hbaseDy hhidDy
        (hfraction.le.trans hfrac.le) hbroad q label V hV)
  exact ⟨row, hbound, kept, hkept, hsub, hloss, hfit⟩

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
