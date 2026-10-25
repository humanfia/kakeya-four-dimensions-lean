-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Graph.PhysicalRows, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Graph/PhysicalRows.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Physical velocity rows on one coarse cell for an arbitrary
quadratic test, on literal fine physical codes.
Follows `exists_original_coarse_velocity_rows` (this LOT tree, o265,
session x0943, Broad/Source/OriginalVelocityRowSource.lean) in the
frame-free model of `PhysicalModel`.
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.PhysicalValidity

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 600000

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.SourceGeometry
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
open Submission.Obl.k4_initial_horizon_bound
open Submission.Obl.k4_mk_grid_transfer
open scoped ENNReal

noncomputable section

variable {X : Type} [MeasurableSpace X]

/-- The physical rows of one coarse cell. The bad broad mass is charged to
the EARLIER cell mass; the fractional loss to the current cell mass. -/
theorem physical_coarse_velocity_rows (ν : Measure X) [IsFiniteMeasure ν]
    (P0 : MvPolynomial (Fin 4) ℝ)
    (p v : X → Fin 4 → ℝ) (hpm : Measurable p) (hvm : Measurable v)
    (hp0 : ∀ x, p x 0 = 0) (hv0 : ∀ x, v x 0 = 1)
    (qa qb qc : X → ℝ) (hqa : Measurable qa) (hqb : Measurable qb)
    (hquad : ∀ x t, MvPolynomial.eval (fun j => p x j + t * v x j) P0 =
      qa x * t ^ 2 + qb x * t + qc x)
    {K : ℝ} (hwhole : ∀ x t, t ∈ Icc (0 : ℝ) 1 →
      |MvPolynomial.eval (fun j => p x j + t * v x j) P0| ≤ K)
    (hraw : ∀ x t, t ∈ Icc (0 : ℝ) 1 →
      ‖liftedVector (fun j => v x j.castSucc) (2 * qa x * t + qb x)‖ ≤ K)
    (earlier current : Set (X × ℝ)) (hearlier : MeasurableSet earlier)
    (hearlierUnit : earlier ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    (hcurrent : MeasurableSet current) (hcurrentUnit : current ⊆ univ ×ˢ Icc (0 : ℝ) 1)
    {coarse : ℝ} (hcoarse : 0 < coarse) (q : Fin 4 → ℤ)
    {baseMesh hidden lossRate liftRho baseRho fraction baseFraction dimension ε : ℝ}
    (hbase : 0 < baseMesh) (hbaseHidden : baseMesh ≤ hidden)
    (hshape : coarse = hidden ^ ((2 : ℝ) / 3)) (hRate : 0 < lossRate)
    (hRateK : lossRate⁻¹ ≤ K) (hK1 : 1 ≤ K)
    (hlift : 0 < liftRho) (hbaseRho : 0 ≤ baseRho) (hfraction : 0 < fraction)
    (hfraction1 : fraction < baseFraction) (hε : 0 ≤ ε)
    (hquadError : 8 * K * coarse ^ 2 < hidden)
    (hdirError : 32 * K * coarse ≤ liftRho / 2)
    (hconditioned : 1 ≤ K * baseRho ^ 3)
    (hsmall : 36 * K ^ 3 * (K * liftRho) ≤ 1)
    (hbudget : 256 * nativeRowConstant ^ 3 * K ^ 9 * hidden ^ ((1 - dimension) / 3) ≤
      (fraction * liftRho / 4) ^ 4 * ε ^ 4)
    (S : Finset (Fin 4 → ℤ)) (hS : S.Nonempty)
    (hcount : (S.card : ℝ) ≤ K * (coarse / baseMesh) ^ 3 * (coarse / hidden) ^ dimension)
    (hcover : ∀ z ∈ coarseCellSource P0 p v coarse current q,
      physCode P0 p v baseMesh hidden z ∈ S)
    (hlong : ∀ z ∈ coarseCellSource P0 p v coarse current q,
      ENNReal.ofReal (lossRate * coarse) ≤
        incidenceDuration (coarseCellSource P0 p v coarse earlier q) z.1)
    (hbroad : ∀ label (V : Submodule ℝ (EuclideanSpace ℝ (Fin 3))), Module.finrank ℝ V < 3 →
      baseFraction * (((ν.prod volume).restrict (coarseCellSource P0 p v coarse current q)).restrict
        (physCode P0 p v baseMesh hidden ⁻¹' {label})).real univ ≤
      (((ν.prod volume).restrict (coarseCellSource P0 p v coarse current q)).restrict
        (physCode P0 p v baseMesh hidden ⁻¹' {label})).real
          {z | baseRho ≤ Metric.infDist (WithLp.toLp 2 (fun j : Fin 3 => v z.1 j.castSucc) :
            EuclideanSpace ℝ (Fin 3)) (V : Set _)}) :
    ∃ row : (Fin 4 → ℤ) → Fin 3 → ℝ, Measurable row ∧ (∀ c j, |row c j| ≤ 28 * K ^ 6) ∧
      ∃ kept : Set (X × ℝ), MeasurableSet kept ∧
        kept ⊆ coarseCellSource P0 p v coarse current q ∧
        (ν.prod volume).real (coarseCellSource P0 p v coarse current q) ≤
          (ν.prod volume).real kept +
            ε * (ν.prod volume).real (coarseCellSource P0 p v coarse earlier q) +
            fraction * (ν.prod volume).real (coarseCellSource P0 p v coarse current q) ∧
        ∀ z ∈ kept, |2 * qa z.1 * z.2 + qb z.1 -
          ∑ j : Fin 3, row (physCode P0 p v baseMesh hidden z) j * v z.1 j.castSucc| ≤
            80 * K ^ 7 * liftRho := by
  classical
  have hcurve := measurable_physCurve P0 p v hpm hvm
  have hphys := measurable_physCode P0 p v hcurve baseMesh hidden
  obtain ⟨n, hn, hncard, code, cell, hcode, hinj, hcellS, hvalid, hlaws⟩ :=
    finite_state_enumeration_with_laws (physCode P0 p v baseMesh hidden) hphys S hS
  set src := coarseCellSource P0 p v coarse current q with hsrc
  have hsrcm : MeasurableSet src := measurableSet_coarseCellSource P0 p v hcurve coarse hcurrent q
  let μ := (ν.prod volume).restrict src
  have hcellEq : ∀ z ∈ src, cell (code z) = physCode P0 p v baseMesh hidden z :=
    fun z hz => hvalid z (hcover z hz)
  have hcovae : ∀ᵐ z ∂μ, physCode P0 p v baseMesh hidden z ∈ S := by
    filter_upwards [ae_restrict_mem hsrcm] with z hz
    exact hcover z hz
  have hbroadEnum : ∀ i, cellBroad μ code
      (fun z => (WithLp.toLp 2 (fun j : Fin 3 => v z.1 j.castSucc) : EuclideanSpace ℝ (Fin 3)))
      baseRho baseFraction i := by
    intro i V hV
    rw [hlaws μ hcovae i]
    exact hbroad (cell i) V hV
  have hcountn : (n : ℝ) ≤ K * (coarse / baseMesh) ^ 3 * (coarse / hidden) ^ dimension :=
    (Nat.cast_le.mpr hncard).trans hcount
  have ha := cellModel_valid ν P0 p v hpm hvm hp0 hv0 qa qb qc hqa hqb hquad hwhole hraw
    earlier current hearlier hearlierUnit hcurrent hcurrentUnit hcoarse q hbase hbaseHidden
    hshape hRate hRateK hK1 hlift hbaseRho hfraction.le hfraction1 hquadError hdirError
    hconditioned hsmall code cell hinj hcode hcountn hcellEq hlong hbroadEnum
  set a := cellModel ν P0 p v qa qb qc earlier current coarse q baseMesh hidden lossRate K liftRho
    baseRho fraction baseFraction dimension code cell with hadef
  have hinc : a.incidence = μ := cellModel_incidence ν P0 p v hcurve qa qb qc earlier current
    hcurrent coarse q baseMesh hidden lossRate K liftRho baseRho fraction baseFraction dimension
    code cell hlong
  obtain ⟨row, T, hrowMeas, hT, hrow, hloss, hmoment, hfit⟩ :=
    native_literal_rows_fixed a ha (physCode P0 p v baseMesh hidden) src hcellEq
  have hbad : a.broadMass ≤ ε * a.priorScale := by
    apply bad_mass_le_of_quartic_remainder (bad := a.broadMass) (M := a.priorScale) (ε := ε)
      (coefficient := (fraction * liftRho / 4) ^ 4)
      (remainder := 256 * nativeRowConstant ^ 3 * K ^ 9 * hidden ^ ((1 - dimension) / 3))
      measureReal_nonneg measureReal_nonneg
      (pow_pos (div_pos (mul_pos hfraction hlift) (by norm_num)) 4) hε
    · have hab : a.bound = K := rfl
      have ham : a.mesh = hidden := rfl
      have had : a.dimension = dimension := rfl
      rw [hab, ham, had] at hmoment
      exact hmoment.trans_eq (by ring)
    · exact hbudget
  have hμfin : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    calc (ν.prod volume) src ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) :=
          measure_mono (fun z hz => hcurrentUnit hz.1)
      _ = ν univ * volume (Icc (0 : ℝ) 1) := Measure.prod_prod _ _
      _ < ⊤ := by
        rw [Real.volume_Icc]
        exact ENNReal.mul_lt_top (measure_lt_top ν univ) ENNReal.ofReal_lt_top
  refine ⟨row, hrowMeas, hrow, T ∩ src, hT.inter hsrcm, inter_subset_right, ?_, ?_⟩
  · have hsplit : μ.real T + μ.real Tᶜ = μ.real univ := measureReal_add_measureReal_compl hT
    have hμT : μ.real T = (ν.prod volume).real (T ∩ src) := by
      rw [measureReal_def, measureReal_def, Measure.restrict_apply hT]
    have hμu : μ.real univ = (ν.prod volume).real src := by
      rw [measureReal_def, measureReal_def, Measure.restrict_apply_univ]
    rw [hinc] at hloss
    change μ.real Tᶜ ≤ a.broadMass + fraction * μ.real univ at hloss
    have hprior : a.priorScale = (ν.prod volume).real
        (coarseCellSource P0 p v coarse earlier q) := rfl
    rw [hprior] at hbad
    rw [← hμT, ← hμu]
    linarith only [hsplit, hloss, hbad]
  · intro z hz
    exact (hfit z ⟨hz.1, hz.2⟩).2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
