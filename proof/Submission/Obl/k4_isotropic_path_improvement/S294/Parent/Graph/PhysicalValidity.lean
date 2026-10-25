-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Graph.PhysicalValidity, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Graph/PhysicalValidity.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/-
x1037 (o287). Validity of the frame-free physical velocity model.
Follows `originalNativeModel_valid` (this LOT tree, o265, session x0943,
Broad/Source/OriginalNativeValidity.lean), with the test, frame and
coefficient bounds as explicit hypotheses.
-/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph.PhysicalModel

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 400000

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

/-- The physical model of one coarse cell is valid. Its only data are the
literal physical cell enumeration, the earlier duration witnesses, per-cell
base breadth, the whole-time test bounds, and the numerical scale relations. -/
theorem cellModel_valid (ν : Measure X) [IsFiniteMeasure ν] (P0 : MvPolynomial (Fin 4) ℝ)
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
    {baseMesh hidden lossRate liftRho baseRho fraction baseFraction dimension : ℝ}
    (hbase : 0 < baseMesh) (hbaseHidden : baseMesh ≤ hidden)
    (hshape : coarse = hidden ^ ((2 : ℝ) / 3)) (hRate : 0 < lossRate)
    (hRateK : lossRate⁻¹ ≤ K) (hK1 : 1 ≤ K)
    (hlift : 0 < liftRho) (hbaseRho : 0 ≤ baseRho) (hfraction : 0 ≤ fraction)
    (hfraction1 : fraction < baseFraction)
    (hquadError : 8 * K * coarse ^ 2 < hidden)
    (hdirError : 32 * K * coarse ≤ liftRho / 2)
    (hconditioned : 1 ≤ K * baseRho ^ 3)
    (hsmall : 36 * K ^ 3 * (K * liftRho) ≤ 1)
    {n : ℕ} (code : X × ℝ → Fin n) (cell : Fin n → Fin 4 → ℤ)
    (hinj : Function.Injective cell) (hcode : Measurable code)
    (hcount : (n : ℝ) ≤ K * (coarse / baseMesh) ^ 3 * (coarse / hidden) ^ dimension)
    (hcell : ∀ z ∈ coarseCellSource P0 p v coarse current q,
      cell (code z) = physCode P0 p v baseMesh hidden z)
    (hlong : ∀ z ∈ coarseCellSource P0 p v coarse current q,
      ENNReal.ofReal (lossRate * coarse) ≤
        incidenceDuration (coarseCellSource P0 p v coarse earlier q) z.1)
    (hbroad : ∀ i, cellBroad ((ν.prod volume).restrict (coarseCellSource P0 p v coarse current q))
      code (fun z => WithLp.toLp 2 (fun j : Fin 3 => v z.1 j.castSucc)) baseRho baseFraction i) :
    (cellModel ν P0 p v qa qb qc earlier current coarse q baseMesh hidden lossRate K liftRho
      baseRho fraction baseFraction dimension code cell).Valid := by
  set a := cellModel ν P0 p v qa qb qc earlier current coarse q baseMesh hidden lossRate K liftRho
      baseRho fraction baseFraction dimension code cell with ha
  have hcurve : Measurable (fun z : X × ℝ => nativePhysicalCurve P0 (p z.1) (v z.1) z.2) := by
    unfold nativePhysicalCurve liftedVector
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j
    · exact ((measurable_pi_apply _).comp (hpm.comp measurable_fst)).add
        (measurable_snd.mul ((measurable_pi_apply _).comp (hvm.comp measurable_fst)))
    · exact ((measurable_pi_apply _).comp (hpm.comp measurable_fst)).add
        (measurable_snd.mul ((measurable_pi_apply _).comp (hvm.comp measurable_fst)))
    · exact ((measurable_pi_apply _).comp (hpm.comp measurable_fst)).add
        (measurable_snd.mul ((measurable_pi_apply _).comp (hvm.comp measurable_fst)))
    · exact (MvPolynomial.continuous_eval P0).measurable.comp
        (measurable_pi_iff.mpr fun j => ((measurable_pi_apply j).comp (hpm.comp measurable_fst)).add
          (measurable_snd.mul ((measurable_pi_apply j).comp (hvm.comp measurable_fst))))
  have hinc := cellModel_incidence ν P0 p v hcurve qa qb qc earlier current hcurrent coarse q
    baseMesh hidden lossRate K liftRho baseRho fraction baseFraction dimension code cell hlong
  have hev : MeasurableSet (coarseCellSource P0 p v coarse current q) :=
    measurableSet_coarseCellSource P0 p v hcurve coarse hcurrent q
  have hsrc : MeasurableSet (coarseCellSource P0 p v coarse earlier q) :=
    measurableSet_coarseCellSource P0 p v hcurve coarse hearlier q
  have hhidden : 0 < hidden := hbase.trans_le hbaseHidden
  have hunitFinite (S : Set (X × ℝ)) (hS : S ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
      (ν.prod volume) S < ⊤ := by
    calc (ν.prod volume) S ≤ (ν.prod volume) (univ ×ˢ Icc (0 : ℝ) 1) := measure_mono hS
      _ = ν univ * volume (Icc (0 : ℝ) 1) := Measure.prod_prod _ _
      _ < ⊤ := by
        rw [Real.volume_Icc]
        exact ENNReal.mul_lt_top (measure_lt_top ν univ) ENNReal.ofReal_lt_top
  have hcurSub : coarseCellSource P0 p v coarse current q ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => hcurrentUnit hz.1
  have hearSub : coarseCellSource P0 p v coarse earlier q ⊆ univ ×ˢ Icc (0 : ℝ) 1 :=
    fun z hz => hearlierUnit hz.1
  have hcomp (u : Fin 3 → ℝ) (w : ℝ) (i : Fin 4) :
      |(liftedVector u w) i| ≤ ‖liftedVector u w‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (liftedVector u w) i
  have hdir : Measurable (fun z : X × ℝ =>
      liftedVector (fun j => v z.1 j.castSucc) (2 * qa z.1 * z.2 + qb z.1)) := by
    unfold liftedVector
    apply (WithLp.measurable_toLp 2 _).comp
    apply measurable_pi_iff.mpr
    intro j
    fin_cases j <;> simp <;> fun_prop
  refine
    { priorFinite := by
        change IsFiniteMeasure (ν.restrict _)
        infer_instance
      incidenceFinite := by
        rw [hinc]
        refine ⟨?_⟩
        rw [Measure.restrict_apply_univ]
        exact hunitFinite _ hcurSub
      cellInjective := hinj
      weightMeas := measurable_const.indicator hev
      codeMeas := hcode
      bound_ge := hK1
      mesh_pos := hbase
      mesh_ge := hbaseHidden
      liftRho_pos := hlift
      baseRho_nonneg := hbaseRho
      fraction_nonneg := hfraction
      fraction_lt := hfraction1
      timeVelocity := hv0
      quadratic := fun x t => hquad x t
      whole := fun x t ht => hwhole x t ht
      anchorMeas := ?_
      tangentMeas := ?_
      directionMeas := ?_
      tangentError := hquadError
      directionError := hdirError
      density := ?_
      support := ?_
      priorCap := ?_
      supportCount := ?_
      boundedMeas := MeasurableSet.univ.prod measurableSet_Icc
      boundedFull := ?_
      baseBound := ?_
      scalarBound := ?_
      rawBound := ?_
      baseBroad := ?_
      conditioned := hconditioned
      small := hsmall }
  · change Measurable (fun x : X => baseMesh⁻¹ • heightScale (baseMesh / hidden)
      (nativePhysicalCurve P0 (p x) (v x) a.anchor))
    have hm : Measurable (fun x : X => heightScale (baseMesh / hidden)
        (nativePhysicalCurve P0 (p x) (v x) a.anchor)) :=
      (measurable_heightScale _).comp (hcurve.comp (measurable_id.prodMk measurable_const))
    exact hm.const_smul (baseMesh⁻¹ : ℝ)
  · change Measurable (fun x : X => liftedVector (fun j => v x j.castSucc)
      (2 * qa x * a.anchor + qb x))
    exact hdir.comp (measurable_id.prodMk measurable_const)
  · change Measurable (fun z : X × ℝ => unitTangent (liftedVector
      (fun j => (WithLp.toLp 2 (fun j : Fin 3 => v z.1 j.castSucc) :
        EuclideanSpace ℝ (Fin 3)) j) (2 * qa z.1 * z.2 + qb z.1)))
    exact measurable_unitTangent hdir
  · intro l t
    change Set.indicator _ (fun _ => (1 : ENNReal)) (l, t) ≤ ENNReal.ofReal K
    exact (Set.indicator_le_self _ (fun _ => (1 : ENNReal)) (l, t)).trans
      (by simpa using ENNReal.ofReal_le_ofReal hK1)
  · intro l t ht
    have hmem : (l, t) ∈ coarseCellSource P0 p v coarse current q := by
      by_contra h
      apply ht
      change Set.indicator _ (fun _ => (1 : ENNReal)) (l, t) = 0
      exact Set.indicator_of_notMem h _
    refine ⟨?_, ?_⟩
    · have hq0 := congrFun hmem.2 0
      change ⌊nativePhysicalCurve P0 (p l) (v l) t 0 / coarse⌋ = q 0 at hq0
      have htime : nativePhysicalCurve P0 (p l) (v l) t 0 = t := by
        change p l 0 + t * v l 0 = t
        rw [hp0, hv0, zero_add, mul_one]
      rw [htime] at hq0
      exact time_window_of_floor_code hcoarse (q 0) hq0
    · change baseMesh⁻¹ • heightScale (baseMesh / hidden)
        (nativePhysicalCurve P0 (p l) (v l) t) ∈ latticeCell (cell (code (l, t)))
      rw [hcell _ hmem]
      exact physCode_mem_latticeCell P0 p v hbase hhidden (l, t)
  · have hlongm : MeasurableSet {x | ENNReal.ofReal (lossRate * coarse) ≤
        incidenceDuration (coarseCellSource P0 p v coarse earlier q) x} :=
      measurableSet_le measurable_const (measurable_incidenceDuration hsrc)
    have hh := retained_duration_prior_bound ν hsrc MeasurableSet.univ hlongm
      (ENNReal.ofReal (lossRate * coarse)) (fun l hl => hl.2)
    rw [Measure.restrict_apply_univ, duration_withDensity_apply ν hsrc MeasurableSet.univ] at hh
    simp only [univ_prod, preimage_univ, inter_univ] at hh
    have hfin := hunitFinite _ hearSub
    have hreal := ENNReal.toReal_mono hfin.ne hh
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_pos hRate hcoarse).le] at hreal
    change (ν.restrict _).real univ ≤ K * (ν.prod volume).real _ / hidden ^ ((2 : ℝ) / 3)
    rw [← hshape, measureReal_def, Measure.restrict_apply_univ]
    have hM : 0 ≤ (ν.prod volume).real (coarseCellSource P0 p v coarse earlier q) :=
      measureReal_nonneg
    rw [le_div_iff₀ hcoarse]
    have hstep : lossRate * coarse * (ν {x | ENNReal.ofReal (lossRate * coarse) ≤
        incidenceDuration (coarseCellSource P0 p v coarse earlier q) x}).toReal ≤
        (ν.prod volume).real (coarseCellSource P0 p v coarse earlier q) := hreal
    have hKr : 1 ≤ K * lossRate := by
      have := mul_le_mul_of_nonneg_right hRateK hRate.le
      rwa [inv_mul_cancel₀ hRate.ne'] at this
    have hν0 : 0 ≤ (ν {x | ENNReal.ofReal (lossRate * coarse) ≤
        incidenceDuration (coarseCellSource P0 p v coarse earlier q) x}).toReal :=
      ENNReal.toReal_nonneg
    nlinarith
  · change (n : ℝ) ≤ K * (hidden ^ ((2 : ℝ) / 3) / baseMesh) ^ 3 *
      (hidden ^ ((2 : ℝ) / 3) / hidden) ^ dimension
    rw [← hshape]
    exact hcount
  · rw [hinc]
    rw [Measure.restrict_apply' hev]
    apply measure_mono_null _ (measure_empty (μ := ν.prod volume))
    intro z hz
    exact (hz.1 (hcurSub hz.2)).elim
  · intro z hz j
    have hh := (hcomp (fun j => v z.1 j.castSucc) (2 * qa z.1 * z.2 + qb z.1) j.castSucc).trans
      (hraw z.1 z.2 hz.2)
    have heq : (liftedVector (fun j => v z.1 j.castSucc) (2 * qa z.1 * z.2 + qb z.1))
        j.castSucc = v z.1 j.castSucc := by
      fin_cases j <;> rfl
    rw [heq] at hh
    exact hh
  · intro z hz
    have hh := (hcomp (fun j => v z.1 j.castSucc) (2 * qa z.1 * z.2 + qb z.1) 3).trans
      (hraw z.1 z.2 hz.2)
    change |2 * qa z.1 * z.2 + qb z.1| ≤ K
    exact hh
  · intro z hz
    exact hraw z.1 z.2 hz.2
  · intro i
    rw [hinc]
    exact hbroad i

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Graph
