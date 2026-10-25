-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Velocity.CoarseDuration, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Velocity/CoarseDuration.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Velocity/CoarseDuration.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity.VisitedCells
import Submission.Obl.k4_scalar_graph_residual_discovery.CountedDuration

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity

open Set MeasureTheory SourceGeometry
open Submission.Obl.k4_initial_horizon_bound
open Submission.Obl.k4_scalar_graph_residual_discovery
open scoped ENNReal

noncomputable section

def nativeCoarseCode {X : Type*} (P : MvPolynomial (Fin 4) ℝ)
    (p v : X → Fin 4 → ℝ) (coarse : ℝ) (z : X × ℝ) : Fin 4 → ℤ :=
  fun j => ⌊nativePhysicalCurve P (p z.1) (v z.1) z.2 j / coarse⌋

/-- Prune short line/coarse-cell portions against the full original prior.
Every retained portion has an EARLIER duration witness. Arbitrary subsequent
restrictions may use that same witness and its unchanged-prior cap. -/
theorem exists_native_coarse_duration_source {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [SFinite ν] (P : MvPolynomial (Fin 4) ℝ)
    (hP : P.totalDegree ≤ 2) (p v : X → Fin 4 → ℝ) {K coarse lossRate : ℝ}
    (hK : 0 ≤ K) (hcoarse : 0 < coarse) (hcoarse1 : coarse ≤ 1) (hRate : 0 ≤ lossRate)
    (hv : ∀ x, ∀ j : Fin 3, |v x j.castSucc| ≤ K)
    (hwhole : ∀ x t, t ∈ Icc (0 : ℝ) 1 →
      |MvPolynomial.eval (fun j => p x j + t * v x j) P| ≤ K)
    (hcurve : Measurable (fun z : X × ℝ => nativePhysicalCurve P (p z.1) (v z.1) z.2))
    (E : Set (X × ℝ)) (hE : MeasurableSet E) (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) :
    ∃ keep : Set (X × ℝ), MeasurableSet keep ∧ keep ⊆ E ∧
      (ν.prod volume) (E \ keep) ≤
        ENNReal.ofReal (5 * lossRate * (114 * K + 5) ^ 4) * ν univ ∧
      (∀ z ∈ keep, ENNReal.ofReal (lossRate * coarse) ≤
        incidenceDuration (E ∩ (nativeCoarseCode P p v coarse) ⁻¹'
          {nativeCoarseCode P p v coarse z}) z.1) ∧
      ∀ q : Fin 4 → ℤ,
        ENNReal.ofReal (lossRate * coarse) *
            ν {x | ENNReal.ofReal (lossRate * coarse) ≤
              incidenceDuration (E ∩ (nativeCoarseCode P p v coarse) ⁻¹' {q}) x} ≤
          (ν.prod volume) (E ∩ (nativeCoarseCode P p v coarse) ⁻¹' {q}) := by
  classical
  let code := nativeCoarseCode P p v coarse
  have hcode : Measurable code := by
    apply measurable_pi_iff.mpr
    intro j
    exact Int.measurable_floor.comp
      (((PiLp.continuous_apply 2 _ j).measurable.comp hcurve).div_const coarse)
  let cells (q : Fin 4 → ℤ) := E ∩ code ⁻¹' {q}
  have hcells (q : Fin 4 → ℤ) : MeasurableSet (cells q) :=
    hE.inter (hcode (measurableSet_singleton q))
  choose menus hmenus hcover using fun x =>
    exists_native_curve_cell_menu P hP (p x) (v x) hK hcoarse (hv x) (hwhole x)
  let a := ENNReal.ofReal (lossRate * coarse)
  let D := ENNReal.ofReal ((2 / coarse + 3) * (114 * K + 5) ^ 4)
  have hcount (x : X) : ((menus x).card : ENNReal) ≤ D := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (hmenus x)
  have hsupport (x : X) (q : Fin 4 → ℤ) (hq : incidenceDuration (cells q) x ≠ 0) :
      q ∈ menus x := by
    obtain ⟨t, ht⟩ := nonempty_of_measure_ne_zero hq
    exact (hcover x q).mpr ⟨t, (hunit ht.1).2, ht.2⟩
  let bad := ⋃ q : Fin 4 → ℤ,
    cells q ∩ ({x | incidenceDuration (cells q) x < a} ×ˢ (univ : Set ℝ))
  have hbad : MeasurableSet bad := by
    apply MeasurableSet.iUnion
    intro q
    exact (hcells q).inter ((measurableSet_lt
      (measurable_incidenceDuration (hcells q)) measurable_const).prod MeasurableSet.univ)
  have hraw : (ν.prod volume) bad ≤ a * D * ν univ := by
    simpa only [one_smul, one_mul] using counted_short_incidence_deletion_le ν
      (ν.prod volume) (c := 1) (by simp) hcells menus a D hcount hsupport
  have hnum : (lossRate * coarse) * ((2 / coarse + 3) * (114 * K + 5) ^ 4) ≤
      5 * lossRate * (114 * K + 5) ^ 4 := by
    have hh : coarse * (2 / coarse + 3) ≤ 5 := by
      rw [mul_add, mul_div_cancel₀ _ hcoarse.ne']
      linarith
    calc
      _ = lossRate * (coarse * (2 / coarse + 3)) * (114 * K + 5) ^ 4 := by ring
      _ ≤ lossRate * 5 * (114 * K + 5) ^ 4 := by gcongr
      _ = _ := by ring
  have hbudget : a * D ≤ ENNReal.ofReal (5 * lossRate * (114 * K + 5) ^ 4) := by
    rw [← ENNReal.ofReal_mul (mul_nonneg hRate hcoarse.le)]
    exact ENNReal.ofReal_le_ofReal hnum
  refine ⟨E \ bad, hE.diff hbad, diff_subset, ?_, ?_, ?_⟩
  · apply (measure_mono ?_).trans (hraw.trans (mul_le_mul' hbudget le_rfl))
    intro z hz
    by_contra h
    exact hz.2 ⟨hz.1, h⟩
  · intro z hz
    by_contra hh
    have hshort : incidenceDuration (cells (code z)) z.1 < a := lt_of_not_ge hh
    exact hz.2 (mem_iUnion.mpr ⟨code z, ⟨⟨hz.1, rfl⟩, hshort, mem_univ _⟩⟩)
  · intro q
    let long := {x | a ≤ incidenceDuration (cells q) x}
    have hlong : MeasurableSet long :=
      measurableSet_le measurable_const (measurable_incidenceDuration (hcells q))
    have hh := retained_duration_prior_bound ν (hcells q) MeasurableSet.univ hlong a
      (fun x hx => hx.2)
    rw [Measure.restrict_apply_univ, duration_withDensity_apply ν (hcells q) MeasurableSet.univ] at hh
    simpa only [univ_prod, preimage_univ, inter_univ] using hh

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Velocity
