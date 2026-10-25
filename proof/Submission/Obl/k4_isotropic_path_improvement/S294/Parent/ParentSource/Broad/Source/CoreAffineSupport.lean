-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CoreAffineSupport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CoreAffineSupport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CoreAffineSupport.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreOscillation
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AffineCoordinates

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Metric Native Analytic
open Submission.Lib.K4AffineCubeSupport
open Submission.Lib.K4AffineMeshCaps
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open k4_stable_native_signal_oscillation
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R qcore : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ ε : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ)
    (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hpure hd hp

/-- The actual raw core and its earlier norming floor produce a finite joint
physical support with the EXACT fine/old affine determinant. -/
theorem CoreEntryData.exists_actual_affine_support
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (b : Fin p.C) (hb : p.lev b = mid)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L) (hB : 0 < d.B k (p.γ b))
    (a : Fin V.count)
    (C : CoreEntryData e R K (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
      (V.entryLaw b a) (packetNativeCubePoint (d.N k) (d.B k) p b) (V.outer b a)
      (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    (i : ↥C.codes × Bool) (hi : (C.kept i).Nonempty)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (old : Fin p.C) (hγ : p.γ b = p.γ old)
    (hwidth : δ (d.N k) (p.r (p.lev b)) ≤ δ (d.N k) (p.r (p.lev old)))
    (hFineOld : p.F b ⊆ p.F old)
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden)
    (hrows : ∀ r : Fin 3, (∑ j : Fin 3, |(packetCubeMatrix p old b)⁻¹ r j| * baseMesh) ≤ 1)
    (hheight :
      2 * (K ^ 14 * (K ^ 6)⁻¹ *
        (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev old)))) +
        ((K ^ (qcore + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
          (K ^ R * (matrixEntrySum (packetCubeMatrix p old b)⁻¹ * baseMesh)) ≤ hidden)
    (U : Set Event) (hUcore : U ⊆ C.raw i) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * baseMesh ^ 3 ≤ 108 * |(packetCubeMatrix p old b).det| ∧
      ∀ z ∈ U, jointCode baseMesh hidden (p.nativeBaseCoordinates old z)
        (packetSignal (d.N k) p old z) ∈ S := by
  have hKpos : 0 < K := by linarith
  have hpoint (z : Event) (hz : z ∈ U) : z ∈ p.F b :=
    ((V.subset b a).2 ((C.subset i).2 (hUcore hz))).2
  have hcube (z : Event) (hz : z ∈ U) :
      p.nativeBaseCoordinates old z ∈ affineCube (packetCubeMatrix p old b) (packetCubeShift p old b) := by
    refine ⟨fun j => nativeBase (packetNativeCubePoint (d.N k) (d.B k) p b z) j, ?_,
      (hp.packet_cube_coordinates old b z).symm⟩
    have hh := (packetNativeCube_source_bounds hp b hB (hpoint z hz)).1
    have heq : (fun j : Fin 3 => nativeBase (packetNativeCubePoint (d.N k) (d.B k) p b z) j) =
        (fun j : Fin 3 => packetNativeCubePoint (d.N k) (d.B k) p b z j.castSucc) := by
      funext j
      fin_cases j <;> rfl
    rwa [heq]
  have hosc (x : Event) (hx : x ∈ U) (y : Event) (hy : y ∈ U)
      (hcode : baseCode baseMesh (p.nativeBaseCoordinates old x) =
        baseCode baseMesh (p.nativeBaseCoordinates old y)) :
      |packetSignal (d.N k) p old x - packetSignal (d.N k) p old y| ≤ 1 * hidden := by
    let Ucell := U ∩ {z | baseCode baseMesh (p.nativeBaseCoordinates old z) =
      baseCode baseMesh (p.nativeBaseCoordinates old x)}
    have hxc : x ∈ Ucell := ⟨hx, rfl⟩
    have hyc : y ∈ Ucell := ⟨hy, hcode.symm⟩
    have hdiam : ∀ z ∈ Ucell, ∀ z' ∈ Ucell,
        ‖packetLocalCorePoint (d.N k) (d.B k) p b K R (C.center i.1.1) z -
          packetLocalCorePoint (d.N k) (d.B k) p b K R (C.center i.1.1) z'‖ ≤
            K ^ R * (matrixEntrySum (packetCubeMatrix p old b)⁻¹ * baseMesh) := by
      intro z hz z' hz'
      exact hp.local_core_diameter_of_same_old_base_cell old b hbase hKpos.le R (C.center i.1.1)
        z z' (hz.2.trans hz'.2.symm)
    have hh := CoreEntryData.actual_core_signal_oscillation V Q hpure hd hp
      hHE hHbase hK hmax hpower hκK b hb hr hrL hB a C i hi hD hjets
      old hγ hwidth hFineOld _ Ucell (fun z hz => hUcore hz.1) hdiam x hxc y hyc
    have hbound := hh.trans hheight
    simpa only [packetSignal, div_eq_mul_inv, one_mul, mul_comm, mul_one] using hbound
  obtain ⟨S, hS, hcover⟩ := affine_cube_joint_cover (p.nativeBaseCoordinates old)
    (packetSignal (d.N k) p old) U (packetCubeMatrix p old b) (packetCubeShift p old b)
    (hp.packet_cube_det_ne_zero old b) hbase hhidden (show (0 : ℝ) ≤ 1 by norm_num)
    hrows hcube hosc
  exact ⟨S, by norm_num at hS ⊢; exact hS, hcover⟩

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
