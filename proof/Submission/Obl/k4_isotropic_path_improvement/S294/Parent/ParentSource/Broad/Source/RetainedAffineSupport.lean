-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.RetainedAffineSupport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/RetainedAffineSupport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/RetainedAffineSupport.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalAffineSupport
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PreparedAncestry

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

/-- This cover applies to the actual retained core source inside an old
packet. Prepared packet uniqueness derives the genuine fine ancestry;
no additional support or retained-source witness is supplied. -/
theorem ValueBranchData.exists_original_core_retained_support
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    (old : Fin p.C) (hmid : p.lev old ≤ mid)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hwidth : δ (d.N k) (p.r mid) ≤ δ (d.N k) (p.r (p.lev old)))
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden)
    (hrows : ∀ b ∈ originalFinePackets p old mid, ∀ r : Fin 3,
      (∑ j : Fin 3, |(packetCubeMatrix p old b)⁻¹ r j| * baseMesh) ≤ 1)
    (hheight : ∀ b ∈ originalFinePackets p old mid,
      2 * (K ^ 14 * (K ^ 6)⁻¹ *
        (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev old)))) +
        ((K ^ (qcore + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
          (K ^ R * (matrixEntrySum (packetCubeMatrix p old b)⁻¹ * baseMesh)) ≤ hidden) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * baseMesh ^ 3 ≤
        7776 * K ^ (3 * R + 28) * p.κ ^ 4 * d.N k ^ (d.f (p.r mid) - d.f (p.r (p.lev old))) ∧
      ∀ z ∈ V.coreRetained cores (p.γ old) ∩ p.F old,
        jointCode baseMesh hidden (p.nativeBaseCoordinates old z) (packetSignal (d.N k) p old z) ∈ S := by
  classical
  let nodes := originalFinePackets p old mid
  have hnodes (b : Fin p.C) (hb : b ∈ nodes) :
      p.lev b = mid ∧ p.γ b = p.γ old ∧ p.F b ⊆ p.F old := (Finset.mem_filter.mp hb).2
  obtain ⟨S, hS, hcover⟩ := V.exists_actual_original_affine_support Q hpure hd hp
    hHE hHbase hK hmax hpower hκK cores old nodes hnodes hr hrL hD hjets
    (fun b hb => by simpa only [(hnodes b hb).1] using hwidth) hbase hhidden hrows hheight
  refine ⟨S, hS, ?_⟩
  intro z hz
  obtain ⟨hzres, hzunion⟩ := hz.1
  obtain ⟨v, hv⟩ := mem_iUnion.mp hzunion
  by_cases hγv : p.γ v.1.1 = p.γ old
  · rw [ite_eq_left hγv] at hv
    obtain ⟨hzinner, hzkept⟩ := hv
    obtain ⟨i, hzi⟩ := mem_iUnion.mp hzkept
    have hzbase : z ∈ Q.base (p.γ old) := hHbase _ (V.residual_subset _ hzres)
    have hzfine : z ∈ p.F v.1.1 := ((V.subset v.1.1 v.1.2).2
      ((V.subset v.1.1 v.1.2).1 hzinner)).2
    have hnode := Q.mem_original_fine_packets hp old v.1.1 mid hmid v.2.1 hγv z hzbase hz.2 hzfine
    exact hcover v hnode z ⟨i, hzi⟩
  · rw [ite_eq_right hγv] at hv
    exact hv.elim

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
