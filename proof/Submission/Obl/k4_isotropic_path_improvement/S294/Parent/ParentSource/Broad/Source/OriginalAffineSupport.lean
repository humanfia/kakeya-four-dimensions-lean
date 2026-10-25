-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.OriginalAffineSupport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/OriginalAffineSupport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/OriginalAffineSupport.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PacketAffineSupport
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AffineReferenceVolumes

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

/-- A concrete joint support for every retained original value/core entry
in a family of finer packets. All packet reference volumes are summed
using the actual original path floors. -/
theorem ValueBranchData.exists_actual_original_affine_support
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    (old : Fin p.C) (nodes : Finset (Fin p.C))
    (hnodes : ∀ b ∈ nodes, p.lev b = mid ∧ p.γ b = p.γ old ∧ p.F b ⊆ p.F old)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hwidth : ∀ b ∈ nodes,
      δ (d.N k) (p.r (p.lev b)) ≤ δ (d.N k) (p.r (p.lev old)))
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden)
    (hrows : ∀ b ∈ nodes, ∀ r : Fin 3,
      (∑ j : Fin 3, |(packetCubeMatrix p old b)⁻¹ r j| * baseMesh) ≤ 1)
    (hheight : ∀ b ∈ nodes,
      2 * (K ^ 14 * (K ^ 6)⁻¹ *
        (δ (d.N k) (p.r (p.lev b)) / δ (d.N k) (p.r (p.lev old)))) +
        ((K ^ (qcore + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
          (K ^ R * (matrixEntrySum (packetCubeMatrix p old b)⁻¹ * baseMesh)) ≤ hidden) :
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * baseMesh ^ 3 ≤
        7776 * K ^ (3 * R + 28) * p.κ ^ 4 * d.N k ^ (d.f (p.r mid) - d.f (p.r (p.lev old))) ∧
      ∀ v : V.ActiveValue, v.1.1 ∈ nodes → ∀ z, (∃ i, z ∈ (cores v).kept i) →
        jointCode baseMesh hidden (p.nativeBaseCoordinates old z) (packetSignal (d.N k) p old z) ∈ S := by
  classical
  obtain ⟨-, -, hν⟩ := hd.weights k
  letI : ∀ w, IsProbabilityMeasure (d.ν k w) := hν
  have hN : 0 < d.N k := (by norm_num : (0 : ℝ) < 2).trans_le (hd.1 k)
  have hKpos : 0 < K := by linarith
  have hBworld : ∀ w, 0 < d.B k w := by
    obtain ⟨_, _, _, _, _, _, _, _, hformat, _⟩ := hd
    obtain ⟨M, D, hformat⟩ := hformat
    intro w
    exact ((hformat k).2.2.2.1 w).2.1
  let I := ↥nodes
  have hn (b : I) := hnodes b.1 b.2
  choose F hF hcover using fun b : I =>
    V.exists_actual_affine_packet_support Q hpure hd hp hHE hHbase hK hmax hpower hκK
      b.1 (hn b).1 hr hrL (hBworld _) cores hD hjets old (hn b).2.1 (hwidth b.1 b.2)
      (hn b).2.2 hbase hhidden (hrows b.1 b.2) (hheight b.1 b.2)
  let S := Finset.univ.biUnion F
  have hcard : (S.card : ℝ) ≤ ∑ b : I, ((F b).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  have hsum : (S.card : ℝ) * baseMesh ^ 3 ≤
      (216 * K ^ (3 * R + 28)) * (∑ b ∈ nodes, |(packetCubeMatrix p old b).det|) := by
    calc
      _ ≤ (∑ b : I, ((F b).card : ℝ)) * baseMesh ^ 3 :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ∑ b : I, ((F b).card : ℝ) * baseMesh ^ 3 := Finset.sum_mul _ _ _
      _ ≤ ∑ b : I, 216 * K ^ (3 * R + 28) * |(packetCubeMatrix p old b.1).det| :=
        Finset.sum_le_sum (fun b _ => hF b)
      _ = _ := by
        rw [← Finset.mul_sum]
        congr 1
        exact Finset.sum_coe_sort nodes (fun b => |(packetCubeMatrix p old b).det|)
  have href := hp.affine_reference_volume_sum_le hN old mid nodes hnodes
  refine ⟨S, ?_, ?_⟩
  · refine hsum.trans ((mul_le_mul_of_nonneg_left href (by positivity)).trans_eq ?_)
    ring
  · intro v hv z hz
    let b : I := ⟨v.1.1, hv⟩
    exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_univ _, hcover b v rfl z hz⟩

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
