-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.PacketAffineSupport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/PacketAffineSupport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/PacketAffineSupport.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreSupportUnions
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ValueCoreRetention

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
theorem ValueBranchData.exists_actual_affine_packet_support
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (b : Fin p.C) (hb : p.lev b = mid)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L) (hB : 0 < d.B k (p.γ b))
    (cores : V.CoreFamilies (ENNReal.ofReal ((K ^ qcore)⁻¹)))
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
    : ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * baseMesh ^ 3 ≤ 216 * K ^ (3 * R + 28) * |(packetCubeMatrix p old b).det| ∧
      ∀ v : V.ActiveValue, v.1.1 = b → ∀ z, (∃ i, z ∈ (cores v).kept i) →
        jointCode baseMesh hidden (p.nativeBaseCoordinates old z) (packetSignal (d.N k) p old z) ∈ S := by
  classical
  let I := {v : V.ActiveValue // v.1.1 = b}
  letI : Fintype I := Fintype.ofFinite I
  have hI : Fintype.card I ≤ V.count := by
    have hinj : Function.Injective (fun v : I => v.1.1.2) := by
      intro v w h
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (v.2.trans w.2.symm) h
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj
  have hentry (v : I) : ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * baseMesh ^ 3 ≤
        216 * K ^ (3 * R + 18) * |(packetCubeMatrix p old b).det| ∧
      ∀ z, (∃ i, z ∈ (cores v.1).kept i) → jointCode baseMesh hidden
        (p.nativeBaseCoordinates old z) (packetSignal (d.N k) p old z) ∈ S := by
    have hvb : v.1.1.1 = b := v.2
    have hBv : 0 < d.B k (p.γ v.1.1.1) := by simpa only [hvb] using hB
    have hγv : p.γ v.1.1.1 = p.γ old := by simpa only [hvb] using hγ
    have hwv : δ (d.N k) (p.r (p.lev v.1.1.1)) ≤ δ (d.N k) (p.r (p.lev old)) := by
      simpa only [hvb] using hwidth
    have hFv : p.F v.1.1.1 ⊆ p.F old := by simpa only [hvb] using hFineOld
    obtain ⟨S, hS, hcover⟩ := CoreEntryData.exists_actual_affine_core_support V Q hpure hd hp
      hHE hHbase hK hmax hpower hκK v.1.1.1 v.1.2.1 hr hrL hBv v.1.1.2 (cores v.1)
      hD hjets old hγv hwv hFv hbase hhidden
      (by simpa only [hvb] using hrows) (by simpa only [hvb] using hheight)
    exact ⟨S, by simpa only [hvb] using hS, hcover⟩
  choose F hF hcover using hentry
  let S := Finset.univ.biUnion F
  have hcard : (S.card : ℝ) ≤ ∑ v : I, ((F v).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  have hKpos : 0 < K := by linarith
  refine ⟨S, ?_, ?_⟩
  · calc
      _ ≤ (∑ v : I, ((F v).card : ℝ)) * baseMesh ^ 3 :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ∑ v : I, ((F v).card : ℝ) * baseMesh ^ 3 := Finset.sum_mul _ _ _
      _ ≤ ∑ _v : I, 216 * K ^ (3 * R + 18) * |(packetCubeMatrix p old b).det| :=
        Finset.sum_le_sum (fun v _ => hF v)
      _ = (Fintype.card I : ℝ) * (216 * K ^ (3 * R + 18) * |(packetCubeMatrix p old b).det|) := by
        simp
      _ ≤ (V.count : ℝ) * (216 * K ^ (3 * R + 18) * |(packetCubeMatrix p old b).det|) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hI) (by positivity)
      _ ≤ K ^ 10 * (216 * K ^ (3 * R + 18) * |(packetCubeMatrix p old b).det|) :=
        mul_le_mul_of_nonneg_right V.count_le (by positivity)
      _ = _ := by rw [show 3 * R + 28 = 10 + (3 * R + 18) by omega, pow_add]; ring
  · intro v hv z hz
    let v' : I := ⟨v, hv⟩
    exact Finset.mem_biUnion.mpr ⟨v', Finset.mem_univ _, hcover v' z hz⟩

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
