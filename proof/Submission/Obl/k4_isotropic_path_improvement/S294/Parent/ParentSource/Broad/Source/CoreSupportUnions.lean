-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.CoreSupportUnions, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/CoreSupportUnions.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/CoreSupportUnions.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.CoreAffineSupport

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
theorem CoreEntryData.exists_actual_affine_core_support
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (b : Fin p.C) (hb : p.lev b = mid)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L) (hB : 0 < d.B k (p.γ b))
    (a : Fin V.count)
    (C : CoreEntryData e R K (packetNativeValueTest (d.N k) (d.B k) p b (V.center a))
      (V.entryLaw b a) (packetNativeCubePoint (d.N k) (d.B k) p b) (V.outer b a)
      (ENNReal.ofReal ((K ^ qcore)⁻¹)))
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
      (S.card : ℝ) * baseMesh ^ 3 ≤ 216 * K ^ (3 * R + 18) * |(packetCubeMatrix p old b).det| ∧
      ∀ z, (∃ i, z ∈ C.kept i) → jointCode baseMesh hidden (p.nativeBaseCoordinates old z)
        (packetSignal (d.N k) p old z) ∈ S := by
  classical
  have hentry (i : ↥C.codes × Bool) : ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ) * baseMesh ^ 3 ≤ 108 * |(packetCubeMatrix p old b).det| ∧
      ∀ z ∈ C.kept i, jointCode baseMesh hidden (p.nativeBaseCoordinates old z)
        (packetSignal (d.N k) p old z) ∈ S := by
    by_cases hi : (C.kept i).Nonempty
    · exact CoreEntryData.exists_actual_affine_support V Q hpure hd hp
        hHE hHbase hK hmax hpower hκK b hb hr hrL hB a C i hi hD hjets
        old hγ hwidth hFineOld hbase hhidden hrows hheight (C.kept i) (C.subset i).1
    · refine ⟨∅, by simp, ?_⟩
      intro z hz
      exact (hi ⟨z, hz⟩).elim
  choose F hF hcover using hentry
  let S := Finset.univ.biUnion F
  have hcard : (S.card : ℝ) ≤ ∑ i : ↥C.codes × Bool, ((F i).card : ℝ) := by
    exact_mod_cast Finset.card_biUnion_le
  refine ⟨S, ?_, ?_⟩
  · calc
      _ ≤ (∑ i : ↥C.codes × Bool, ((F i).card : ℝ)) * baseMesh ^ 3 :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ∑ i : ↥C.codes × Bool, ((F i).card : ℝ) * baseMesh ^ 3 := Finset.sum_mul _ _ _
      _ ≤ ∑ _i : ↥C.codes × Bool, 108 * |(packetCubeMatrix p old b).det| :=
        Finset.sum_le_sum (fun i _ => hF i)
      _ = 216 * (C.codes.card : ℝ) * |(packetCubeMatrix p old b).det| := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
          Fintype.card_coe, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left C.count_le (by norm_num)) (abs_nonneg _)
  · intro z hz
    obtain ⟨i, hi⟩ := hz
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hcover i z hi⟩

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
