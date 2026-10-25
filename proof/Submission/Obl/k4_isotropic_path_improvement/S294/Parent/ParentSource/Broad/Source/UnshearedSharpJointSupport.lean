-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.UnshearedSharpJointSupport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/UnshearedSharpJointSupport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/UnshearedSharpJointSupport.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedFrameResolution

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open MeasureTheory Set Native Matrix
open k4_stable_native_signal_oscillation
open Submission.Lib.K4AffineCubeSupport
open Submission.Lib.K4AffineMeshCaps
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
noncomputable section

section Path
variable {W : ℕ} {p : PathData W} {N L : ℝ} {ω : Fin W → ℝ}
    {ν : Fin W → Measure Ln} {E : Fin W → Set Ev} {B : Fin W → ℝ}
    {f : ℝ → ℝ} {κ₁ : ℝ} {m : ℕ} {s : ℕ → ℝ} {δ₀ : ℝ}
    {Mp Dp : ℕ} {σ : ℝ}
    (hp : p.Valid N L ω ν E B f κ₁ m s δ₀ Mp Dp σ)
include hp

/-- Actual fine packets and a physical signal pair estimate yield a
joint census in the literal unsheared old coordinates. All affine
occupancy and inverse-frame resolution data are produced from the path. -/
theorem Native.PathData.Valid.unsheared_original_level_joint_support
    (hN : 1 ≤ N) (old : Fin p.C) (mid : ℕ)
    {I : Type*} [Fintype I] (fine : I → Fin p.C) (hlev : ∀ i, p.lev (fine i)=mid)
    (regions : I → Set Ev) (hne : ∀ i, (regions i).Nonempty)
    (hsource : ∀ i, regions i⊆p.F (fine i)∩p.F old)
    (hB : ∀ i, 0 < B (p.γ (fine i))) (signal : Ev → ℝ)
    {base hidden additive Lip : ℝ} (hbase : 0 < base) (hhidden : 0 < hidden)
    (hLip : 0 ≤ Lip) (hadditive : additive ≤ hidden/2)
    (hpair : ∀ i z, z∈regions i → ∀ z', z'∈regions i →
      |signal z-signal z'| ≤ additive+Lip*
        ‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖) :
    let frameBudget := 3*(((1+4*p.κ+6*p.κ^3*N^(2*δ₀*L))*
      ((2:ℝ)^p.T mid/(2:ℝ)^p.T (p.lev old)))*
      (1+2*(p.κ*N^(2*δ₀*L))*(1+‖p.u old‖)))*base
    let C := max 1 (max frameBudget (6*(Lip*base/hidden)))
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ)*base^3 ≤ 864*C^3*(∑ i, |(unshearedPacketCubeMatrix p old (fine i)).det|) ∧
      ∀ i z, z∈regions i →
        jointCode base hidden (fun j => unshearedPacketBase p old z j) (signal z)∈S := by
  classical
  dsimp only
  let matrices := fun i => unshearedPacketCubeMatrix p old (fine i)
  let frameBudget := 3*(((1+4*p.κ+6*p.κ^3*N^(2*δ₀*L))*
    ((2:ℝ)^p.T mid/(2:ℝ)^p.T (p.lev old)))*
    (1+2*(p.κ*N^(2*δ₀*L))*(1+‖p.u old‖)))*base
  have hframe (i : I) (r : Fin 3) :
      (∑ j : Fin 3, |(matrices i)⁻¹ r j|)*base ≤ frameBudget := by
    obtain ⟨z,hz⟩ := hne i
    have hf := (path_packet_support hp (fine i) ((hsource i hz).1)).2.1
    have ho := (path_packet_support hp old ((hsource i hz).2)).2.1
    have hh := hp.unsheared_packet_cube_inverse_rows_bound hN old (fine i) hf ho hbase.le r
    simpa only [matrices,frameBudget,Finset.sum_mul,hlev i] using hh
  have hpoint (i : I) (z : Ev) (hz : z∈regions i) :
      (fun j => unshearedPacketBase p old z j)∈affineCube (matrices i)
        (unshearedPacketCubeShift p old (fine i)) := by
    refine ⟨fun j => nativeBase (packetNativeCubePoint N B p (fine i) z) j,?_,?_⟩
    · have hh := (packetNativeCube_source_bounds hp (fine i) (hB i) ((hsource i hz).1)).1
      have heq : (fun j : Fin 3 => nativeBase (packetNativeCubePoint N B p (fine i) z) j)=
          fun j : Fin 3 => packetNativeCubePoint N B p (fine i) z j.castSucc := by
        ext j
        fin_cases j <;> rfl
      rwa [heq]
    · exact (hp.unsheared_packet_cube_coordinates old (fine i) z).symm
  exact joint_support_from_sharp_affine_family (unshearedPacketBase p old) signal regions
    matrices (fun i => unshearedPacketCubeShift p old (fine i))
    (fun i => hp.unsheared_packet_cube_det_ne_zero old (fine i))
    hbase hhidden hLip hadditive hframe hpoint hpair

/-- At the physical parent mesh condition the true h/a signal slope
cancels; only the actual affine budget appears in the count. -/
theorem Native.PathData.Valid.unsheared_physical_parent_level_joint_support
    (hN : 1 ≤ N) (old : Fin p.C) (mid : ℕ)
    {I : Type*} [Fintype I] (fine : I → Fin p.C) (hlev : ∀ i, p.lev (fine i)=mid)
    (regions : I → Set Ev) (hne : ∀ i, (regions i).Nonempty)
    (hsource : ∀ i, regions i⊆p.F (fine i)∩p.F old)
    (hB : ∀ i, 0 < B (p.γ (fine i))) (signal : Ev → ℝ)
    {a base hidden additive Lip G : ℝ} (ha : 0 < a) (hbase : 0 < base) (hhidden : 0 < hidden)
    (hLip : 0 ≤ Lip) (hphysicalLip : Lip ≤ G*(((2:ℝ)^p.T (p.lev old))⁻¹)/a)
    (hmesh : 6*G*(((2:ℝ)^p.T (p.lev old))⁻¹)*base ≤ a*hidden)
    (hadditive : additive ≤ hidden/2)
    (hpair : ∀ i z, z∈regions i → ∀ z', z'∈regions i →
      |signal z-signal z'| ≤ additive+Lip*
        ‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖) :
    let frameBudget := 3*(((1+4*p.κ+6*p.κ^3*N^(2*δ₀*L))*
      ((2:ℝ)^p.T mid/(2:ℝ)^p.T (p.lev old)))*
      (1+2*(p.κ*N^(2*δ₀*L))*(1+‖p.u old‖)))*base
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ)*base^3 ≤ 864*(max 1 frameBudget)^3*
        (∑ i, |(unshearedPacketCubeMatrix p old (fine i)).det|) ∧
      ∀ i z, z∈regions i →
        jointCode base hidden (fun j => unshearedPacketBase p old z j) (signal z)∈S := by
  have hslope := physical_parent_joint_slope_budget ha hbase.le hhidden hphysicalLip hmesh
  have heq (frameBudget : ℝ) :
      max 1 (max frameBudget (6*(Lip*base/hidden)))=max 1 frameBudget := by
    rw [←max_assoc,max_eq_left (hslope.trans (le_max_left _ _))]
  simpa only [heq] using hp.unsheared_original_level_joint_support hN old mid fine hlev
    regions hne hsource hB signal hbase hhidden hLip hadditive hpair

end Path
end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
