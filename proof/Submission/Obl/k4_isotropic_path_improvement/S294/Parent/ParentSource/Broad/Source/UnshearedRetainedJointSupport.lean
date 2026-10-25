-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.UnshearedRetainedJointSupport, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/UnshearedRetainedJointSupport.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 2677a0404c1ed53d6c31d9fee7cfe07a1745d292,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/UnshearedRetainedJointSupport.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedSharpJointSupport
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RetainedAffineSupport
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PhysicalCodePruning

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Matrix Native Analytic
open Submission.Lib.K4AffineCubeSupport
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open k4_stable_native_signal_oscillation
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- Sharp original-core pair estimates give an ACTUAL retained original
joint census. All value/core labels, ancestry, nonempty original
witnesses, frame resolutions and full-reference determinant sums are
constructed internally. The physical signal is arbitrary; only its sharp estimate and its numeric
additive error remain inputs from gradient renewal. -/
theorem ValueBranchData.exists_actual_unsheared_joint_support
    (hHbase : ∀ w, H w ⊆ Q.base w) (hK : 2304 ≤ K)
    {θ : ENNReal} (cores : V.CoreFamilies θ)
    (old : Fin p.C) (hmid : p.lev old ≤ mid)
    (source : Set Event) (hsub : source ⊆ V.coreRetained cores (p.γ old) ∩ p.F old)
    (signal : Ev → ℝ)
    {base hidden additive Lip : ℝ} (hbase : 0 < base) (hhidden : 0 < hidden) (hLip : 0 ≤ Lip)
    (hadditive : additive ≤ hidden/2)
    (hsharp : ∀ (v : V.ActiveValue) (ci : ↥(cores v).codes × Bool),
      p.γ v.1.1=p.γ old →
      ∀ z, z∈source ∩ (V.inner v.1.1 v.1.2 ∩ (cores v).kept ci) →
      ∀ z', z'∈source ∩ (V.inner v.1.1 v.1.2 ∩ (cores v).kept ci) →
        |signal z-signal z'| ≤
          additive+Lip*‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖) :
    let frameBudget := 3*(((1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*
      ((2:ℝ)^p.T mid/(2:ℝ)^p.T (p.lev old)))*
      (1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)))*base
    let C := max 1 (max frameBudget (6*(Lip*base/hidden)))
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ)*base^3 ≤ 62208*C^3*K^(3*R+28)*p.κ^4*d.N k^(2*δ₀*d.L)*
        d.N k^(d.f (p.r mid)-d.f (p.r (p.lev old))) ∧
      ∀ z∈source, jointCode base hidden (fun j => unshearedPacketBase p old z j) (signal z)∈S := by
  classical
  obtain ⟨-, -, hν⟩ := hd.weights k
  have : ∀ w, IsProbabilityMeasure (d.ν k w) := hν
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hKp : 0 < K := by linarith
  let nodes := originalFinePackets p old mid
  have hn (b : ↥nodes) : p.lev b.1=mid ∧ p.γ b.1=p.γ old ∧ p.F b.1 ⊆ p.F old :=
    (Finset.mem_filter.mp b.2).2
  let Val (b : ↥nodes) := {v : V.ActiveValue // v.1.1=b.1}
  letI : ∀ b : ↥nodes, Fintype (Val b) := fun b => Fintype.ofFinite _
  let Entry := Σ b : ↥nodes, Σ v : Val b, ↥(cores v.1).codes × Bool
  let region (j : Entry) := source ∩
    (V.inner j.2.1.1.1.1 j.2.1.1.1.2 ∩ (cores j.2.1.1).kept j.2.2)
  let Live := {j : Entry // (region j).Nonempty}
  letI : Fintype Live := Fintype.ofFinite _
  let fine (j : Live) := j.1.1.1
  have hlev (j : Live) : p.lev (fine j)=mid := (hn j.1.1).1
  have hsource (j : Live) : region j.1 ⊆ p.F (fine j) ∩ p.F old := by
    intro z hz
    have houter := ((cores j.1.2.1.1).subset j.1.2.2).2
      (((cores j.1.2.1.1).subset j.1.2.2).1 hz.2.2)
    have hf := ((V.subset j.1.2.1.1.1.1 j.1.2.1.1.1.2).2 houter).2
    refine ⟨?_,(hsub hz.1).2⟩
    simpa only [fine,j.1.2.1.2] using hf
  have hB (j : Live) : 0 < d.B k (p.γ (fine j)) := by
    obtain ⟨_,_,_,_,_,_,_,_,hformat,_⟩ := hd
    obtain ⟨M,D,hformat⟩ := hformat
    exact ((hformat k).2.2.2.1 _).2.1
  obtain ⟨S,hS,hcover⟩ := hp.unsheared_original_level_joint_support hN old mid fine hlev
    (fun j => region j.1) (fun j => j.2) hsource hB signal hbase hhidden hLip hadditive
    (fun j z hz z' hz' => by
      have hγ : p.γ j.1.2.1.1.1.1=p.γ old := by
        simpa only [j.1.2.1.2] using (hn j.1.1).2.1
      exact hsharp j.1.2.1.1 j.1.2.2 hγ z hz z' hz')
  let det (j : Entry) := |(unshearedPacketCubeMatrix p old j.1.1).det|
  have hLiveFull : (∑ j : Live, det j.1) ≤ ∑ j : Entry, det j := by
    apply Finset.sum_le_sum_of_injOn (fun j : Live => j.1)
    · intro j _ j' _ hh
      exact Subtype.ext hh
    · exact Finset.subset_univ _
    · intro j _
      exact le_rfl
    · intro j _ _
      exact abs_nonneg _
  have hValCard (b : ↥nodes) : Fintype.card (Val b) ≤ V.count := by
    have hinj : Function.Injective (fun v : Val b => v.1.1.2) := by
      intro v w hvw
      apply Subtype.ext
      apply Subtype.ext
      exact Prod.ext (v.2.trans w.2.symm) hvw
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj
  have hAt (b : ↥nodes) :
      (∑ j : Σ v : Val b, ↥(cores v.1).codes × Bool, |(unshearedPacketCubeMatrix p old b.1).det|) ≤
        2*K^(3*R+28)*|(unshearedPacketCubeMatrix p old b.1).det| := by
    rw [Fintype.sum_sigma]
    have hcore (v : Val b) :
        (∑ _ci : ↥(cores v.1).codes × Bool, |(unshearedPacketCubeMatrix p old b.1).det|) ≤
          2*K^(3*R+18)*|(unshearedPacketCubeMatrix p old b.1).det| := by
      calc
        _ = 2*((cores v.1).codes.card:ℝ)*|(unshearedPacketCubeMatrix p old b.1).det| := by
          simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_coe,
            Fintype.card_bool,Nat.cast_mul,Nat.cast_ofNat,nsmul_eq_mul]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (cores v.1).count_le (by norm_num)) (abs_nonneg _)
    calc
      _ ≤ ∑ v : Val b, 2*K^(3*R+18)*|(unshearedPacketCubeMatrix p old b.1).det| :=
        Finset.sum_le_sum (fun v _ => hcore v)
      _ = (Fintype.card (Val b):ℝ)*(2*K^(3*R+18)*|(unshearedPacketCubeMatrix p old b.1).det|) := by simp
      _ ≤ (V.count:ℝ)*(2*K^(3*R+18)*|(unshearedPacketCubeMatrix p old b.1).det|) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hValCard b) (by positivity)
      _ ≤ K^10*(2*K^(3*R+18)*|(unshearedPacketCubeMatrix p old b.1).det|) :=
        mul_le_mul_of_nonneg_right V.count_le (by positivity)
      _ = _ := by rw [show 3*R+28=10+(3*R+18) by omega,pow_add]; ring
  have hFull : (∑ j : Entry, det j) ≤
      2*K^(3*R+28)*(∑ b∈nodes, |(unshearedPacketCubeMatrix p old b).det|) := by
    calc
      _ = ∑ b : ↥nodes, ∑ _j : Σ v : Val b, ↥(cores v.1).codes × Bool,
          |(unshearedPacketCubeMatrix p old b.1).det| := by rw [Fintype.sum_sigma]
      _ ≤ ∑ b : ↥nodes, 2*K^(3*R+28)*|(unshearedPacketCubeMatrix p old b.1).det| :=
        Finset.sum_le_sum (fun b _ => hAt b)
      _ = _ := by
        rw [←Finset.mul_sum]
        exact congrArg (fun x : ℝ => 2*K^(3*R+28)*x)
          (Finset.sum_coe_sort nodes (fun b => |(unshearedPacketCubeMatrix p old b).det|))
  have href := hp.unsheared_affine_reference_volume_sum_le hN old mid nodes
    (fun b hb => (Finset.mem_filter.mp hb).2)
  let frameBudget := 3*(((1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*
      ((2:ℝ)^p.T mid/(2:ℝ)^p.T (p.lev old)))*
      (1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)))*base
  let C := max 1 (max frameBudget (6*(Lip*base/hidden)))
  have hC : 0 ≤ C := (by norm_num : (0:ℝ) ≤ 1).trans (le_max_left _ _)
  refine ⟨S,?_,?_⟩
  · calc
      _ ≤ 864*C^3*(∑ j : Live, det j.1) := hS
      _ ≤ 864*C^3*(2*K^(3*R+28)*(∑ b∈nodes, |(unshearedPacketCubeMatrix p old b).det|)) :=
        mul_le_mul_of_nonneg_left (hLiveFull.trans hFull) (by positivity)
      _ ≤ 864*C^3*(2*K^(3*R+28)*(d.N k^(2*δ₀*d.L)*(36*p.κ^4*d.N k^(d.f (p.r mid)-d.f (p.r (p.lev old)))))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left href (by positivity)) (by positivity)
      _ = _ := by ring
  · intro z hz
    have hzall := hsub hz
    obtain ⟨v,hv⟩ := mem_iUnion.mp hzall.1.2
    by_cases hγ : p.γ v.1.1=p.γ old
    · rw [ite_eq_left hγ] at hv
      obtain ⟨hzinner,hzcore⟩ := hv
      obtain ⟨ci,hci⟩ := mem_iUnion.mp hzcore
      have hzbase := hHbase _ (V.residual_subset _ hzall.1.1)
      have hzfine := ((V.subset v.1.1 v.1.2).2 ((V.subset v.1.1 v.1.2).1 hzinner)).2
      have hnode := Q.mem_original_fine_packets hp old v.1.1 mid hmid v.2.1 hγ
        z hzbase hzall.2 hzfine
      let b : ↥nodes := ⟨v.1.1,hnode⟩
      let vb : Val b := ⟨v,rfl⟩
      let entry : Entry := ⟨b,vb,ci⟩
      have hzr : z∈region entry := ⟨hz,hzinner,hci⟩
      let live : Live := ⟨entry,⟨z,hzr⟩⟩
      have hh := hcover live z hzr
      exact hh
    · rw [ite_eq_right hγ] at hv
      exact hv.elim


/-- At the physical parent joint mesh condition, the entire actual
value/core census retains its original profile factor and pays no
inverse a/h signal slope. -/
theorem ValueBranchData.exists_actual_unsheared_physical_joint_support
    (hHbase : ∀ w, H w⊆Q.base w) (hK : 2304 ≤ K)
    {θ : ENNReal} (cores : V.CoreFamilies θ)
    (old : Fin p.C) (hmid : p.lev old ≤ mid)
    (source : Set Event) (hsub : source⊆V.coreRetained cores (p.γ old)∩p.F old)
    (signal : Ev → ℝ) {a base hidden additive Lip G : ℝ}
    (ha : 0 < a) (hbase : 0 < base) (hhidden : 0 < hidden) (hLip : 0 ≤ Lip)
    (hphysicalLip : Lip ≤ G*(((2:ℝ)^p.T (p.lev old))⁻¹)/a)
    (hmesh : 6*G*(((2:ℝ)^p.T (p.lev old))⁻¹)*base ≤ a*hidden)
    (hadditive : additive ≤ hidden/2)
    (hsharp : ∀ (v : V.ActiveValue) (ci : ↥(cores v).codes × Bool),
      p.γ v.1.1=p.γ old →
      ∀ z, z∈source∩(V.inner v.1.1 v.1.2∩(cores v).kept ci) →
      ∀ z', z'∈source∩(V.inner v.1.1 v.1.2∩(cores v).kept ci) →
        |signal z-signal z'| ≤ additive+Lip*
          ‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖) :
    let frameBudget := 3*(((1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*
      ((2:ℝ)^p.T mid/(2:ℝ)^p.T (p.lev old)))*
      (1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)))*base
    ∃ S : Finset (Fin 4 → ℤ),
      (S.card : ℝ)*base^3 ≤ 62208*(max 1 frameBudget)^3*K^(3*R+28)*p.κ^4*
        d.N k^(2*δ₀*d.L)*d.N k^(d.f (p.r mid)-d.f (p.r (p.lev old))) ∧
      ∀ z∈source, jointCode base hidden
        (fun j => unshearedPacketBase p old z j) (signal z)∈S := by
  have hslope := physical_parent_joint_slope_budget ha hbase.le hhidden hphysicalLip hmesh
  have heq (frameBudget : ℝ) :
      max 1 (max frameBudget (6*(Lip*base/hidden)))=max 1 frameBudget := by
    rw [←max_assoc,max_eq_left (hslope.trans (le_max_left _ _))]
  simpa only [heq] using V.exists_actual_unsheared_joint_support Q hd hp hHbase hK
    cores old hmid source hsub signal hbase hhidden hLip hadditive hsharp

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
