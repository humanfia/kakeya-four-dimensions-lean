-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ShallowParentStateBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ShallowParentStateBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ShallowParentStateBreadth.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.VaryingParentStateBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalDeepBroadState
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.OriginalUnshearedSignalMenus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PhysicalParentCorePairs
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.LocalReferences
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentSignalCellCaps

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Metric Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open scoped ENNReal BigOperators

noncomputable section

/-- Actual sharp physical parent pairs produce whole-deep menus, then
quarter breadth is renewed in an ARBITRARY shallow target frame. Every
deep packet uses its own active quarter parent, and only unchanged full
deep references enter the deletion budget. No second gradient cut occurs. -/
theorem ValueBranchData.exists_shallow_parent_state_breadth_of_core_gradients
    {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {H H₀ : Fin (d.W k) → Set Event} {mid m : ℕ} {K : ℝ} {q e R qcore : ℕ}
    (V : ValueBranchData d k p H mid K q e R)
    {u : T → ℝ} {τ : ℝ} (Q : PreparedAngularPath d k p m H₀ u τ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w⊆d.E k w) (hHbase : ∀ w, H w⊆Q.base w)
    (hHterminal : ∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K) (hκK : 3*p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K^qcore)⁻¹)))
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction) (hio : i ≤ stop)
    (old : Fin p.C) (hmid : p.lev old ≤ mid) (hstop : mid ≤ stop) (hr : 0 ≤ p.r mid)
    {G : ℝ} (hG : 0 ≤ G) {base hidden width : ℝ}
    (hbase : 0 < base) (hhidden : 0 < hidden)
    (hbaseSmall : ∀ deep : Fin p.C, p.lev deep=stop → p.unshearedDeepRadius old deep ≤ base)
    (hheightSmall : ∀ deep : Fin p.C, p.lev deep=stop →
      let aOld := δ (d.N k) (p.r (p.lev old))
      let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)
      let Lip := (12*K*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison)*
        (((2:ℝ)^p.T (p.lev old))⁻¹)/aOld
      (2+G/2)*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/aOld))+
        Lip*(6*p.unshearedDeepRadius old deep) ≤ hidden)
    (hcoreSmall : ∀ fine deep : Fin p.C, p.lev fine=mid → p.lev deep=stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ (K^R)⁻¹/12)
    (hfraction : 0 ≤ fraction) (hwidth : 0 ≤ width)
    (hwidthScale : width*(6*p.κ^3*d.N k^(2*δ₀*d.L)) ≤ r)
    (stateRef : ENNReal) (hstate0 : stateRef≠0) (hstateTop : stateRef≠∞)
    (source : Set Event) (hsource : MeasurableSet source)
    (hsub : source⊆V.coreRetained cores (p.γ old)∩(broad.residual (p.γ old)∩p.F old))
    (hgood : source⊆Prod.fst ⁻¹' ParentSignal.goodLines
      (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)))
    (hgrad : ∀ (v : V.ActiveValue) (ci : ↥(cores v).codes × Bool),
      p.γ v.1.1=p.γ old →
      (source∩(V.inner v.1.1 v.1.2∩(cores v).kept ci)).Nonempty →
      ∀ x∈closedBall (0 : Base) 2,
        ‖fderiv ℝ (parentCorePrediction (d.N k) (d.B k) p v.1.1 (d.P k (p.γ v.1.1)) K R
          ((cores v).center ci.1.1) ((cores v).sheet ci)) x‖ ≤
          G*(K^14*(K^6)⁻¹*δ (d.N k) (p.r mid)+12*K*coreRowStep p v.1.1 K R)) :
    let raw := (d.ν k (p.γ old)).prod volume
    let reference := d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)
    let code := fun z => jointCode base hidden (fun j => unshearedPacketBase p old z j)
      (physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z)
    ∃ kept : Set Event, MeasurableSet kept ∧ kept⊆source ∧
      raw source ≤ raw kept+(stateRef*(⌈K^12⌉₊:ENNReal)*ENNReal.ofReal (p.κ^2))*reference ∧
      ∀ label (n center : P2), ‖n‖=1 →
        (raw.restrict kept) {z | code z=label ∧
          |Inner.inner ℝ n ((6*p.κ)⁻¹ • p.normalizedVelocity old z-center)| ≤ width} ≤
          (stateRef⁻¹*ENNReal.ofReal (8*fraction))*(raw.restrict kept) (code ⁻¹' {label}) := by
  classical
  intro raw reference code
  let μ := raw.restrict source
  let aOld := δ (d.N k) (p.r (p.lev old))
  let additive := (2+G/2)*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/aOld))
  let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)
  let Lip := (12*K*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison)*
    (((2:ℝ)^p.T (p.lev old))⁻¹)/aOld
  have hKp : 0 < K := by linarith
  have hNp : 0 < d.N k := by linarith [hd.1 k]
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hLip : 0 ≤ Lip := by dsimp [Lip,aOld,comparison,δ]; positivity
  have hpair := V.physical_parent_pairs_of_core_gradients hd hp hHE hK hmax hκK cores hr old source
    (fun z hz => (hsub hz).2.2) hgood hG hgrad
  obtain ⟨rawMenus,hrawCard,hrawCover⟩ := V.exists_original_unsheared_signal_deep_menus Q hd hp
    hHbase hK cores old stop hstop source (fun z hz => (hsub hz).1)
    (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) hLip hbase hhidden
    hbaseSmall hheightSmall hcoreSmall hpair
  have hcode : Measurable code := by
    have heq : code=fun z => fun j =>
        ⌊parentUnshearedCoordinates (d.N k) p old (d.P k (p.γ old)) z j/
          (if j=3 then hidden else base)⌋ := by
      funext z j
      fin_cases j <;> rfl
    rw [heq]
    apply measurable_pi_iff.mpr
    intro j
    exact Int.measurable_floor.comp (((measurable_pi_apply j).comp
      (measurable_parentUnshearedCoordinates _ _ _ _)).div_const _)
  let nodes := originalFinePackets p old stop
  let good := nodes.filter (fun deep => (source∩p.F deep).Nonempty)
  let I := ↥good
  have hn (j : I) : p.lev j.1=stop ∧ p.γ j.1=p.γ old ∧ p.F j.1⊆p.F old :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp j.2).1).2
  let sourceGlob := fun v : Fin (d.W k) => if v=p.γ old then source else ∅
  have hglob (v) : sourceGlob v⊆broad.residual v := by
    by_cases hv : v=p.γ old
    · subst v
      exact fun z hz => (hsub (by simpa only [sourceGlob,ite_true] using hz)).2.1
    · simp only [sourceGlob,ite_eq_right hv,empty_subset]
  have hparent (j : I) := broad.exists_original_deep_broad_state_on_source hp hio sourceGlob hglob j.1 (hn j).1
    (by simpa only [sourceGlob,(hn j).2.1,ite_true] using (Finset.mem_filter.mp j.2).2)
  choose parent hparentLev hparentγ hparentActive hparentBroad hparentRet hparentCover using hparent
  let menus (j : I) := rawMenus ⟨j.1,(Finset.mem_filter.mp j.2).1⟩
  have hcard (j : I) : (menus j).card ≤ ⌈K^12⌉₊ := by
    exact_mod_cast (hrawCard ⟨j.1,(Finset.mem_filter.mp j.2).1⟩).trans (Nat.le_ceil _)
  have hpacket (b deep : Fin p.C) (hlev : p.lev deep=stop) (hγ : p.γ deep=p.γ b)
      {z : Event} (hz : z∈F.fineOriginalEvent b deep univ) : z∈p.F deep := by
    have hh := hz.1
    simp only [PathData.packetWitness,ite_eq_left (show p.lev deep=stop ∧ p.γ deep=p.γ b from ⟨hlev,hγ⟩)] at hh
    exact hh.1.1
  have hcover : ∀ᵐ z ∂μ, ∃ j : I, z∈F.fineOriginalEvent (parent j) j.1 univ := by
    filter_upwards [ae_restrict_mem hsource] with z hz
    obtain ⟨b,hbi,hbw,hzb,_,_⟩ := broad.witness _ z (hsub hz).2.1
    obtain ⟨deep,hdlev,hdγ,_,_,hzevent⟩ := broad.original_parent_fine_cover b hbi z
      (by rw [hbw]; exact ⟨(hsub hz).2.1,hzb⟩)
    have hzdeep := hpacket b deep hdlev hdγ hzevent
    have hzbase := hHbase _ (V.residual_subset _ (hsub hz).1.1)
    have hnode := Q.mem_original_fine_packets hp old deep stop (hmid.trans hstop) hdlev
      (hdγ.trans hbw) z hzbase (hsub hz).2.2 hzdeep
    let jj : I := ⟨deep,Finset.mem_filter.mpr ⟨hnode,⟨z,hz,hzdeep⟩⟩⟩
    refine ⟨jj,hparentCover jj z ?_⟩
    exact ⟨by simpa only [sourceGlob,(hn jj).2.1,ite_true] using hz,hzdeep⟩
  have hmenu : ∀ᵐ z ∂μ, ∀ j : I, z∈F.fineOriginalEvent (parent j) j.1 univ → code z∈menus j := by
    filter_upwards [ae_restrict_mem hsource] with z hz j hzevent
    exact hrawCover ⟨j.1,(Finset.mem_filter.mp j.2).1⟩ z
      ⟨hz,hpacket (parent j) j.1 (hn j).1 (hparentγ j).symm hzevent⟩
  obtain ⟨keep,hkeep,hbudget,hcaps⟩ := F.exists_broad_physical_state_source_varying_parent hd hp
    (hp.residual_subset_event H₀ hHterminal) hHterminal (p.γ old) old parent (fun j : I => j.1)
    hparentActive (fun j => (hparentγ j).trans (hn j).2.1) (fun j => (hn j).1)
    (fun j => (hparentγ j).symm) hfraction hwidth hwidthScale hparentBroad hparentRet
    μ Measure.restrict_le_self code hcode menus ⌈K^12⌉₊ hcard hcover hmenu stateRef hstate0 hstateTop
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hsum : (∑ j : I, ENNReal.ofReal (((2:ℝ)^p.T stop)⁻¹)*
      d.ν k (p.γ j.1) (p.A j.1)) ≤ ENNReal.ofReal (p.κ^2)*reference := by
    have hh := hp.local_reference_sum_le hN old stop good
      (fun b hb => (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2)
    calc
      _ = ∑ j : I, ENNReal.ofReal (((2:ℝ)^p.T stop)⁻¹)*d.ν k (p.γ old) (p.A j.1) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [(hn j).2.1]
      _ = ∑ b∈good, ENNReal.ofReal (((2:ℝ)^p.T stop)⁻¹)*d.ν k (p.γ old) (p.A b) :=
        Finset.sum_coe_sort good (fun b => ENNReal.ofReal (((2:ℝ)^p.T stop)⁻¹)*d.ν k (p.γ old) (p.A b))
      _ ≤ _ := hh
  let kept := source∩keep
  have hkept : MeasurableSet kept := hsource.inter hkeep
  have hlaw : μ.restrict keep=raw.restrict kept := by
    rw [Measure.restrict_restrict hkeep,inter_comm]
  refine ⟨kept,hkept,inter_subset_left,?_,?_⟩
  · have hbudget' := hbudget.trans (add_le_add le_rfl
      (mul_le_mul' le_rfl (mul_le_mul' le_rfl hsum)))
    rw [hlaw,Measure.restrict_apply_univ,Measure.restrict_apply_univ] at hbudget'
    simpa only [mul_assoc] using hbudget'
  · intro label n center hnormal
    rw [←hlaw]
    exact hcaps label n center hnormal

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
