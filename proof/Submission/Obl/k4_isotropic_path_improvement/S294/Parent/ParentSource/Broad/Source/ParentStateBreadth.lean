-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentStateBreadth, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentStateBreadth.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentStateBreadth.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentDeepMenuSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentSignalCellCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.PhysicalStateBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.LocalReferences

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open MeasureTheory Set Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
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

/-- Actual parent-gradient renewal and original deep histories give
strip breadth on the genuine parent-P states. The source is a literal
original event subset, and each loss is paid once by the full old reference. -/
theorem ValueBranchData.exists_actual_parent_state_breadth
    (hHE : ∀ w, H w⊆d.E k w) (hHbase : ∀ w, H w⊆Q.base w)
    (hHterminal : ∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k^(τ+ε) ≤ K) (hκK : 3*p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K^qcore)⁻¹)))
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    (hHbroad : ∀ w, H w⊆broad.residual w)
    (old : Fin p.C) (hold : p.lev old=i) (hactive : F.active old)
    (hmid : p.lev old ≤ mid) (hstop : mid ≤ stop)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    {Kc gradientWidth θrow : ℝ} {qc : ℕ} (hKc : 2*K^(qcore+7) ≤ Kc)
    (hwidthpos : 0 < gradientWidth) (hwidthfloor : (Kc^qc)⁻¹ ≤ gradientWidth)
    (hstrip : gradientWidth*(6*p.κ^3*d.N k^(2*δ₀*d.L)) ≤ r)
    (hdeep : ∀ fine deep : Fin p.C, p.lev fine=mid → p.lev deep=stop →
      6*K^R*p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ renewalCellMesh Kc J qc)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) (hfraction : 0 ≤ fraction)
    (gradientRef : ENNReal) (hgrad0 : gradientRef≠0) (hgradTop : gradientRef≠∞)
    (hβ1 : gradientRef⁻¹*ENNReal.ofReal (8*fraction)<1)
    {base hidden width : ℝ} (hbase : 0 < base) (hhidden : 0 < hidden)
    (hbaseSmall : ∀ deep : Fin p.C, p.lev deep=stop → p.unshearedDeepRadius old deep ≤ base)
    (hheightSmall : ∀ deep : Fin p.C, p.lev deep=stop →
      let G := coreGradientCoeff (2*K^(qcore+7)) gradientWidth θrow J
      let aOld := δ (d.N k) (p.r (p.lev old))
      let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)
      let Lip := (12*K*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison)*
        (((2:ℝ)^p.T (p.lev old))⁻¹)/aOld
      (2+G/2)*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/aOld))+
        Lip*(6*p.unshearedDeepRadius old deep) ≤ hidden)
    (hcoreSmall : ∀ fine deep : Fin p.C, p.lev fine=mid → p.lev deep=stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ (K^R)⁻¹/12)
    (hwidth : 0 ≤ width) (hwidthScale : width*(6*p.κ^3*d.N k^(2*δ₀*d.L)) ≤ r)
    (stateRef : ENNReal) (hstate0 : stateRef≠0) (hstateTop : stateRef≠∞)
    (source : Set Event) (hsource : MeasurableSet source)
    (hsub : source⊆V.coreRetained cores (p.γ old)∩(broad.residual (p.γ old)∩p.F old)) :
    let raw := (d.ν k (p.γ old)).prod volume
    let reference := d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)
    let gradientCost := ENNReal.ofReal (4*K^(3*R+28)*p.κ^2)*
      (ENNReal.ofReal (θrow*(K^R)⁻¹)+27*(gradientRef*ENNReal.ofReal (p.κ^2)))
    let code := fun z => jointCode base hidden (fun j => unshearedPacketBase p old z j)
      (physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z)
    ∃ kept : Set Event, MeasurableSet kept ∧ kept⊆source ∧
      kept⊆Prod.fst ⁻¹' ParentSignal.goodLines (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) ∧
      raw source ≤ raw kept+(gradientCost+stateRef*(⌈K^12⌉₊:ENNReal)*ENNReal.ofReal (p.κ^2))*reference ∧
      ∀ label (n center : P2), ‖n‖=1 →
        (raw.restrict kept) {z | code z=label ∧
          |Inner.inner ℝ n ((6*p.κ)⁻¹ • p.normalizedVelocity old z-center)| ≤ width} ≤
          (stateRef⁻¹*ENNReal.ofReal (8*fraction))*(raw.restrict kept) (code ⁻¹' {label}) := by
  classical
  obtain ⟨earlier,hearlier,hearlierSub,hearlierGood,hgradient,hmenus⟩ :=
    V.exists_parent_deep_menu_source Q hpure hd hp hHE hHbase hHterminal
      hK hmax hpower hκK cores broad hHbroad old hold hactive hmid hstop hr hrL hD hjets
      hKc hwidthpos hwidthfloor hstrip hdeep hθrow hθrow1 hfraction gradientRef hgrad0 hgradTop hβ1
      source hsource (fun z hz => ⟨(hsub hz).1,(hsub hz).2.2⟩)
  let raw := (d.ν k (p.γ old)).prod (volume : Measure ℝ)
  let μ := raw.restrict earlier
  let code := fun z => jointCode base hidden (fun j => unshearedPacketBase p old z j)
    (physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z)
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
  have hsupport : ∀ᵐ z ∂μ, z∈earlier ∧
      z∈V.coreRetained cores (p.γ old)∩(broad.residual (p.γ old)∩p.F old) :=
    (ae_restrict_mem hearlier).mono (fun z hz => ⟨hz,hsub (hearlierSub hz)⟩)
  let nodes := originalFinePackets p old stop
  let good := nodes.filter (fun deep =>
    F.coding.code deep ∉ Q.intrinsicNarrowStates F.code stop F.U r fraction old ∧
    F.coding.code deep ∉ fineRetentionFailures (Q.coarseLaw (p.lev old) (F.code old))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U old) (ENNReal.ofReal (1/8:ℝ)))
  let I := ↥good
  have hn (j : I) : p.lev j.1=stop ∧ p.γ j.1=p.γ old ∧ p.F j.1⊆p.F old :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp j.2).1).2
  have he (j : I) := (Finset.mem_filter.mp j.2).2.1
  have hret (j : I) := (Finset.mem_filter.mp j.2).2.2
  obtain ⟨rawMenus,hrawCard,hrawCover⟩ :=
    hmenus base hidden hbase hhidden hbaseSmall hheightSmall hcoreSmall
  let menus (j : I) := rawMenus ⟨j.1,(Finset.mem_filter.mp j.2).1⟩
  have hcard (j : I) : (menus j).card ≤ ⌈K^12⌉₊ := by
    exact_mod_cast (hrawCard ⟨j.1,(Finset.mem_filter.mp j.2).1⟩).trans (Nat.le_ceil _)
  have hpacket (deep : Fin p.C) (hdlev : p.lev deep=stop) (hdγ : p.γ deep=p.γ old)
      {z : Event} (hz : z∈F.fineOriginalEvent old deep univ) : z∈p.F deep := by
    have hh := hz.1
    have htag : p.lev deep=stop ∧ p.γ deep=p.γ old := ⟨hdlev,hdγ⟩
    simp only [PathData.packetWitness,ite_eq_left htag] at hh
    exact hh.1.1
  have hcover : ∀ᵐ z ∂μ, ∃ j : I, z∈F.fineOriginalEvent old j.1 univ := by
    filter_upwards [hsupport] with z hz
    obtain ⟨deep,hdlev,hdγ,hdnon,hdret,hzevent⟩ :=
      broad.original_parent_fine_cover old hold z hz.2.2
    have hzbase := hHbase _ (V.residual_subset _ hz.2.1.1)
    have hnode := Q.mem_original_fine_packets hp old deep stop (hmid.trans hstop) hdlev hdγ
      z hzbase hz.2.2.2 (hpacket deep hdlev hdγ hzevent)
    exact ⟨⟨deep,Finset.mem_filter.mpr ⟨hnode,hdnon,hdret⟩⟩,hzevent⟩
  have hmenu : ∀ᵐ z ∂μ, ∀ j : I, z∈F.fineOriginalEvent old j.1 univ → code z∈menus j := by
    filter_upwards [hsupport] with z hz j hzevent
    exact hrawCover ⟨j.1,(Finset.mem_filter.mp j.2).1⟩ z
      ⟨hz.1,hpacket j.1 (hn j).1 (hn j).2.1 hzevent⟩
  obtain ⟨keep,hkeep,hbudget,hcaps⟩ := F.exists_broad_physical_state_source hd hp
    (hp.residual_subset_event H₀ hHterminal) hHterminal old old hactive (fun j : I => j.1)
    (fun j => (hn j).1) (fun j => (hn j).2.1) hfraction hwidth hwidthScale he hret
    μ Measure.restrict_le_self code hcode menus ⌈K^12⌉₊ hcard hcover hmenu stateRef hstate0 hstateTop
  have hN : 0 < d.N k := by linarith [hd.1 k]
  have hsum : (∑ j : I, ENNReal.ofReal (((2:ℝ)^p.T stop)⁻¹)*
      d.ν k (p.γ j.1) (p.A j.1)) ≤ ENNReal.ofReal (p.κ^2)*
        (d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)) := by
    have hh := hp.local_reference_sum_le hN old stop good
      (fun b hb => (Finset.mem_filter.mp (Finset.mem_filter.mp hb).1).2)
    calc
      _ = ∑ j : I, ENNReal.ofReal (((2:ℝ)^p.T stop)⁻¹)*d.ν k (p.γ old) (p.A j.1) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [(hn j).2.1]
      _ = ∑ b∈good, ENNReal.ofReal (((2:ℝ)^p.T stop)⁻¹)*d.ν k (p.γ old) (p.A b) :=
        Finset.sum_coe_sort good (fun b => ENNReal.ofReal (((2:ℝ)^p.T stop)⁻¹)*
          d.ν k (p.γ old) (p.A b))
      _ ≤ _ := hh
  let kept := earlier∩keep
  have hkept : MeasurableSet kept := hearlier.inter hkeep
  have hlaw : μ.restrict keep=raw.restrict kept := by
    rw [Measure.restrict_restrict hkeep,inter_comm]
  refine ⟨kept,hkept,(fun z hz => hearlierSub hz.1),(fun z hz => hearlierGood hz.1),?_,?_⟩
  · have hbudget' := hbudget.trans (add_le_add le_rfl
      (mul_le_mul' le_rfl (mul_le_mul' le_rfl hsum)))
    rw [hlaw,Measure.restrict_apply_univ,Measure.restrict_apply_univ] at hbudget'
    apply hgradient.trans
    apply (add_le_add hbudget' le_rfl).trans
    apply le_of_eq
    ring
  · intro label n center hn
    rw [←hlaw]
    exact hcaps label n center hn

end Prepared
end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
