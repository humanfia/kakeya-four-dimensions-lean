-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentSharpOriginalSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentSharpOriginalSource.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x1046 (branch x0943), commit 1fcc75a78b90aa1b479052c83612b68563af73b6,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentSharpOriginalSource.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.OriginalParentSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedRetainedJointSupport
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentMovingBandCap

set_option autoImplicit false
set_option maxRecDepth 32768

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

/-- Renew the actual global parent gradient and export the pair estimates
on each retained original value/core entry. The same estimates may be
used for geometric counts and later whole-packet menus. -/
theorem ValueBranchData.exists_parent_sharp_pair_original_source
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hHterminal : ∀ w, H₀ w ⊆ {z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k^(τ+ε) ≤ K) (hκK : 3*p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K^qcore)⁻¹)))
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    (hHbroad : ∀ w, H w ⊆ broad.residual w)
    (old : Fin p.C) (hold : p.lev old=i) (hactive : F.active old)
    (hmid : p.lev old ≤ mid) (hstop : mid ≤ stop)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    {Kc width θrow : ℝ} {qc : ℕ} (hKc : 2*K^(qcore+7) ≤ Kc)
    (hwidthpos : 0 < width) (hwidthfloor : (Kc^qc)⁻¹ ≤ width)
    (hstrip : width*(6*p.κ^3*d.N k^(2*δ₀*d.L)) ≤ r)
    (hdeep : ∀ fine deep : Fin p.C, p.lev fine=mid → p.lev deep=stop →
      6*K^R*p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ renewalCellMesh Kc J qc)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) (hfraction : 0 ≤ fraction)
    (δref : ENNReal) (hδ0 : δref ≠ 0) (hδtop : δref ≠ ∞)
    (hβ1 : δref⁻¹*ENNReal.ofReal (8*fraction) < 1)
    (source : Set Event) (hsource : MeasurableSet source)
    (hsub : source ⊆ V.coreRetained cores (p.γ old) ∩ p.F old)
 :
    let G := coreGradientCoeff (2*K^(qcore+7)) width θrow J
    let oldWidth := δ (d.N k) (p.r (p.lev old))
    let additive := (2+G/2)*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/oldWidth))
    let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)
    let slope := 12*K*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison
    ∃ current : Set Event, MeasurableSet current ∧ current⊆source ∧
      current⊆Prod.fst ⁻¹' ParentSignal.goodLines
        (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) ∧
      ((d.ν k (p.γ old)).prod volume) source ≤
        ((d.ν k (p.γ old)).prod volume) current+
          ENNReal.ofReal (4*K^(3*R+28)*p.κ^2)*
            (ENNReal.ofReal (θrow*(K^R)⁻¹)+27*(δref*ENNReal.ofReal (p.κ^2)))*
            (d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)) ∧
      ∀ (v : V.ActiveValue) (ci : ↥(cores v).codes × Bool),
        p.γ v.1.1=p.γ old →
        ∀ z∈current∩(V.inner v.1.1 v.1.2∩(cores v).kept ci),
        ∀ z'∈current∩(V.inner v.1.1 v.1.2∩(cores v).kept ci),
          |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-
            physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z'| ≤
              additive+(slope*(((2:ℝ)^p.T (p.lev old))⁻¹)/oldWidth)*
                ‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖ := by
  let raw : Measure Event := (d.ν k (p.γ old)).prod volume
  let μ := raw.restrict source
  have hs : ∀ᵐ z ∂μ, z∈V.coreRetained cores (p.γ old)∩p.F old :=
    (ae_restrict_mem hsource).mono (fun z hz => hsub hz)
  obtain ⟨keep,hkeep,hkeepGood,hloss,hgood⟩ := V.exists_original_parent_gradient_core_source
    Q hpure hd hp hHE hHbase hHterminal hK hmax hpower hκK cores broad hHbroad old hold hactive
    hmid hstop hr hrL hD hjets hKc hwidthpos hwidthfloor hstrip hdeep
    hθrow hθrow1 hfraction δref hδ0 hδtop hβ1 μ Measure.restrict_le_self hs
  let current := source∩keep
  have hcurrent : MeasurableSet current := hsource.inter hkeep
  have hcurrentSub : current⊆V.coreRetained cores (p.γ old)∩p.F old := fun z hz => hsub hz.1
  let G := coreGradientCoeff (2*K^(qcore+7)) width θrow J
  let oldWidth := δ (d.N k) (p.r (p.lev old))
  let additive := (2+G/2)*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/oldWidth))
  let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)
  let slope := 12*K*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison
  let Lip := slope*(((2:ℝ)^p.T (p.lev old))⁻¹)/oldWidth
  have hKp : 0 < K := by linarith
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have ha : 0 < oldWidth := by dsimp [oldWidth,δ]; positivity
  have hG : 0 ≤ G := by
    dsimp [G,coreGradientCoeff]
    have hK0 := coreRow_spec.1
    positivity
  have hLip : 0 ≤ Lip := by dsimp [Lip,slope,comparison]; positivity
  have hsharp (v : V.ActiveValue) (ci : ↥(cores v).codes × Bool)
      (hγ : p.γ v.1.1=p.γ old) (z : Event)
      (hz : z∈current∩(V.inner v.1.1 v.1.2∩(cores v).kept ci))
      (z' : Event) (hz' : z'∈current∩(V.inner v.1.1 v.1.2∩(cores v).kept ci)) :
      |physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z-
          physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z'| ≤
        additive+Lip*‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖ := by
    have htrigger : (keep∩(V.inner v.1.1 v.1.2∩(cores v).kept ci)).Nonempty :=
      ⟨z,hz.1.2,hz.2⟩
    have hh := hgood v ci hγ htrigger
      z ⟨((cores v).subset ci).1 hz.2.2,hkeepGood hz.1.2⟩
      z' ⟨((cores v).subset ci).1 hz'.2.2,hkeepGood hz'.1.2⟩
    rw [v.2.1] at hh
    have hcomp := hp.native_base_le_unsheared hN old z z'
    calc
      _ = oldWidth⁻¹*|MvPolynomial.eval (xp z.1 z.2) (d.P k (p.γ old))-
          MvPolynomial.eval (xp z'.1 z'.2) (d.P k (p.γ old))| := by
        change |oldWidth⁻¹*_-oldWidth⁻¹*_|=_
        rw [←mul_sub,abs_mul,abs_of_pos (inv_pos.mpr ha)]
      _ ≤ oldWidth⁻¹*((2+G/2)*(K^14*(K^6)⁻¹*δ (d.N k) (p.r mid))+
          (24*K)/2*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*
            (((2:ℝ)^p.T (p.lev old))⁻¹)*‖packetBase p old z-packetBase p old z'‖) :=
        mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ha.le)
      _ ≤ oldWidth⁻¹*((2+G/2)*(K^14*(K^6)⁻¹*δ (d.N k) (p.r mid))+
          (24*K)/2*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*
            (((2:ℝ)^p.T (p.lev old))⁻¹)*
              (comparison*‖unshearedPacketBase p old z-unshearedPacketBase p old z'‖)) := by
        gcongr
      _ = _ := by dsimp [additive,Lip,slope]; ring
  refine ⟨current,hcurrent,inter_subset_left,(fun z hz => hkeepGood hz.2),?_,hsharp⟩
  have hlaw : μ.restrict keep=raw.restrict current := by
    rw [Measure.restrict_restrict hkeep,inter_comm]
  rw [hlaw,Measure.restrict_apply_univ] at hloss
  simpa only [Measure.restrict_apply_univ] using hloss

/-- Renew the actual GLOBAL parent gradient once, then count every resolved
independent joint mesh of P/a in the literal unsheared old coordinates.
All parent bounds, original-law cuts, gradients, fine frames and support
lists are produced from the original problem and path. -/
theorem ValueBranchData.exists_parent_sharp_original_source
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hHterminal : ∀ w, H₀ w ⊆ {z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k^(τ+ε) ≤ K) (hκK : 3*p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K^qcore)⁻¹)))
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    (hHbroad : ∀ w, H w ⊆ broad.residual w)
    (old : Fin p.C) (hold : p.lev old=i) (hactive : F.active old)
    (hmid : p.lev old ≤ mid) (hstop : mid ≤ stop)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    {Kc width θrow : ℝ} {qc : ℕ} (hKc : 2*K^(qcore+7) ≤ Kc)
    (hwidthpos : 0 < width) (hwidthfloor : (Kc^qc)⁻¹ ≤ width)
    (hstrip : width*(6*p.κ^3*d.N k^(2*δ₀*d.L)) ≤ r)
    (hdeep : ∀ fine deep : Fin p.C, p.lev fine=mid → p.lev deep=stop →
      6*K^R*p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ renewalCellMesh Kc J qc)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) (hfraction : 0 ≤ fraction)
    (δref : ENNReal) (hδ0 : δref ≠ 0) (hδtop : δref ≠ ∞)
    (hβ1 : δref⁻¹*ENNReal.ofReal (8*fraction) < 1)
    (source : Set Event) (hsource : MeasurableSet source)
    (hsub : source ⊆ V.coreRetained cores (p.γ old) ∩ p.F old)
 :
    let G := coreGradientCoeff (2*K^(qcore+7)) width θrow J
    let oldWidth := δ (d.N k) (p.r (p.lev old))
    let additive := (2+G/2)*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/oldWidth))
    let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)
    let slope := 12*K*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison
    ∃ current : Set Event, MeasurableSet current ∧ current⊆source ∧
      current⊆Prod.fst ⁻¹' ParentSignal.goodLines
        (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) ∧
      ((d.ν k (p.γ old)).prod volume) source ≤
        ((d.ν k (p.γ old)).prod volume) current+
          ENNReal.ofReal (4*K^(3*R+28)*p.κ^2)*
            (ENNReal.ofReal (θrow*(K^R)⁻¹)+27*(δref*ENNReal.ofReal (p.κ^2)))*
            (d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)) ∧
      ∀ base hidden : ℝ, 0 < base → 0 < hidden → additive ≤ hidden/2 →
        6*slope*(((2:ℝ)^p.T (p.lev old))⁻¹)*base ≤ oldWidth*hidden →
        let frameBudget := 3*(((1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*
          ((2:ℝ)^p.T mid/(2:ℝ)^p.T (p.lev old)))*comparison)*base
        ∃ S : Finset (Fin 4 → ℤ),
          (S.card : ℝ)*base^3 ≤ 62208*(max 1 frameBudget)^3*K^(3*R+28)*p.κ^4*
            d.N k^(2*δ₀*d.L)*d.N k^(d.f (p.r mid)-d.f (p.r (p.lev old))) ∧
          ∀ z∈current, jointCode base hidden
            (fun j => unshearedPacketBase p old z j)
            (physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z)∈S := by
  obtain ⟨current,hcurrent,hcurrentSource,hgood,hloss,hsharp⟩ :=
    V.exists_parent_sharp_pair_original_source Q hpure hd hp hHE hHbase hHterminal
      hK hmax hpower hκK cores broad hHbroad old hold hactive hmid hstop hr hrL hD hjets
      hKc hwidthpos hwidthfloor hstrip hdeep hθrow hθrow1 hfraction δref hδ0 hδtop hβ1
      source hsource hsub
  have hcurrentSub : current⊆V.coreRetained cores (p.γ old)∩p.F old :=
    fun z hz => hsub (hcurrentSource hz)
  let G := coreGradientCoeff (2*K^(qcore+7)) width θrow J
  let oldWidth := δ (d.N k) (p.r (p.lev old))
  let additive := (2+G/2)*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/oldWidth))
  let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)
  let slope := 12*K*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison
  let Lip := slope*(((2:ℝ)^p.T (p.lev old))⁻¹)/oldWidth
  have hKp : 0 < K := by linarith
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have ha : 0 < oldWidth := by dsimp [oldWidth,δ]; positivity
  have hG : 0 ≤ G := by
    dsimp [G,coreGradientCoeff]
    have hK0 := coreRow_spec.1
    positivity
  have hLip : 0 ≤ Lip := by dsimp [Lip,slope,comparison]; positivity
  refine ⟨current,hcurrent,hcurrentSource,hgood,hloss,?_⟩
  intro base hidden hbase hhidden herror hmesh
  exact V.exists_actual_unsheared_physical_joint_support Q hd hp hHbase hK cores old hmid
    current hcurrentSub (physicalParentSignal (d.N k) p old (d.P k (p.γ old))) ha hbase hhidden
    hLip le_rfl hmesh herror hsharp

end Prepared
end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
