-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorSignalSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/AncestorSignalSource.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorSignalCoordinates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CoreGradientSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.UnshearedRetainedJointSupport

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native Analytic
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

/-- Renew the actual fixed ANCESTOR test once, then construct independent
joint support lists in EVERY later packet of the same world and every
surviving subset. The mesh condition uses only the RELATIVE clock and
thickness ratios. Both simple roots and large curvature are handled by
the actual original old-signal gradient factory; no polynomial background,
physical-P gradient, new prior or child-count charge is supplied. -/
theorem ValueBranchData.exists_ancestor_signal_joint_source
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hHterminal : ∀ w, H₀ w ⊆ {z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k^(τ+ε) ≤ K) (hκK : 3*p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K^qcore)⁻¹)))
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    (hHbroad : ∀ w, H w ⊆ broad.residual w)
    (root : Fin p.C) (hroot : p.lev root=i) (hactive : F.active root)
    (hmid : p.lev root ≤ mid) (hstop : mid ≤ stop)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hwidth : δ (d.N k) (p.r mid) ≤ δ (d.N k) (p.r (p.lev root)))
    {Kc width θrow : ℝ} {qc : ℕ} (hKc : 2*K^(qcore+7) ≤ Kc)
    (hwidthpos : 0 < width) (hwidthfloor : (Kc^qc)⁻¹ ≤ width)
    (hstrip : width*(6*p.κ^3*d.N k^(2*δ₀*d.L)) ≤ r)
    (hdeep : ∀ fine deep : Fin p.C, p.lev fine=mid → p.lev deep=stop →
      6*K^R*p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ renewalCellMesh Kc J qc)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) (hfraction : 0 ≤ fraction)
    (δref : ENNReal) (hδ0 : δref ≠ 0) (hδtop : δref ≠ ∞)
    (hβ1 : δref⁻¹*ENNReal.ofReal (8*fraction) < 1)
    (source : Set Event) (hsource : MeasurableSet source)
    (hsub : source ⊆ V.coreRetained cores (p.γ root) ∩ p.F root) :
    let G := coreGradientCoeff (2*K^(qcore+7)) width θrow J;
    let additive := (2+G/2)*(K^14*(K^6)⁻¹*
      (δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev root))));
    let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u root‖);
    let Lip := 4*p.κ*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison;
    ∃ current : Set Event, MeasurableSet current ∧ current⊆source ∧
      ((d.ν k (p.γ root)).prod volume) source ≤
        ((d.ν k (p.γ root)).prod volume) current+
          ENNReal.ofReal (4*K^(3*R+28)*p.κ^2)*
            (ENNReal.ofReal (θrow*(K^R)⁻¹)+27*(δref*ENNReal.ofReal (p.κ^2)))*
            (d.ν k (p.γ root) (p.A root)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹)) ∧
      ∀ child : Fin p.C, p.γ child=p.γ root → p.lev child ≤ mid →
      ∀ S : Set Event, S⊆current∩p.F child →
      ∀ base hidden : ℝ, 0 < base → 0 < hidden →
        (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*additive ≤ hidden/2 →
        6*Lip*((2:ℝ)^p.T (p.lev root)/(2:ℝ)^p.T (p.lev child))*base ≤
          (δ (d.N k) (p.r (p.lev child))/δ (d.N k) (p.r (p.lev root)))*hidden →
        let frameBudget := 3*(((1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*
          ((2:ℝ)^p.T mid/(2:ℝ)^p.T (p.lev child)))*
          (1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u child‖)))*base;
        ∃ menu : Finset (Fin 4 → ℤ),
          (menu.card : ℝ)*base^3 ≤ 62208*(max 1 frameBudget)^3*K^(3*R+28)*p.κ^4*
            d.N k^(2*δ₀*d.L)*d.N k^(d.f (p.r mid)-d.f (p.r (p.lev child))) ∧
          ∀ z∈S, jointCode base hidden (fun j => unshearedPacketBase p child z j)
            (physicalParentSignal (d.N k) p child (p.R root) z)∈menu := by
  let raw : Measure Event := (d.ν k (p.γ root)).prod volume
  let μ := raw.restrict source
  have hs : ∀ᵐ z ∂μ, z∈V.coreRetained cores (p.γ root)∩p.F root :=
    (ae_restrict_mem hsource).mono (fun z hz => hsub hz)
  obtain ⟨keep,hkeep,hloss,hgood⟩ := V.exists_gradient_core_source Q hpure hd hp
    hHE hHbase hHterminal hK hmax hpower hκK cores broad hHbroad root hroot hactive
    hmid hstop hr hrL hD hjets hwidth hKc hwidthpos hwidthfloor hstrip hdeep
    hθrow hθrow1 hfraction δref hδ0 hδtop hβ1 μ Measure.restrict_le_self hs
  let current := source∩keep
  have hcurrent : MeasurableSet current := hsource.inter hkeep
  have hlaw : μ.restrict keep=raw.restrict current := by
    rw [Measure.restrict_restrict hkeep,inter_comm]
  rw [hlaw,Measure.restrict_apply_univ] at hloss
  let G := coreGradientCoeff (2*K^(qcore+7)) width θrow J
  let additive := (2+G/2)*(K^14*(K^6)⁻¹*
    (δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev root))))
  let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u root‖)
  let nativeLip := 4*p.κ*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))
  let Lip := nativeLip*comparison
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hG : 0 ≤ G := by
    dsimp [G,coreGradientCoeff]
    have hrow := coreRow_spec.1
    positivity
  have hNativeLip : 0 ≤ nativeLip := by dsimp [nativeLip]; positivity
  have hLip : 0 ≤ Lip := by dsimp [Lip,comparison]; positivity
  refine ⟨current,hcurrent,inter_subset_left,?_,?_⟩
  · simpa only [Measure.restrict_apply_univ] using hloss
  intro child hworld hchild S hS base hidden hbase hhidden hadditive hmesh
  let addChild := (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*additive
  let lipChild := (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*Lip*
    ((2:ℝ)^p.T (p.lev root)/(2:ℝ)^p.T (p.lev child))
  have hLipChild : 0 ≤ lipChild := by dsimp [lipChild,δ]; positivity
  have hSCore : S⊆V.coreRetained cores (p.γ child)∩p.F child := by
    intro z hz
    refine ⟨?_,(hS hz).2⟩
    rw [hworld]
    exact (hsub (hS hz).1.1).1
  have hsharp (v : V.ActiveValue) (ci : ↥(cores v).codes × Bool)
      (hγ : p.γ v.1.1=p.γ child)
      (z : Ev) (hz : z∈S∩(V.inner v.1.1 v.1.2∩(cores v).kept ci))
      (z' : Ev) (hz' : z'∈S∩(V.inner v.1.1 v.1.2∩(cores v).kept ci)) :
      |physicalParentSignal (d.N k) p child (p.R root) z-
        physicalParentSignal (d.N k) p child (p.R root) z'| ≤
        addChild+lipChild*‖unshearedPacketBase p child z-unshearedPacketBase p child z'‖ := by
    have htrigger : (keep∩(V.inner v.1.1 v.1.2∩(cores v).kept ci)).Nonempty :=
      ⟨z,(hS hz.1).1.2,hz.2⟩
    have hh := hgood v ci (hγ.trans hworld) htrigger
      z (((cores v).subset ci).1 hz.2.2) z' (((cores v).subset ci).1 hz'.2.2)
    rw [v.2.1] at hh
    have hrootPair : |packetSignal (d.N k) p root z-packetSignal (d.N k) p root z'| ≤
        additive+Lip*‖unshearedPacketBase p root z-unshearedPacketBase p root z'‖ := by
      change |packetSignal (d.N k) p root z-packetSignal (d.N k) p root z'| ≤
        additive+nativeLip*comparison*‖unshearedPacketBase p root z-unshearedPacketBase p root z'‖
      have hh' : |packetSignal (d.N k) p root z-packetSignal (d.N k) p root z'| ≤
          additive+nativeLip*‖packetBase p root z-packetBase p root z'‖ := by
        simpa only [packetSignal,div_eq_mul_inv,mul_comm,additive,nativeLip,G] using hh
      apply hh'.trans
      have hcomp := hp.native_base_le_unsheared hN root z z'
      have hscaled := mul_le_mul_of_nonneg_left hcomp hNativeLip
      dsimp only [comparison] at *
      nlinarith only [hscaled]
    exact ancestor_signal_pair_in_child_units (d.N k) p root child z z' hrootPair
  have hslope : 6*(lipChild*base/hidden) ≤ 1 :=
    ancestor_signal_joint_slope_budget (d.N k) p root child hbase.le hhidden hmesh
  have hmax (frame : ℝ) : max 1 (max frame (6*(lipChild*base/hidden)))=max 1 frame := by
    rw [←max_assoc,max_eq_left (hslope.trans (le_max_left _ _))]
  simpa only [hmax] using V.exists_actual_unsheared_joint_support Q hd hp hHbase hK
    cores child hchild S hSCore (physicalParentSignal (d.N k) p child (p.R root))
    hbase hhidden hLipChild hadditive hsharp

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
