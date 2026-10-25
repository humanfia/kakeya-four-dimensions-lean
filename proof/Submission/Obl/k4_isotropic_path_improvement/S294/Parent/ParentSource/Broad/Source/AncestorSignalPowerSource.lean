-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorSignalPowerSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/AncestorSignalPowerSource.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorSignalSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentSeparatedPowerSource

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

/-- The actual ancestor-R source has a uniform power census in every
later packet. Additive errors cancel to aFine/aChild, slopes use only
the relative aspect ratio, and the full original deletion cost still
uses the smaller native envelope. No inverse ancestor width is paid. -/
theorem ValueBranchData.exists_power_ancestor_signal_joint_source
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
    (hsub : source ⊆ V.coreRetained cores (p.γ root) ∩ p.F root)
    {Kgeom : ℝ} (hKK : K ≤ Kgeom)
    (hgeometry : d.N k^(2*δ₀*d.L) ≤ Kgeom) (hconstant : 96*coreRowK₀ ≤ Kgeom)
    (w t : ℕ) (hwidthPower : (Kgeom^w)⁻¹ ≤ width) (hθPower : (Kgeom^t)⁻¹ ≤ θrow)
    (hκ₁ : κ₁ ≤ 1) (hmidm : mid < m) :
    let gp := (qcore+8)*J+w+t*⌈coreRowC₀⌉₊+1;
    ∃ current : Set Event, MeasurableSet current ∧ current⊆source ∧
      ((d.ν k (p.γ root)).prod volume) source ≤
        ((d.ν k (p.γ root)).prod volume) current+
          ENNReal.ofReal (4*K^(3*R+28)*p.κ^2)*
            (ENNReal.ofReal (θrow*(K^R)⁻¹)+27*(δref*ENNReal.ofReal (p.κ^2)))*
            (d.ν k (p.γ root) (p.A root)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹)) ∧
      ∀ child : Fin p.C, p.γ child=p.γ root → p.lev child ≤ mid → s (p.lev child) ≤ s mid →
      ∀ S : Set Event, S⊆current∩p.F child →
      ∀ dimension profileError : ℝ, 0 ≤ dimension → dimension ≤ 1 →
        d.f (p.r mid)-d.f (p.r (p.lev child)) ≤
          dimension*(p.r mid-p.r (p.lev child))+profileError →
        d.N k^profileError ≤ Kgeom →
      ∀ basePower heightPower : ℕ, ∀ base hidden : ℝ, 0 < base → 0 < hidden →
        Kgeom^(gp+10)*(δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev child))) ≤ hidden →
        Kgeom^(gp+12)*((2:ℝ)^p.T (p.lev root)/(2:ℝ)^p.T (p.lev child))*base ≤
          (δ (d.N k) (p.r (p.lev child))/δ (d.N k) (p.r (p.lev root)))*hidden →
        base ≤ Kgeom^basePower*(δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev child))) →
        hidden ≤ Kgeom^heightPower*(δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev child))) →
        ∃ menu : Finset (Fin 4 → ℤ),
          (menu.card : ℝ)*base^3*hidden^dimension ≤ Kgeom^(3*basePower+3*R+heightPower+73) ∧
          (menu.card : ℝ) ≤ Kgeom^(3*basePower+3*R+heightPower+73)/(base^3*hidden^dimension) ∧
          ∀ z∈S, jointCode base hidden (fun j => unshearedPacketBase p child z j)
            (physicalParentSignal (d.N k) p child (p.R root) z)∈menu := by
  obtain ⟨current,hcurrent,hcurrentSub,hloss,hcount⟩ := V.exists_ancestor_signal_joint_source
    Q hpure hd hp hHE hHbase hHterminal hK hmax hpower hκK cores broad hHbroad
    root hroot hactive hmid hstop hr hrL hD hjets hwidth hKc hwidthpos hwidthfloor
    hstrip hdeep hθrow hθrow1 hfraction δref hδ0 hδtop hβ1 source hsource hsub
  let gp := (qcore+8)*J+w+t*⌈coreRowC₀⌉₊+1
  let G := coreGradientCoeff (2*K^(qcore+7)) width θrow J
  let additive := (2+G/2)*(K^14*(K^6)⁻¹*
    (δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev root))))
  let comparison := 1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u root‖)
  let Lip := 4*p.κ*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hKp : 0 < K := by linarith
  have hGeom : 2304 ≤ Kgeom := hK.trans hKK
  have hmaxGeom : max p.κ (d.K k) ≤ Kgeom := hmax.trans hKK
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hκK' : p.κ ≤ Kgeom := (le_max_left _ _).trans hmaxGeom
  have hG : 0 ≤ G := by
    dsimp [G,coreGradientCoeff]
    have hrow := coreRow_spec.1
    positivity
  have hGK : G ≤ Kgeom^gp := coreGradientCoeff_le_power_of_envelope qcore w t J
    hKp.le hKK (by linarith) hconstant hwidthpos hwidthPower hθrow hθPower
  refine ⟨current,hcurrent,hcurrentSub,hloss,?_⟩
  intro child hworld hchild hsChild S hS dimension profileError hdim hdim1
    hprofile hprofilePower basePower heightPower base hidden hbase hhidden
    hhiddenFloor hphysical hbaseUpper hhiddenUpper
  let ratio := δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev child))
  have hratio : 0 ≤ ratio := by dsimp [ratio,δ]; positivity
  have haRoot : δ (d.N k) (p.r (p.lev root))≠0 := by unfold δ; positivity
  have haChild : δ (d.N k) (p.r (p.lev child))≠0 := by unfold δ; positivity
  have hcancel : (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*additive=
      (2+G/2)*(K^14*(K^6)⁻¹*ratio) := by
    dsimp [additive,ratio]
    field_simp
  have herrorK : K^14*(K^6)⁻¹ ≤ Kgeom^14*(Kgeom^6)⁻¹ := by
    have heq (x : ℝ) (hx : x≠0) : x^14*(x^6)⁻¹=x^8 := by
      simpa using (pow_sub₀ x hx (by norm_num : (6:ℕ) ≤ 14)).symm
    rw [heq K hKp.ne',heq Kgeom (by linarith)]
    exact pow_le_pow_left₀ hKp.le hKK 8
  have hadditive : (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*additive ≤ hidden/2 := by
    rw [hcancel]
    apply le_trans (b := (2+G/2)*(Kgeom^14*(Kgeom^6)⁻¹*ratio))
    · gcongr
    · exact gradient_error_le_half_power_mesh (by linarith) gp hGK hratio hhiddenFloor
  have hLipCompare : Lip ≤ 12*Kgeom*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison := by
    dsimp [Lip,comparison]
    gcongr
    linarith only [hκK',hGeom]
  have hslope : 6*Lip*((2:ℝ)^p.T (p.lev root)/(2:ℝ)^p.T (p.lev child))*base ≤
      (δ (d.N k) (p.r (p.lev child))/δ (d.N k) (p.r (p.lev root)))*hidden := by
    apply le_trans (b := 6*(12*Kgeom*G*(1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*comparison)*
      ((2:ℝ)^p.T (p.lev root)/(2:ℝ)^p.T (p.lev child))*base)
    · gcongr
    · exact original_parent_anisotropic_mesh_budget hd hp hGeom hmaxGeom hgeometry gp hG hGK
        root (by positivity) hbase.le hphysical
  obtain ⟨menu,hmenu,hcover⟩ := hcount child hworld hchild S hS base hidden hbase hhidden hadditive hslope
  let frameBudget := 3*(((1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*
    ((2:ℝ)^p.T mid/(2:ℝ)^p.T (p.lev child)))*
    (1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u child‖)))*base
  have hframe : max 1 frameBudget ≤ Kgeom^(basePower+12) := by
    have hh := original_unsheared_resolution_le_power hd hp hN hκ₁ (p.lev child) mid
      (hp.2.2.2.2.2.2.2 child).1 hmidm hsChild hGeom hmaxGeom hgeometry child basePower hbaseUpper
    simpa only [frameBudget,mul_assoc] using hh
  have hC : 0 ≤ max 1 frameBudget := zero_le_one.trans (le_max_left _ _)
  have hmenuGeom : (menu.card:ℝ)*base^3 ≤ 62208*(max 1 frameBudget)^3*Kgeom^(3*R+28)*p.κ^4*
      d.N k^(2*δ₀*d.L)*d.N k^(d.f (p.r mid)-d.f (p.r (p.lev child))) := by
    apply hmenu.trans
    gcongr
  have hweighted := physical_parent_joint_census_le_power (hd.1 k) hGeom hκ hκK' hC
    basePower heightPower R hframe (Real.rpow_nonneg hNp.le _) hgeometry hhidden hdim hdim1
    hprofile hprofilePower hhiddenUpper hmenuGeom
  exact ⟨menu,hweighted,physical_parent_joint_census_div_bound hbase hhidden hweighted,hcover⟩

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
