-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.MultiscaleAncestorCensus, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/MultiscaleAncestorCensus.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.MultiscaleAncestorSignalSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.MultiscaleCensus

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators

noncomputable section

/-- One actual original ancestor source supplies ALL independent census
queries after choosing a later child and any registered depth subsequence.
Its admissibility ratio is the relative a/h; the source and all deletion
charges were already fixed before that child or subsequence was chosen. -/
theorem BroadMultiscaleCoreSource.exists_multiscale_ancestor_census_source
    {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {m n : ℕ} {K : ℝ} {e R : ℕ} {depth : Fin n → ℕ}
    {H₀ original : Fin (d.W k) → Set Event} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H₀ u τ) (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (C : BroadMultiscaleCoreSource d k p original n depth K e R)
    (hHE : ∀ w, original w⊆d.E k w) (hHbase : ∀ w, original w⊆Q.base w)
    (hHterminal : ∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k^(τ+ε) ≤ K) (hκK : 3*p.κ ≤ K)
    {i stop : ℕ} {a A r fraction : ℝ} {θ : ENNReal}
    {F : PaletteFamily Q i stop a A θ} (broad : BroadResidual F r fraction)
    (hHbroad : ∀ w, original w⊆broad.residual w)
    (root : Fin p.C) (hroot : p.lev root=i) (hactive : F.active root)
    (hmid : ∀ j, p.lev root ≤ depth j) (hstop : ∀ j, depth j ≤ stop)
    (hr : ∀ j, 0 ≤ p.r (depth j)) (hrL : ∀ j, p.r (depth j) ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hwidth : ∀ j, δ (d.N k) (p.r (depth j)) ≤ δ (d.N k) (p.r (p.lev root)))
    {Kc width θrow : ℝ} {qc : ℕ} (hKc : 2*K^((3*R+58)+7) ≤ Kc)
    (hwidthpos : 0 < width) (hwidthfloor : (Kc^qc)⁻¹ ≤ width)
    (hstrip : width*(6*p.κ^3*d.N k^(2*δ₀*d.L)) ≤ r)
    (hdeep : ∀ j, ∀ fine deep : Fin p.C, p.lev fine=depth j → p.lev deep=stop →
      6*K^R*p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ renewalCellMesh Kc J qc)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) (hfraction : 0 ≤ fraction)
    (δref : ENNReal) (hδ0 : δref≠0) (hδtop : δref≠∞)
    (hβ1 : δref⁻¹*ENNReal.ofReal (8*fraction)<1)
    (source : Set Event) (hsource : MeasurableSet source)
    (hsub : source⊆C.current (p.γ root)∩p.F root)
    {Kgeom : ℝ} (hKK : K ≤ Kgeom)
    (hgeometry : d.N k^(2*δ₀*d.L) ≤ Kgeom) (hconstant : 96*coreRowK₀ ≤ Kgeom)
    (w t : ℕ) (hwidthPower : (Kgeom^w)⁻¹ ≤ width) (hθPower : (Kgeom^t)⁻¹ ≤ θrow)
    (hκ₁ : κ₁ ≤ 1) (hmidm : ∀ j, depth j < m) :
    let gp := ((3*R+58)+8)*J+w+t*⌈coreRowC₀⌉₊+1;
    let reference := d.ν k (p.γ root) (p.A root)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹);
    let cost := ENNReal.ofReal (4*K^(3*R+28)*p.κ^2)*
      (ENNReal.ofReal (θrow*(K^R)⁻¹)+27*(δref*ENNReal.ofReal (p.κ^2)));
    ∃ current : Set Event, MeasurableSet current ∧ current⊆source ∧
      ((d.ν k (p.γ root)).prod volume) source ≤
        ((d.ν k (p.γ root)).prod volume) current+(n:ENNReal)*cost*reference ∧
      ∀ child : Fin p.C, p.γ child=p.γ root →
      ∀ (nn : ℕ) (dep : ℕ → ℕ) (index : Fin nn → Fin n),
        dep 0=p.lev child → (∀ j, depth (index j)=dep (j.val+1)) →
        (∀ j : Fin nn, p.lev child ≤ dep (j.val+1)) →
        (∀ j : Fin nn, s (p.lev child) ≤ s (dep (j.val+1))) →
      ∀ dimension profileError fineMesh Kcensus : ℝ, ∀ gapPower : ℕ,
        0 ≤ dimension → dimension ≤ 1 →
        (∀ j : Fin nn, d.f (p.r (dep (j.val+1)))-d.f (p.r (p.lev child)) ≤
          dimension*(p.r (dep (j.val+1))-p.r (p.lev child))+profileError) →
        d.N k^profileError ≤ Kgeom → 0 < fineMesh →
        (δ (d.N k) (p.r (p.lev child))/δ (d.N k) (p.r (p.lev root)))/
          ((2:ℝ)^p.T (p.lev root)/(2:ℝ)^p.T (p.lev child)) ≤ Kcensus →
        Kgeom^(3*R+gp+gapPower+83) ≤ Kcensus →
        Kgeom^(gp+10)*(δ (d.N k) (p.r (dep nn))/δ (d.N k) (p.r (p.lev child))) ≤ fineMesh →
        (∀ j<nn, δ (d.N k) (p.r (dep j))/δ (d.N k) (p.r (p.lev child)) ≤
          Kgeom^gapPower*(δ (d.N k) (p.r (dep (j+1)))/δ (d.N k) (p.r (p.lev child)))) →
      ∀ S : Set Event, S⊆current∩p.F child →
      ∀ base hidden : ℝ, fineMesh ≤ base → base ≤ 1 → fineMesh ≤ hidden → hidden ≤ 1 →
        Kcensus^(100:ℕ)*base ≤
          ((δ (d.N k) (p.r (p.lev child))/δ (d.N k) (p.r (p.lev root)))/
            ((2:ℝ)^p.T (p.lev root)/(2:ℝ)^p.T (p.lev child)))*hidden →
        (occupied S (fun z j => unshearedPacketBase p child z j)
          (physicalParentSignal (d.N k) p child (p.R root)) base hidden).Finite ∧
        ((occupied S (fun z j => unshearedPacketBase p child z j)
          (physicalParentSignal (d.N k) p child (p.R root)) base hidden).ncard:ℝ) ≤
          Kcensus/(base^3*hidden^dimension) := by
  obtain ⟨current,hcurrent,hcurrentSub,hloss,hcount⟩ := C.exists_ancestor_signal_layer_source
    Q hpure hd hp hHE hHbase hHterminal hK hmax hpower hκK broad hHbroad
    root hroot hactive hmid hstop hr hrL hD hjets hwidth hKc hwidthpos hwidthfloor
    hstrip hdeep hθrow hθrow1 hfraction δref hδ0 hδtop hβ1 source hsource hsub
    hKK hgeometry hconstant w t hwidthPower hθPower hκ₁ hmidm
  let gp := ((3*R+58)+8)*J+w+t*⌈coreRowC₀⌉₊+1
  refine ⟨current,hcurrent,hcurrentSub,hloss,?_⟩
  intro child hworld nn dep index hzero hmatch hchild hsChild dimension profileError
    fineMesh Kcensus gapPower hdim hdim1 hprofile hprofilePower hFine hθK hbudget hlast hstep S hS
  let ratio := fun j => δ (d.N k) (p.r (dep j))/δ (d.N k) (p.r (p.lev child))
  let hRel := (2:ℝ)^p.T (p.lev root)/(2:ℝ)^p.T (p.lev child)
  let aRel := δ (d.N k) (p.r (p.lev child))/δ (d.N k) (p.r (p.lev root))
  let theta := aRel/hRel
  have hrel : 0 < hRel := by dsimp [hRel]; positivity
  have htheta : 0 < theta := by dsimp [theta,aRel,hRel,δ]; positivity
  have hratio (j : ℕ) : 0 < ratio j := by dsimp [ratio,δ]; positivity
  have hratio0 : ratio 0=1 := by
    dsimp only [ratio]
    rw [hzero,div_self (by unfold δ; positivity)]
  apply parent_joint_census_from_depth_menus S
      (fun z j => unshearedPacketBase p child z j)
      (physicalParentSignal (d.N k) p child (p.R root)) (hK.trans hKK)
      htheta hθK hbudget hFine nn ratio (fun j _ => hratio j) hratio0 hlast hstep
  intro j hj base hidden hb hw hlo hphysical hbaseUpper hhiddenUpper
  have hphysical' : Kgeom^(gp+12)*hRel*base ≤ aRel*hidden := by
    calc
      _ = (Kgeom^(gp+12)*base)*hRel := by ring
      _ ≤ (theta*hidden)*hRel := mul_le_mul_of_nonneg_right hphysical hrel.le
      _ = _ := by dsimp [theta]; field_simp
  let jj : Fin nn := ⟨j,hj⟩
  have hk := hcount (index jj)
  rw [hmatch jj] at hk
  obtain ⟨menu,-,hmenu,hcover⟩ := hk child hworld (hchild jj) (hsChild jj) S hS
    dimension profileError hdim hdim1 (hprofile jj) hprofilePower
    0 (gp+10+gapPower) base hidden hb hw hlo hphysical'
    (by simpa only [pow_zero,one_mul,ratio] using hbaseUpper) hhiddenUpper
  refine ⟨menu,?_,hcover⟩
  convert hmenu using 1 <;> congr 2 <;> omega

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
