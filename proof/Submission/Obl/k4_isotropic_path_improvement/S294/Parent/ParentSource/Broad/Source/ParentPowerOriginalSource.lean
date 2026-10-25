-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.ParentPowerOriginalSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/ParentSource/Broad/Source/ParentPowerOriginalSource.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 83ada3e49b5540f6b00606ae3df6268df68021ab,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Source/ParentPowerOriginalSource.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.ParentSharpOriginalSource
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.ParentCensusPower

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

/-- One actual original physical parent source has all independent joint
censuses with explicit envelope powers. Gradient, fine-frame, slope and
profile constants are derived from primitive width/retention/mesh budgets. -/
theorem ValueBranchData.exists_power_parent_joint_original_source
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
    (hκ₁ : κ₁ ≤ 1) (hmidm : mid < m) (hs : s (p.lev old) ≤ s mid)
    (hgeometry : d.N k^(2*δ₀*d.L) ≤ K) (hconstant : 96*coreRowK₀ ≤ K)
    (w t : ℕ) (hwidthPower : (K^w)⁻¹ ≤ width) (hθPower : (K^t)⁻¹ ≤ θrow)
    {dimension profileError : ℝ} (hdim : 0 ≤ dimension) (hdim1 : dimension ≤ 1)
    (hprofile : d.f (p.r mid)-d.f (p.r (p.lev old)) ≤
      dimension*(p.r mid-p.r (p.lev old))+profileError)
    (hprofilePower : d.N k^profileError ≤ K)
    (source : Set Event) (hsource : MeasurableSet source)
    (hsub : source ⊆ V.coreRetained cores (p.γ old) ∩ p.F old)
 :
    let gradientPower := (qcore+8)*J+w+t*⌈coreRowC₀⌉₊+1
    let ratio := δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev old))
    ∃ current : Set Event, MeasurableSet current ∧ current⊆source ∧
      current⊆Prod.fst ⁻¹' ParentSignal.goodLines
        (d.P k (p.γ old)) (d.K k) (d.B k (p.γ old)) ∧
      ((d.ν k (p.γ old)).prod volume) source ≤
        ((d.ν k (p.γ old)).prod volume) current+
          ENNReal.ofReal (4*K^(3*R+28)*p.κ^2)*
            (ENNReal.ofReal (θrow*(K^R)⁻¹)+27*(δref*ENNReal.ofReal (p.κ^2)))*
            (d.ν k (p.γ old) (p.A old)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev old))⁻¹)) ∧
      ∀ basePower heightPower : ℕ, ∀ base hidden : ℝ, 0 < base → 0 < hidden →
        K^(gradientPower+10)*ratio ≤ hidden →
        K^(gradientPower+12)*(((2:ℝ)^p.T (p.lev old))⁻¹)*base ≤
          δ (d.N k) (p.r (p.lev old))*hidden →
        base ≤ K^basePower*ratio → hidden ≤ K^heightPower*ratio →
        ∃ S : Finset (Fin 4 → ℤ),
          (S.card : ℝ)*base^3*hidden^dimension ≤ K^(3*basePower+3*R+heightPower+73) ∧
          (S.card : ℝ) ≤ K^(3*basePower+3*R+heightPower+73)/(base^3*hidden^dimension) ∧
          ∀ z∈current, jointCode base hidden
            (fun j => unshearedPacketBase p old z j)
            (physicalParentSignal (d.N k) p old (d.P k (p.γ old)) z)∈S := by
  obtain ⟨current,hcurrent,hcurrentSub,hgood,hloss,hcount⟩ := V.exists_parent_sharp_original_source
    Q hpure hd hp hHE hHbase hHterminal hK hmax hpower hκK cores broad hHbroad old hold hactive
    hmid hstop hr hrL hD hjets hKc hwidthpos hwidthfloor hstrip hdeep
    hθrow hθrow1 hfraction δref hδ0 hδtop hβ1 source hsource hsub
  let gradientPower := (qcore+8)*J+w+t*⌈coreRowC₀⌉₊+1
  let G := coreGradientCoeff (2*K^(qcore+7)) width θrow J
  let ratio := δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev old))
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hK1 : 1 ≤ K := by linarith
  have hK0 : 0 ≤ K := zero_le_one.trans hK1
  have hκ : 0 ≤ p.κ := (zero_lt_one.trans_le hp.1).le
  have hκK' : p.κ ≤ K := (le_max_left _ _).trans hmax
  have hG : 0 ≤ G := by
    dsimp [G,coreGradientCoeff]
    have hRow := coreRow_spec.1
    positivity
  have hGK : G ≤ K^gradientPower := coreGradientCoeff_le_power qcore w t J
    (by linarith) hconstant hwidthpos hwidthPower hθrow hθPower
  have hratio : 0 ≤ ratio := by dsimp [ratio,δ]; positivity
  have holdm : p.lev old < m := (hp.2.2.2.2.2.2.2 old).1
  refine ⟨current,hcurrent,hcurrentSub,hgood,hloss,?_⟩
  intro basePower heightPower base hidden hbase hhidden hhiddenFloor hphysical hbaseUpper hhiddenUpper
  have hadditive := gradient_error_le_half_power_mesh (by linarith : 3 ≤ K) gradientPower hGK hratio hhiddenFloor
  have hslope := original_parent_anisotropic_mesh_budget hd hp hK hmax hgeometry gradientPower
    hG hGK old (by positivity : 0 ≤ (((2:ℝ)^p.T (p.lev old))⁻¹)) hbase.le hphysical
  obtain ⟨S,hS,hcover⟩ := hcount base hidden hbase hhidden hadditive hslope
  let frameBudget := 3*(((1+4*p.κ+6*p.κ^3*d.N k^(2*δ₀*d.L))*
    ((2:ℝ)^p.T mid/(2:ℝ)^p.T (p.lev old)))*
    (1+2*(p.κ*d.N k^(2*δ₀*d.L))*(1+‖p.u old‖)))*base
  have hframe : max 1 frameBudget ≤ K^(basePower+12) := by
    have hh := original_unsheared_resolution_le_power hd hp hN hκ₁ (p.lev old) mid holdm hmidm hs
      hK hmax hgeometry old basePower hbaseUpper
    simpa only [frameBudget,mul_assoc] using hh
  have hC : 0 ≤ max 1 frameBudget := zero_le_one.trans (le_max_left _ _)
  have hweighted := physical_parent_joint_census_le_power (hd.1 k) hK hκ hκK' hC
    basePower heightPower R hframe (Real.rpow_nonneg hNp.le _) hgeometry hhidden hdim hdim1
    hprofile hprofilePower hhiddenUpper hS
  exact ⟨S,hweighted,physical_parent_joint_census_div_bound hbase hhidden hweighted,hcover⟩

end Prepared
end
end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
