-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RootCensusPackage, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The census package of one active root (session x1088, for x1082's `rootPackage_exists`).

`root_census_package` calls x1065's `BroadMultiscaleCoreSource.exists_multiscale_ancestor_census_source`
ONCE for the root `a` and a source (the records' kept slice), and returns its `current` with
* the mass bound of the census theorem,
* the MK4 occupancy of the root (`child := a`, shape factor `1`, `Source.RootCensus`), and
* for EVERY child `b` at level `lev a + c` with `par^[c] b = a` and every measurable
  `Se ⊆ current ∩ F_b`, the literal `CapClauses` (`Source.ChildCaps.childCapClauses`, its census
  conjunct from the census theorem at `child := b`, `Source.RootCensus.child_hocc_of_census`).
All census side conditions are the census theorem's own, passed as hypotheses; the two
specializations take their depth subsequences and constants as parameters. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootCensus
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.MultiscaleAncestorCensus

set_option autoImplicit false
set_option maxRecDepth 32768
set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Native
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Analytic
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators

noncomputable section

/-- **The census package of one active root.** -/
theorem root_census_package
    {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)}
    {m n : ℕ} {K : ℝ} {e R : ℕ} {depth : Fin n → ℕ}
    {H₀ original : Fin (d.W k) → Set ParentSource.Event} {u : T → ℝ} {τ ε : ℝ}
    (Q : PreparedAngularPath d k p m H₀ u τ) (hpure : Q.uniformPureBounds ε) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (C : BroadMultiscaleCoreSource d k p original n depth K e R)
    (hHE : ∀ w, original w⊆d.E k w) (hHbase : ∀ w, original w⊆Q.base w)
    (hHterminal : ∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k^(τ+ε) ≤ K) (hκK : 3*p.κ ≤ K)
    {i stop : ℕ} {aF AF rF fraction : ℝ} {θF : ENNReal}
    {F : PaletteFamily Q i stop aF AF θF} (broad : BroadResidual F rF fraction)
    (hHbroad : ∀ w, original w⊆broad.residual w)
    (root : Fin p.C) (hroot : p.lev root=i) (hactive : F.active root)
    (hmid : ∀ j, p.lev root ≤ depth j) (hstop : ∀ j, depth j ≤ stop)
    (hr : ∀ j, 0 ≤ p.r (depth j)) (hrL : ∀ j, p.r (depth j) ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hwidth : ∀ j, ParentSource.δ (d.N k) (p.r (depth j)) ≤ ParentSource.δ (d.N k) (p.r (p.lev root)))
    {Kc width θrow : ℝ} {qc : ℕ} (hKc : 2*K^((3*R+58)+7) ≤ Kc)
    (hwidthpos : 0 < width) (hwidthfloor : (Kc^qc)⁻¹ ≤ width)
    (hstrip : width*(6*p.κ^3*d.N k^(2*δ₀*d.L)) ≤ rF)
    (hdeep : ∀ j, ∀ fine deep : Fin p.C, p.lev fine=depth j → p.lev deep=stop →
      6*K^R*p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ renewalCellMesh Kc J qc)
    (hθrow : 0 < θrow) (hθrow1 : θrow ≤ 1) (hfraction : 0 ≤ fraction)
    (δref : ENNReal) (hδ0 : δref≠0) (hδtop : δref≠∞)
    (hβ1 : δref⁻¹*ENNReal.ofReal (8*fraction)<1)
    (source : Set ParentSource.Event) (hsource : MeasurableSet source)
    (hsub : source⊆C.current (p.γ root)∩p.F root)
    {Kgeom : ℝ} (hKK : K ≤ Kgeom)
    (hgeometry : d.N k^(2*δ₀*d.L) ≤ Kgeom) (hconstant : 96*coreRowK₀ ≤ Kgeom)
    (w t : ℕ) (hwidthPower : (Kgeom^w)⁻¹ ≤ width) (hθPower : (Kgeom^t)⁻¹ ≤ θrow)
    (hκ₁ : κ₁ ≤ 1) (hmidm : ∀ j, depth j < m)
    -- the MK4 specialization: child := root
    (nnA : ℕ) (depA : ℕ → ℕ) (indexA : Fin nnA → Fin n)
    (hzeroA : depA 0 = p.lev root) (hmatchA : ∀ j, depth (indexA j) = depA (j.val+1))
    (hchildA : ∀ j : Fin nnA, p.lev root ≤ depA (j.val+1))
    (hsChildA : ∀ j : Fin nnA, s (p.lev root) ≤ s (depA (j.val+1)))
    (dimension profileErrorA fineMeshA KcensusA : ℝ) (gapPowerA : ℕ)
    (hdim0 : 0 ≤ dimension) (hdim1 : dimension ≤ 1)
    (hprofileA : ∀ j : Fin nnA, d.f (p.r (depA (j.val+1)))-d.f (p.r (p.lev root)) ≤
      dimension*(p.r (depA (j.val+1))-p.r (p.lev root))+profileErrorA)
    (hprofilePowerA : d.N k^profileErrorA ≤ Kgeom) (hFineA : 0 < fineMeshA)
    (hθKA : (ParentSource.δ (d.N k) (p.r (p.lev root))/ParentSource.δ (d.N k) (p.r (p.lev root)))/
      ((2:ℝ)^p.T (p.lev root)/(2:ℝ)^p.T (p.lev root)) ≤ KcensusA)
    (hbudgetA : Kgeom^(3*R+(((3*R+58)+8)*J+w+t*⌈coreRowC₀⌉₊+1)+gapPowerA+83) ≤ KcensusA)
    (hlastA : Kgeom^((((3*R+58)+8)*J+w+t*⌈coreRowC₀⌉₊+1)+10)*
      (ParentSource.δ (d.N k) (p.r (depA nnA))/ParentSource.δ (d.N k) (p.r (p.lev root))) ≤ fineMeshA)
    (hstepA : ∀ j<nnA, ParentSource.δ (d.N k) (p.r (depA j))/ParentSource.δ (d.N k) (p.r (p.lev root)) ≤
      Kgeom^gapPowerA*(ParentSource.δ (d.N k) (p.r (depA (j+1)))/ParentSource.δ (d.N k) (p.r (p.lev root))))
    -- the child specialization: every child at level `lb = lev root + c`
    (c lb : ℕ) (hlb : lb = p.lev root + c)
    (nnB : ℕ) (depB : ℕ → ℕ) (indexB : Fin nnB → Fin n)
    (hzeroB : depB 0 = lb) (hmatchB : ∀ j, depth (indexB j) = depB (j.val+1))
    (hchildB : ∀ j : Fin nnB, lb ≤ depB (j.val+1))
    (hsChildB : ∀ j : Fin nnB, s lb ≤ s (depB (j.val+1)))
    {d₁ : ℝ} (hd₀ : 0 ≤ d₁) (hd₁ : d₁ < 1) (profileErrorB fineMeshB KcensusB : ℝ)
    (gapPowerB : ℕ)
    (hprofileB : ∀ j : Fin nnB, d.f (p.r (depB (j.val+1)))-d.f (p.r lb) ≤
      d₁*(p.r (depB (j.val+1))-p.r lb)+profileErrorB)
    (hprofilePowerB : d.N k^profileErrorB ≤ Kgeom) (hFineB : 0 < fineMeshB)
    (hθKB : (ParentSource.δ (d.N k) (p.r lb)/ParentSource.δ (d.N k) (p.r (p.lev root)))/
      ((2:ℝ)^p.T (p.lev root)/(2:ℝ)^p.T lb) ≤ KcensusB)
    (hbudgetB : Kgeom^(3*R+(((3*R+58)+8)*J+w+t*⌈coreRowC₀⌉₊+1)+gapPowerB+83) ≤ KcensusB)
    (hlastB : Kgeom^((((3*R+58)+8)*J+w+t*⌈coreRowC₀⌉₊+1)+10)*
      (ParentSource.δ (d.N k) (p.r (depB nnB))/ParentSource.δ (d.N k) (p.r lb)) ≤ fineMeshB)
    (hstepB : ∀ j<nnB, ParentSource.δ (d.N k) (p.r (depB j))/ParentSource.δ (d.N k) (p.r lb) ≤
      Kgeom^gapPowerB*(ParentSource.δ (d.N k) (p.r (depB (j+1)))/ParentSource.δ (d.N k) (p.r lb)))
    -- the cap constants at the child level
    (hTlb : p.T (p.lev root) ≤ p.T lb)
    (hscale : O204.Split.δ (d.N k) (p.r lb) ≤ O204.Split.δ (d.N k) (p.r (p.lev root)))
    (hr0 : 0 ≤ p.r lb) (hrLb : p.r lb ≤ d.L)
    (hprof : ∀ r, 0 ≤ r → r ≤ d.L → |d.f r - d.f 0 - d₁ * r| ≤ δ₀ * d.L)
    {Kpk εpk : ℝ} (hε : 0 < εpk) (hres : d.N k ^ (-(d.L - p.r lb)) ≤ 4 * εpk)
    (hKbase : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * d.N k ^ (τ + 2 * δ₀ * d.L + ε) ≤ Kpk)
    (hKband : 64 * (max p.κ (d.K k)) ^ 2 * p.κ * 4 ^ d₁ *
      d.N k ^ (2 * (δ₀ * d.L) + (τ + 2 * δ₀ * d.L) + ε) ≤ Kpk)
    (hKc1 : 1 ≤ KcensusB) (hKcK : KcensusB ≤ Kpk) (hfine : fineMeshB ≤ εpk) :
    ∃ current : Set ParentSource.Event, MeasurableSet current ∧ current ⊆ source ∧
      ((d.ν k (p.γ root)).prod volume) source ≤
        ((d.ν k (p.γ root)).prod volume) current +
          (n : ENNReal) * (ENNReal.ofReal (4*K^(3*R+28)*p.κ^2)*
            (ENNReal.ofReal (θrow*(K^R)⁻¹)+27*(δref*ENNReal.ofReal (p.κ^2)))) *
          (d.ν k (p.γ root) (p.A root)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹)) ∧
      (∀ b w : ℝ, fineMeshA ≤ b → b ≤ 1 → fineMeshA ≤ w → w ≤ 1 →
        KcensusA ^ (100 : ℕ) * b ≤ 1 * w →
        (occupied current (fun z j => unshearedPacketBase p root z j)
          (physicalParentSignal (d.N k) p root (p.R root)) b w).Finite ∧
        ((occupied current (fun z j => unshearedPacketBase p root z j)
          (physicalParentSignal (d.N k) p root (p.R root)) b w).ncard : ℝ) ≤
          KcensusA / (b ^ 3 * w ^ dimension)) ∧
      ∀ b : Fin p.C, p.lev b = lb → p.par^[c] b = root → ∀ Se : Set ParentSource.Event, MeasurableSet Se →
        Se ⊆ current ∩ p.F b →
        CapClauses Kpk εpk d₁ (hRelOf (p.T (p.lev root)) (p.T lb))
          (aRelOf (d.N k) (p.r (p.lev root)) (p.r lb))
          (ENNReal.ofReal ((2 : ℝ) ^ p.T (p.lev b))⁻¹ * d.ν k (p.γ b) (p.A b)) (d.ν k (p.γ b))
          (O204.Tangent.packetBase (p.T (p.lev b)) (p.j b) (p.c b) (p.u b))
          (fun z => O204.Tangent.packetSignal (p.R root) z /
            O204.Split.δ (d.N k) (p.r (p.lev b))) Se := by
  have hcen := C.exists_multiscale_ancestor_census_source Q hpure hd hp hHE hHbase hHterminal hK
    hmax hpower hκK broad hHbroad root hroot hactive hmid hstop hr hrL hD hjets hwidth hKc
    hwidthpos hwidthfloor hstrip hdeep hθrow hθrow1 hfraction δref hδ0 hδtop hβ1 source hsource
    hsub hKK hgeometry hconstant w t hwidthPower hθPower hκ₁ hmidm
  obtain ⟨current, hcm, hcsub, hcmass, hcount⟩ := hcen
  refine ⟨current, hcm, hcsub, hcmass, ?_, ?_⟩
  · -- the MK4 occupancy at child := root
    have h := hcount root rfl nnA depA indexA hzeroA hmatchA hchildA hsChildA dimension
      profileErrorA fineMeshA KcensusA gapPowerA hdim0 hdim1 hprofileA hprofilePowerA hFineA hθKA
      hbudgetA hlastA hstepA current (fun z hz => ⟨hz, (hsub (hcsub hz)).2⟩)
    exact root_census_of_child_eq_root root current h
  · intro b hb hpar Se hSem hSeSub
    subst hb
    -- the child and its ancestor
    have hc : c ≤ p.lev b := by omega
    obtain ⟨hlevpar, hγpar, hFpar⟩ := Broad.iterate_par_spec hp.toOriginal c b hc
    rw [hpar] at hlevpar hγpar hFpar
    have hγ : p.γ root = p.γ b := hγpar
    have hFab : p.F b ⊆ p.F root := hFpar
    have hN0 : 0 < d.N k := by linarith [hd.1 k]
    have hA0 : d.ν k (p.γ b) (p.A b) ≠ 0 := (hp.assignment_mass_pos hN0 b).ne'
    -- the census at child := b on `Se`
    have hcb := hcount b hγ.symm nnB depB indexB hzeroB hmatchB hchildB hsChildB d₁
      profileErrorB fineMeshB KcensusB gapPowerB hd₀ hd₁.le hprofileB hprofilePowerB hFineB hθKB
      hbudgetB hlastB hstepB Se hSeSub
    have hocc := child_hocc_of_census root b hTlb Se hcb
    -- the base set
    have hSebase : Se ⊆ Q.base (p.γ b) := by
      intro z hz
      have h1 : z ∈ C.current (p.γ root) := (hsub (hcsub (hSeSub hz).1)).1
      have h2 := hHbase _ (C.current_subset _ h1)
      rw [hγ] at h2
      exact h2
    have hh' : 0 < hRelOf (p.T (p.lev root)) (p.T (p.lev b)) := by unfold hRelOf; positivity
    exact childCapClauses Q hpure hd hp root b hγ hFab hscale hr0 hrLb hA0 hd₀ hd₁ hprof hε hres
      hKbase hKband Se hSem (fun z hz => (hSeSub hz).2) hSebase hh' hKc1 hKcK hfine hocc

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
