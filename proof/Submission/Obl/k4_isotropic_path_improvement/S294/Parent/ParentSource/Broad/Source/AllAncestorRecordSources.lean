-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AllAncestorRecordSources, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.GlobalAncestorRecordSource

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native Analytic
open k4_stable_native_signal_oscillation
open scoped ENNReal BigOperators

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

/-- Actual value cores, retained broad histories and original pure caps
construct one palette source for ALL active ancestors. Every local
retained law is exactly the corresponding slice of the returned global
family. The deletion is cut*ceil(K^12), with no root-count charge. -/
theorem ValueBranchData.exists_all_ancestor_record_sources
    (hHE : ∀ w, H w⊆d.E k w) (hHbase : ∀ w, H w⊆Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k^(τ+ε) ≤ K) (hκK : 3*p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K^qcore)⁻¹)))
    (i stop : ℕ) (hmid : i ≤ mid) (hstop : mid ≤ stop)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hwidth : δ (d.N k) (p.r mid) ≤ δ (d.N k) (p.r i))
    {baseRef hiddenRef : ℝ} (hbase : 0 < baseRef) (hhidden : 0 < hiddenRef)
    (hbaseSmall : ∀ root : Fin p.C, p.lev root=i → ∀ deep : Fin p.C, p.lev deep=stop →
      p.unshearedDeepRadius root deep ≤ baseRef)
    (hcoreSmall : ∀ fine deep : Fin p.C, p.lev fine=mid → p.lev deep=stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ (K^R)⁻¹/12)
    (hheightSmall : ∀ root : Fin p.C, p.lev root=i →
      ∀ fine deep : Fin p.C, p.lev fine=mid → p.lev deep=stop →
      (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev root)))*
        (2*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r mid)/δ (d.N k) (p.r (p.lev root))))+
          ((K^(qcore+7))^J*(p.κ+K^14*(K^6)⁻¹))*
            (6*K^R*p.deepBaseRadius (d.N k) d.L δ₀ fine deep)) ≤ hiddenRef)
    (paletteMesh paletteBound : ℝ) (paletteFloor : ENNReal)
    (F : PaletteFamily Q i stop paletteMesh paletteBound paletteFloor)
    {frontRadius fraction : ℝ} (broad : BroadResidual F frontRadius fraction)
    (E : Fin (d.W k) → Set Ev) (hE : ∀ w, MeasurableSet (E w))
    (hECore : ∀ w, E w⊆V.coreRetained cores w)
    (hEbroad : ∀ w, E w⊆broad.residual w)
    (hH₀E : ∀ w, H₀ w⊆d.E k w)
    (hH₀terminal : ∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (pv paletteRatio : ℝ) (hRatio : 0 ≤ paletteRatio)
    (hOriginal : ∀ b, F.active b → F.U b⊆likelihoodGood Q.law (labelledSupport Q.residual)
      (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette pv) i stop paletteRatio)
    (χ finest : ℝ) (hχ : 0 ≤ χ)
    {dimension f₀ profileError Kcap : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ x, 0 ≤ x → x ≤ d.L → |d.f x-f₀-dimension*x| ≤ profileError)
    (hbudget : 512*(max p.κ (d.K k))^2*p.κ*4^dimension*
      d.N k^(2*profileError+(τ+2*δ₀*d.L)+ε) ≤ Kcap)
    (cut : ℝ) (hcut : 0 < cut) :
    ∃ (sources : (root : Fin p.C) → F.active root → OriginalAncestorRecordSource F root
        (E (p.γ root)∩p.F root) K baseRef hiddenRef pv paletteRatio cut frontRadius fraction
          χ finest dimension Kcap)
      (keep : Fin (d.W k) → Set Ev),
      (∀ w, MeasurableSet (keep w) ∧ keep w⊆E w) ∧
      (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (E w\keep w)) ≤
        ENNReal.ofReal cut*(⌈K^12⌉₊:ENNReal) ∧
      ∀ root (hroot : F.active root),
        keep (p.γ root)∩p.F root=(sources root hroot).kept := by
  have hsources (root : Fin p.C) (hroot : F.active root) :
      Nonempty (OriginalAncestorRecordSource F root (E (p.γ root)∩p.F root)
        K baseRef hiddenRef pv paletteRatio cut frontRadius fraction χ finest dimension Kcap) := by
    have hl : p.lev root=i := F.level root hroot
    subst i
    have hmRoot : MeasurableSet (E (p.γ root)∩p.F root) :=
      (hE _).inter (hp.2.2.2.2.2.2.2 root).2.2.2.2.2.2.2.2.2.1
    exact V.exists_uniform_ancestor_record_source Q hpure hd hp hHE hHbase hK hmax hpower hκK
      cores root stop hmid hstop hr hrL hD hjets
      hwidth hbase hhidden (hbaseSmall root rfl)
      hcoreSmall (hheightSmall root rfl) paletteMesh paletteBound paletteFloor F hroot broad
      (E (p.γ root)∩p.F root) hmRoot (fun _ hz => hECore _ hz.1)
      (fun _ hz => ⟨hEbroad _ hz.1,hz.2⟩) hH₀E hH₀terminal pv paletteRatio hRatio
      hOriginal χ finest hχ hdim hprofile hbudget cut hcut
  have hbaseE (w) : E w⊆Q.base w := fun z hz =>
    Q.residual_subset _ (broad.subset_prepared _ (hEbroad w hz))
  exact F.assemble_original_ancestor_record_sources hd hp E hE hbaseE hsources

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
