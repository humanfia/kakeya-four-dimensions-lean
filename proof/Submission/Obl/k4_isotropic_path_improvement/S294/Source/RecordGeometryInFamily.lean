-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.RecordGeometryInFamily, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.SampleRecordGeometry
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RecordGeometry

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData)

noncomputable section

/-- A genuine registered core index supplies all actual record
geometry fields needed by the full sample constructor. The two room
facts are scalar, and the reference floors are the literal minima. -/
theorem sample_record_geometry_in_family
    (tune : Tuning) {d : ProblemData} {k m : ℕ} {p : PathData (d.W k)}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hd : d.Valid)
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    {d₁ precision loss gain divisor accuracy K G baseRef hiddenRef : ℝ} {Ep i stop nfam : ℕ}
    (hκ : 0 < κ₁) (hκ1 : κ₁ ≤ 1) (hL : 0 < d.L)
    (hloss : 0 < loss) (hloss1 : loss ≤ 1) (hgain : 0 < gain)
    (hdivisor : 1 ≤ divisor) (hδ0 : 0 ≤ δ₀) (hδ : δ₀ ≤ gain/100)
    (haccuracy : 0 ≤ accuracy) (hm : 0 < m) (hgm : 8 ≤ gain*(m:ℝ))
    (hs : ∀ j, s j=((j:ℝ)+1)/m) (hnfam : 0 < nfam)
    (hlevels : ∀ j : Fin nfam, i+j.val < m) (hstop : stop < m)
    (hwindow : (2*accuracy+4*gain)/κ₁ ≤ s stop-s i)
    (hfamily : accuracy+2*gain ≤ s (i+nfam-1)-s i)
    (hK : 2304 ≤ K) (hKG : K ≤ G) (hmax : max p.κ (d.K k) ≤ K)
    (hgeometry : d.N k^(2*δ₀*d.L) ≤ G)
    (hGpower : G ≤ d.N k^(recordGeometryExponent tune κ₁ d₁ Ep precision loss gain divisor*d.L))
    (hconstant : 24 ≤ d.N k^(gain*d.L))
    (hbaseFloor : d.N k^(-accuracy*d.L) ≤ baseRef)
    (hhiddenFloor : d.N k^(-accuracy*d.L) ≤ hiddenRef) (hhidden : hiddenRef ≤ 1) :
    ∃ j : Fin nfam, i+j.val ≤ stop ∧
      δ (d.N k) (p.r (i+j.val)) ≤ δ (d.N k) (p.r i) ∧
      (∀ root : Fin p.C, p.lev root=i → ∀ deep : Fin p.C, p.lev deep=stop →
        p.unshearedDeepRadius root deep ≤ baseRef) ∧
      (∀ fine deep : Fin p.C, p.lev fine=i+j.val → p.lev deep=stop →
        p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ (K^FixedSourcePowers.coreRadius)⁻¹/12) ∧
      ∀ root : Fin p.C, p.lev root=i →
        ∀ fine deep : Fin p.C, p.lev fine=i+j.val → p.lev deep=stop →
        (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev root)))*
          (2*(K^14*(K^6)⁻¹*(δ (d.N k) (p.r (i+j.val))/δ (d.N k) (p.r (p.lev root))))+
            ((K^(3*FixedSourcePowers.coreRadius+58+7))^FixedSourcePowers.jet*(p.κ+K^14*(K^6)⁻¹))*
              (6*K^FixedSourcePowers.coreRadius*p.deepBaseRadius (d.N k) d.L δ₀ fine deep)) ≤ hiddenRef := by
  have hN : 1 ≤ d.N k := (by norm_num : (1:ℝ) ≤ 2).trans (hd.1 k)
  have hG0 : 0 ≤ G := by linarith only [hK,hKG]
  have hi : i < m := by simpa only [Nat.add_zero] using hlevels ⟨0,hnfam⟩
  obtain ⟨j,hjstop,hbase,hcore,hdepth,hclock⟩ :=
    exists_sample_record_middle_in_family (d₁ := d₁) tune hκ hκ1 hloss hloss1 hgain hdivisor
      hδ0 hδ haccuracy hm hgm hs hnfam hwindow hfamily
  obtain ⟨hbaseBudget,hcoreBudget,hdepthBudget,hclockBudget⟩ :=
    record_geometry_budgets_of_normalized_margins FixedSourcePowers.coreRadius FixedSourcePowers.jet
      (3*FixedSourcePowers.coreRadius+58) hN hG0 hL.le hGpower hconstant hbase hcore hdepth hclock
  refine ⟨j,hjstop,?_⟩
  exact original_record_geometry_of_level_budgets hd hp hK hKG hmax hgeometry
    FixedSourcePowers.coreRadius FixedSourcePowers.jet (3*FixedSourcePowers.coreRadius+58)
    i (i+j.val) stop hi (hlevels j) hstop hhidden
    (hbaseBudget.trans hbaseFloor) hcoreBudget (hdepthBudget.trans hhiddenFloor)
    (hclockBudget.trans hhiddenFloor)

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
