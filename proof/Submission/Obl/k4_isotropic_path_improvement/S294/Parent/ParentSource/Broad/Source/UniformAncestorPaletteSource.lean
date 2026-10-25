-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.UniformAncestorPaletteSource, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.BroadAncestorGridRecords
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorSignalJointCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.RetainedHistoryQueries
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorRecordQueries
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RetainedAncestorBreadth

set_option autoImplicit false
set_option maxRecDepth 32768

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native Analytic
open k4_stable_native_signal_oscillation
open Submission.Lib.K4OriginalGeometricReference.PhysicalGraphCells
open Submission.Lib.K4ListedExceptions
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
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

/-- One actual original-law retained set precedes EVERY later packet,
EVERY query scale and EVERY Borel original-velocity test. The only later
requirements are the explicit relative geometric resolution budgets. -/
theorem ValueBranchData.exists_uniform_ancestor_palette_power_source
    (hHE : ∀ w, H w ⊆ d.E k w) (hHbase : ∀ w, H w ⊆ Q.base w)
    (hK : 2304 ≤ K) (hmax : max p.κ (d.K k) ≤ K)
    (hpower : d.N k ^ (τ + ε) ≤ K) (hκK : 3 * p.κ ≤ K)
    (cores : V.CoreFamilies (ENNReal.ofReal ((K ^ qcore)⁻¹)))
    (root : Fin p.C) (stop : ℕ) (hmid : p.lev root ≤ mid) (hstop : mid ≤ stop)
    (hr : 0 ≤ p.r mid) (hrL : p.r mid ≤ d.L)
    {D J : ℕ} (hD : 5186 ≤ D) (hjets : DenseJetBound D J)
    (hwidth : δ (d.N k) (p.r mid) ≤ δ (d.N k) (p.r (p.lev root)))
    {baseMesh hidden : ℝ} (hbase : 0 < baseMesh) (hhidden : 0 < hidden)
    (hbaseSmall : ∀ deep : Fin p.C, p.lev deep = stop →
      p.unshearedDeepRadius root deep ≤ baseMesh)
    (hcoreSmall : ∀ fine deep : Fin p.C, p.lev fine = mid → p.lev deep = stop →
      p.deepBaseRadius (d.N k) d.L δ₀ fine deep ≤ (K ^ R)⁻¹ / 12)
    (hheightSmall : ∀ fine deep : Fin p.C, p.lev fine = mid → p.lev deep = stop →
      (δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev root)))*
        (2 * (K ^ 14 * (K ^ 6)⁻¹ *
          (δ (d.N k) (p.r mid) / δ (d.N k) (p.r (p.lev root)))) +
          ((K ^ (qcore + 7)) ^ J * (p.κ + K ^ 14 * (K ^ 6)⁻¹)) *
            (6 * K ^ R * p.deepBaseRadius (d.N k) d.L δ₀ fine deep)) ≤ hidden)
    (paletteMesh paletteBound : ℝ) (paletteFloor : ENNReal)
    (F : PaletteFamily Q (p.lev root) stop paletteMesh paletteBound paletteFloor)
    (hactive : F.active root)
    {broadRadius broadFraction : ℝ} (broad : BroadResidual F broadRadius broadFraction)
    (E : Set Event) (hE : MeasurableSet E)
    (hECore : E⊆V.coreRetained cores (p.γ root))
    (hEbroad : E⊆broad.residual (p.γ root)∩p.F root)
    (hH₀E : ∀ w, H₀ w⊆d.E k w)
    (hH₀terminal : ∀ w, H₀ w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (physicalPaletteMesh paletteRatio : ℝ) (hRatio : 0 ≤ paletteRatio)
    (hOriginal : ∀ b, F.active b → F.U b⊆
      likelihoodGood Q.law (labelledSupport Q.residual)
        (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette physicalPaletteMesh)
        (p.lev root) stop paletteRatio)
    (χ finest : ℝ) (hχ : 0 ≤ χ)
    {dimension f₀ profileError Kcap : ℝ} (hdim : 0 ≤ dimension)
    (hprofile : ∀ a, 0 ≤ a → a ≤ d.L → |d.f a-f₀-dimension*a| ≤ profileError)
    (hbudget : 512*(max p.κ (d.K k))^2*p.κ*4^dimension*
      d.N k^(2*profileError+(τ+2*δ₀*d.L)+ε) ≤ Kcap)
    (μ : Measure Ev) (hμ : μ ≤ ((d.ν k (p.γ root)).prod volume).restrict E)
    (cut : ℝ) (hcut : 0 < cut) :
    ∃ (n : ↥(F.retainedOriginalFinePackets root) → ℕ)
      (code : (deep : ↥(F.retainedOriginalFinePackets root)) → Fin (n deep) → (Fin 4 → ℤ))
      (piece : (Σ deep, Fin (n deep)) → Set Ev),
      (∀ deep, (n deep:ℝ) ≤ K^12) ∧
      (∀ r, MeasurableSet (piece r)) ∧
      (∀ r, piece r⊆E∩F.fineOriginalEvent root r.1.1 univ) ∧
      Pairwise (fun r s => Disjoint (piece r) (piece s)) ∧
      (∀ z∈E, ∃ r, z∈piece r) ∧
      (∀ r, (piece r).Nonempty → F.coding.code r.1.1∉
        Q.intrinsicNarrowStates F.code stop F.U broadRadius broadFraction root) ∧
      (∀ r z, z∈piece r →
        (fun j => ⌊parentUnshearedCoordinates (d.N k) p root (p.R root) z j /
          ((Fin.snoc (fun _ : Fin 3 => baseMesh) hidden : Fin 4 → ℝ) j)⌋)∈
          referenceCellOptions
            (Fin.snoc (fun _ : Fin 3 => baseMesh) hidden)
            (Fin.snoc (fun _ : Fin 3 => baseMesh) hidden) (code r.1 r.2)) ∧
    ∃ G : Set Ev, MeasurableSet G ∧
      μ Gᶜ ≤ ENNReal.ofReal cut*(⌈K^12⌉₊:ENNReal)*
        ((d.ν k (p.γ root)).prod volume) {z | (p.γ root,z)∈F.U root} ∧
      (∀ r : Σ deep, Fin (n deep), (μ.restrict G) (piece r)=0 ∨
        ENNReal.ofReal cut*((d.ν k (p.γ root)).prod volume)
          (F.fineOriginalEvent root r.1.1 univ) ≤ (μ.restrict G) (piece r)) ∧
      (∀ (r : Σ deep, Fin (n deep)) (D : Set (ℤ×ℤ)), MeasurableSet D →
        (μ.restrict G) {z | z∈piece r ∧ velocityPalette physicalPaletteMesh (v z.1)∈D} ≤
          ENNReal.ofReal ((8*paletteRatio)/cut)*(μ.restrict G) (piece r)*
            ((Q.coarseLaw (p.lev root) (F.code root)).map
              (labelledVelocityPalette physicalPaletteMesh)) D) ∧
      (0 ≤ broadFraction → ∀ (rec : Σ deep, Fin (n deep)) (width : ℝ)
        (normal : EuclideanSpace ℝ (Fin 2)) (offset : ℝ), ‖normal‖=1 →
        width*(∑ j : Fin 2, ∑ l : Fin 2, |p.Q root j l|) ≤
          broadRadius*((2:ℝ)^p.T (p.lev root)*|(p.Q root).det|) →
        (μ.restrict G) (piece rec∩{z | |Inner.inner ℝ normal (v z.1)-offset| ≤ width}) ≤
          ENNReal.ofReal ((8*broadFraction)/cut)*(μ.restrict G) (piece rec)) ∧
      ∀ child : Fin p.C,
      p.γ child=p.γ root →
      δ (d.N k) (p.r (p.lev child)) ≤ δ (d.N k) (p.r (p.lev root)) →
      0 ≤ p.r (p.lev child) → p.lev child ≤ stop →
      p.r (p.lev child)+χ*finest ≤ d.L →
      3*((2:ℝ)^p.T (p.lev child)/(2:ℝ)^p.T (p.lev root))*baseMesh ≤ (d.N k^χ)^(-finest) →
      3*(δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*hidden ≤ (d.N k^χ)^(-finest) →
      ∀ r t, finest⁻¹ ≤ r → r ≤ finest → 0 ≤ t → t ≤ finest →
      ∀ q (D : Set (ℤ×ℤ)), MeasurableSet D →
        ((μ.restrict G).restrict (p.F child))
          {z | jointCode ((d.N k^χ)^(-r)) ((d.N k^χ)^(-t))
            (fun j => unshearedPacketBase p child z j)
            (physicalParentSignal (d.N k) p child (p.R root) z)=q ∧
          velocityPalette physicalPaletteMesh (v z.1)∈D} ≤
          ENNReal.ofReal ((8*paletteRatio)/cut)*(625:ENNReal)*
            (ENNReal.ofReal (Kcap*(d.N k^χ)^(-3*r-dimension*t))*
              (d.ν k (p.γ child) (p.A child)*
                ENNReal.ofReal (((2:ℝ)^p.T (p.lev child))⁻¹)))*
            ((Q.coarseLaw (p.lev root) (F.code root)).map
              (labelledVelocityPalette physicalPaletteMesh)) D := by
  classical
  obtain ⟨n,code,piece,hn,hm,hs,hdj,hcover,hqueries⟩ :=
    V.exists_broad_ancestor_history_grid_records Q hpure hd hp hHE hHbase hK hmax hpower hκK
      cores root root stop hmid hstop hr hrL hD hjets hwidth hbase hhidden
      hbaseSmall hcoreSmall hheightSmall paletteMesh paletteBound paletteFloor F hactive broad
      E hE hECore hEbroad
  let admissible := fun child : Fin p.C =>
    p.γ child=p.γ root ∧
    δ (d.N k) (p.r (p.lev child)) ≤ δ (d.N k) (p.r (p.lev root)) ∧
    0 ≤ p.r (p.lev child) ∧ p.lev child ≤ stop ∧
    p.r (p.lev child)+χ*finest ≤ d.L ∧
    3*((2:ℝ)^p.T (p.lev child)/(2:ℝ)^p.T (p.lev root))*baseMesh ≤ (d.N k^χ)^(-finest) ∧
    3*(δ (d.N k) (p.r (p.lev root))/δ (d.N k) (p.r (p.lev child)))*hidden ≤ (d.N k^χ)^(-finest)
  let Child := {child : Fin p.C // admissible child}
  let Scales := {rt : ℝ×ℝ // finest⁻¹ ≤ rt.1 ∧ rt.1 ≤ finest ∧ 0 ≤ rt.2 ∧ rt.2 ≤ finest}
  let Query := Child×Scales
  let region := fun q : Query => p.F q.1.1
  let coords := fun q : Query => parentUnshearedCoordinates (d.N k) p q.1.1 (p.R root)
  let meshes : Query → Fin 4 → ℝ := fun q =>
    Fin.snoc (fun _ : Fin 3 => (d.N k^χ)^(-q.2.1.1)) ((d.N k^χ)^(-q.2.1.2))
  let state := fun q : Query => fun z : Ev => fun j => ⌊coords q z j/meshes q j⌋
  let pure := fun q : Query =>
    ENNReal.ofReal (Kcap*(d.N k^χ)^(-3*q.2.1.1-dimension*q.2.1.2))*
      (d.ν k (p.γ q.1.1) (p.A q.1.1)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev q.1.1))⁻¹))
  have hwide (r : Σ deep, Fin (n deep)) (hne : (piece r).Nonempty) :
      F.coding.code r.1.1∉
        Q.intrinsicNarrowStates F.code stop F.U broadRadius broadFraction root := by
    obtain ⟨z,hz⟩ := hne
    exact Native.BroadResidual.not_narrow_of_fine_original_event F broad hp root rfl
      ⟨r.1.1,(F.retained_original_fine_spec root r.1).1⟩ z
      (hEbroad (hs r hz).1) (hs r hz).2
  have hN : 1 ≤ d.N k := by linarith [hd.1 k]
  have hNp : 0 < d.N k := zero_lt_one.trans_le hN
  have hNχ : 1 ≤ d.N k^χ := Real.one_le_rpow hN hχ
  have href : ∀ j, 0 < (Fin.snoc (fun _ : Fin 3 => baseMesh) hidden : Fin 4 → ℝ) j := by
    intro j
    refine Fin.lastCases ?_ (fun _ => ?_) j
    · simpa only [Fin.snoc_last] using hhidden
    · simpa only [Fin.snoc_castSucc] using hbase
  have hrecords := hqueries (Fin.snoc (fun _ : Fin 3 => baseMesh) hidden) href (fun _ => le_rfl)
  have hmenu (q : Query) : ∃ options : (Σ deep, Fin (n deep)) → Finset (Fin 4 → ℤ),
      (∀ r z, z∈piece r → state q z∈options r) ∧
      ∀ r c, c∈options r → ∀ z∈piece r, state q z∈integerCodeBox 2 c := by
    rcases q with ⟨⟨child,hw,hsc,hrc,hl,hdp,hb,hh⟩,⟨⟨r,t⟩,hrl,hrh,ht,htf⟩⟩
    obtain ⟨options,_hcard,hopt,hpad⟩ := ancestor_record_query_menus
      (d.N k) root child piece (fun a => code a.1 a.2) hbase hhidden
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hNp χ) (-r))
      (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hNp χ) (-t))
      (fun a z hz => (hrecords a).2.1 z hz)
      (hb.trans (Real.rpow_le_rpow_of_exponent_le hNχ (neg_le_neg hrh)))
      (hh.trans (Real.rpow_le_rpow_of_exponent_le hNχ (neg_le_neg htf)))
    exact ⟨options,hopt,hpad⟩
  choose options hoptions hpadding using hmenu
  have hpieces : ∀ deep, n deep ≤ ⌈K^12⌉₊ := by
    intro deep
    exact_mod_cast (hn deep).trans (Nat.le_ceil (K^12))
  have hf (deep : ↥(F.retainedOriginalFinePackets root)) : p.lev deep.1=stop :=
    ((Finset.mem_filter.mp (F.retained_original_fine_spec root deep).1).2).1
  have hw (deep : ↥(F.retainedOriginalFinePackets root)) : p.γ deep.1=p.γ root :=
    ((Finset.mem_filter.mp (F.retained_original_fine_spec root deep).1).2).2.1
  have hcoverage : ∀ᵐ z ∂μ, ∃ r, z∈piece r :=
    Filter.Eventually.mono ((ae_mono hμ) (ae_restrict_mem hE)) (fun z hz => hcover z hz)
  have hregion (q : Query) : MeasurableSet (region q) := by
    exact (hp.2.2.2.2.2.2.2 q.1.1).2.2.2.2.2.2.2.2.2.1
  have hwhole (q : Query) (r) (h : (piece r∩region q).Nonempty) : piece r⊆region q := by
    obtain ⟨z,hz,hzc⟩ := h
    have hbasez : z∈Q.base (p.γ root) := Q.residual_subset _
      (broad.subset_prepared _ (hEbroad (hs r hz).1).1)
    have hhist := F.fine_original_event_whole_earlier_packet hp root r.1.1 q.1.1
      (hf r.1) (hw r.1) q.1.2.1 q.1.2.2.2.2.1 z (hs r hz).2 hbasez hzc
    exact fun _ hz => hhist (hs r hz).2
  have hstate (q : Query) (z : Ev) : state q z=
      jointCode ((d.N k^χ)^(-q.2.1.1)) ((d.N k^χ)^(-q.2.1.2))
        (fun j => unshearedPacketBase p q.1.1 z j)
        (physicalParentSignal (d.N k) p q.1.1 (p.R root) z) :=
    (ancestor_joint_code_eq_coordinate_floors _ _ _ _ _ _ _).symm
  have hpureCells (q : Query) (c : Fin 4 → ℤ) :
      ((d.ν k (p.γ root)).prod volume) ((E∩region q)∩{z | state q z=c}) ≤ pure q := by
    let rawE := ((d.ν k (p.γ root)).prod (volume : Measure ℝ)).restrict (E∩region q)
    have hEq : MeasurableSet (E∩region q) := hE.inter (hregion q)
    have hrawμ : rawE ≤ d.μ k (p.γ root) := by
      apply Measure.restrict_mono_set
      intro z hz
      exact hH₀E _ (broad.subset_H _ (hEbroad hz.1).1)
    have hrawbase : ∀ᵐ z ∂rawE, z∈Q.base (p.γ root) :=
      (ae_restrict_mem hEq).mono (fun z hz => Q.residual_subset _
        (broad.subset_prepared _ (hEbroad hz.1).1))
    have hrawroot : ∀ᵐ z ∂rawE, z∈p.F root :=
      (ae_restrict_mem hEq).mono (fun _ hz => (hEbroad hz.1).2)
    have hrawchild : ∀ᵐ z ∂rawE, z∈p.F q.1.1 :=
      (ae_restrict_mem hEq).mono (fun _ hz => hz.2)
    rw [inter_comm (E∩region q) {z | state q z=c}, ←Measure.restrict_apply' hEq]
    have hh := Q.ancestor_joint_signal_child_power_caps hpure.ceiling hd hp root q.1.1
      q.1.2.1 q.1.2.2.1 q.1.2.2.2.1 χ finest hχ q.1.2.2.2.2.2.1
      rawE hrawμ hrawbase hrawroot hrawchild hdim hprofile hbudget
      q.2.1.1 q.2.1.2 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2 c
    have hstateEq : state q=(fun z => jointCode ((d.N k^χ)^(-q.2.1.1)) ((d.N k^χ)^(-q.2.1.2))
        (fun j => unshearedPacketBase p q.1.1 z j)
        (physicalParentSignal (d.N k) p q.1.1 (p.R root) z)) := funext (hstate q)
    rw [hstateEq]
    exact hh
  obtain ⟨G,hG,hloss,hfloor,hcurrent,hcaps⟩ := exists_simultaneous_subhistory_cell_palette_caps
    F hd hp hH₀E (hmid.trans hstop) hRatio hOriginal hH₀terminal root hactive
    (fun deep : ↥(F.retainedOriginalFinePackets root) => deep.1) Subtype.val_injective
    hf hw (fun deep => (F.retained_original_fine_spec root deep).2)
    E hE n ⌈K^12⌉₊ hpieces piece hm hs hdj μ hμ cut hcut region hregion hwhole
    state options state (fun _ q => integerCodeBox 2 q) (fun _ => 625)
    (by intro t q; simp [card_integerCodeBox]) hcoverage
    (fun t r z hz => hoptions t r z hz.1)
    (fun t r q hq z hz => hpadding t r q hq z hz.1) pure hpureCells
  have hstrip (hfr : 0 ≤ broadFraction) (rec : Σ deep, Fin (n deep)) (width : ℝ)
      (normal : EuclideanSpace ℝ (Fin 2)) (offset : ℝ) (hnormal : ‖normal‖=1)
      (hwidth : width*(∑ j : Fin 2, ∑ l : Fin 2, |p.Q root j l|) ≤
        broadRadius*((2:ℝ)^p.T (p.lev root)*|(p.Q root).det|)) :
      (μ.restrict G) (piece rec∩{z | |Inner.inner ℝ normal (v z.1)-offset| ≤ width}) ≤
        ENNReal.ofReal ((8*broadFraction)/cut)*(μ.restrict G) (piece rec) := by
    by_cases hrec : (piece rec).Nonempty
    · have hdom : μ.restrict G ≤ (d.ν k (p.γ root)).prod volume :=
        (Measure.restrict_le_self.trans hμ).trans Measure.restrict_le_self
      exact F.current_record_physical_strip_cap hd hp hH₀E hH₀terminal root rec.1.1 hactive
        (hf rec.1) (hw rec.1) hfr (hwide rec hrec)
        (F.retained_original_fine_spec root rec.1).2
        (μ.restrict G) hdom (piece rec) (fun z hz => (hs rec hz).2) cut hcut (hfloor rec)
        normal hnormal offset hwidth
    · have hempty : piece rec=∅ := Set.not_nonempty_iff_eq_empty.mp hrec
      simp only [hempty,empty_inter,measure_empty,mul_zero,le_refl]
  refine ⟨n,code,piece,hn,hm,hs,hdj,hcover,hwide,?_,G,hG,hloss,hfloor,hcurrent,hstrip,?_⟩
  · exact fun r z hz => (hrecords r).2.1 z hz
  intro child hw hsc hrc hl hdp hb hh r t hrl hrh ht htf c D hD
  have hcap := hcaps (⟨child,hw,hsc,hrc,hl,hdp,hb,hh⟩,⟨(r,t),hrl,hrh,ht,htf⟩) c D hD
  simpa only [hstate,pure,region,Nat.cast_ofNat,
    Submission.Obl.k4_isotropic_path_improvement.S294.Parent.v,
    Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.v] using hcap

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
