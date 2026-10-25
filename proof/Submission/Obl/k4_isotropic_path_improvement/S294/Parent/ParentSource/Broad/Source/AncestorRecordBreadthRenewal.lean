-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.ParentSource.Broad.Source.AncestorRecordBreadthRenewal, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RecordNaturalStates
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.AncestorRecordQueries
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Source.RetainedAncestorBreadth
import Submission.Obl.k4_isotropic_path_improvement.S294.Forward.AncestorRows

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

open Set MeasureTheory Native
open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
open Submission.Lib.K4ListedExceptions
open scoped ENNReal

noncomputable section

/-- The ancestor's graph clock is exactly its own physical signal chart. -/
theorem ancestor_clock_code_eq_reference_floors
    {W : ℕ} (N : ℝ) (p : PathData W) (root : Fin p.C) (mesh : ℝ) (z : Ev) :
    clockParentCode p root (SignalGraph.ancestorSignal N p root) mesh z =
      fun j => ⌊parentUnshearedCoordinates N p root (p.R root) z j / mesh⌋ := by
  have hsignal := SignalGraph.ancestorSignal_clock N p root z
  simp only [one_mul] at hsignal
  change (fun j => ⌊clockParentCoordinates p root (SignalGraph.ancestorSignal N p root) z j/mesh⌋)=_
  simp only [clockParentCoordinates,parentUnshearedCoordinates,hsignal]

/-- Restore every record ratio on a graph-clock code after ANY measurable
middle restriction. The reference reservoir stays fixed while the middle
set varies, so earlier record floors are not lost to later line cuts.
Only81*beta times the reservoir mass is charged. -/
theorem ancestor_clock_record_renewal
    {W : ℕ} {p : PathData W} {Rec : Type*}
    [Fintype Rec] [MeasurableSpace Rec] [MeasurableSingletonClass Rec]
    (N : ℝ) (root : Fin p.C)
    (piece : Rec → Set Ev) (code : Rec → Fin 4 → ℤ)
    (hm : ∀ r, MeasurableSet (piece r))
    (hdj : Pairwise (fun r s => Disjoint (piece r) (piece s)))
    (raw : Measure Ev) (reservoir : Set Ev) (hreservoir : MeasurableSet reservoir)
    (hcover : ∀ z∈reservoir, ∃ r, z∈piece r)
    {baseRef hiddenRef mesh : ℝ}
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef) (hmesh : 0 < mesh)
    (hrecords : ∀ r z, z∈piece r →
      (fun j => ⌊parentUnshearedCoordinates N p root (p.R root) z j /
        ((Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef : Fin 4 → ℝ) j)⌋)∈
      referenceCellOptions
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef)
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef) (code r))
    (hbaseBudget : 3*baseRef ≤ mesh) (hhiddenBudget : 3*hiddenRef ≤ mesh)
    (beta : ENNReal) (hbeta : beta≠0) (hbetaTop : beta≠⊤) :
    ∀ middle : Set Ev, MeasurableSet middle → middle⊆reservoir →
    ∃ current : Set Ev, MeasurableSet current ∧ current⊆middle ∧
      raw middle ≤ raw current+(81:ENNReal)*beta*raw reservoir ∧
      ∀ (B : Set Ev) (cap : ENNReal),
        (∀ r, (raw.restrict reservoir) (piece r∩B) ≤
          cap*(raw.restrict reservoir) (piece r)) →
        ∀ label,
          (raw.restrict current)
            {z | clockParentCode p root (SignalGraph.ancestorSignal N p root) mesh z=label ∧ z∈B} ≤
          (cap/beta)*(raw.restrict current)
            ((clockParentCode p root (SignalGraph.ancestorSignal N p root) mesh) ⁻¹' {label}) := by
  classical
  have hclock : (2:ℝ)^p.T (p.lev root)≠0 := by positivity
  have hthickness : δ N (p.r (p.lev root))≠0 := by unfold δ; positivity
  obtain ⟨menus,hcard,hoptions,_⟩ := ancestor_record_query_menus N root root piece code
    hbaseRef hhiddenRef hmesh hmesh hrecords
    (by simpa only [div_self hclock,mul_one] using hbaseBudget)
    (by simpa only [div_self hthickness,mul_one] using hhiddenBudget)
  let label := clockParentCode p root (SignalGraph.ancestorSignal N p root) mesh
  have hlabel : Measurable label := measurable_clockParentCode p root _ mesh
  have hmeshVector : (Fin.snoc (fun _ : Fin 3 => mesh) mesh : Fin 4 → ℝ)=(fun _ => mesh) := by
    ext j
    refine Fin.lastCases ?_ (fun _ => ?_) j <;> simp only [Fin.snoc_last,Fin.snoc_castSucc]
  have hoptions' : ∀ r z, z∈piece r → label z∈menus r := by
    intro r z hz
    have h := hoptions r z hz
    simpa only [label,ancestor_clock_code_eq_reference_floors,hmeshVector] using h
  have hcoverage : ∀ᵐ z ∂raw.restrict reservoir, ∃ r, z∈piece r := by
    filter_upwards [ae_restrict_mem hreservoir] with z hz
    exact hcover z hz
  intro middle hmiddle hmiddleSub
  obtain ⟨current,state,value,hcurrent,hsub,_hstate,_hfinite,hloss,_hfaith,_hvalue,_hbound,hratios,_⟩ :=
    exists_record_refined_natural_states (raw.restrict reservoir) piece hm hdj hcoverage
      label hlabel middle hmiddle (fun z hz => hcover z (hmiddleSub hz))
      menus 81 hcard (fun r z hz => hoptions' r z hz.2)
      beta hbeta hbetaTop (fun _ _ => (0:ℝ)) (bound := 0) (by norm_num) (by simp)
  have hcurrentSub : current⊆reservoir := hsub.trans hmiddleSub
  have hloss' : raw (middle\current) ≤ (81:ENNReal)*beta*raw reservoir := by
    simpa only [Measure.restrict_eq_self raw
      (show middle\current⊆reservoir from fun z hz => hmiddleSub hz.1),
      Measure.restrict_apply_univ,Nat.cast_ofNat] using hloss
  refine ⟨current,hcurrent,hsub,?_,?_⟩
  · calc
      raw middle = raw current+raw (middle\current) := by
        rw [←measure_inter_add_sdiff middle hcurrent,inter_eq_right.mpr hsub]
      _ ≤ raw current+(81:ENNReal)*beta*raw reservoir := add_le_add_right hloss' _
  · intro B cap hcap q
    have h := hratios B cap hcap q
    have hnum : (current∩label ⁻¹' {q})∩B={z | label z=q ∧ z∈B}∩current := by
      ext z
      simp only [mem_inter_iff,mem_preimage,mem_singleton_iff,mem_ofPred_eq]
      tauto
    rw [hnum,inter_comm current,←Measure.restrict_apply' hcurrent,
      ←Measure.restrict_apply' hcurrent,Measure.restrict_restrict_of_subset hcurrentSub] at h
    exact h

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A : ℝ} {θ : ENNReal}
    (F : PaletteFamily Q i stop a A θ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)

include hd hp

/-- Genuine retained original histories, the already selected reference
record floor, and actual translated-grid menus supply the ancestor graph
stage's breadth renewal. There is no further history-count charge. -/
theorem Native.PaletteFamily.ancestor_clock_breadth_renewal
    (hHE : ∀ w, H w⊆d.E k w)
    (hH : ∀ w, H w⊆{z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (root : Fin p.C) (hactive : F.active root)
    (n : ↥(F.retainedOriginalFinePackets root) → ℕ)
    (code : (deep : ↥(F.retainedOriginalFinePackets root)) → Fin (n deep) → (Fin 4 → ℤ))
    (piece : (Σ deep, Fin (n deep)) → Set Ev)
    (hm : ∀ r, MeasurableSet (piece r))
    (hdj : Pairwise (fun r s => Disjoint (piece r) (piece s)))
    (hsub : ∀ r, piece r⊆F.fineOriginalEvent root r.1.1 univ)
    {frontRadius fraction : ℝ} (hfr : 0 ≤ fraction)
    (hwide : ∀ r, (piece r).Nonempty → F.coding.code r.1.1∉
      Q.intrinsicNarrowStates F.code stop F.U frontRadius fraction root)
    (reservoir : Set Ev) (hreservoir : MeasurableSet reservoir)
    (hcover : ∀ z∈reservoir, ∃ r, z∈piece r)
    (cut : ℝ) (hcut : 0 < cut)
    (hfloor : ∀ r, (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece r)=0 ∨
      ENNReal.ofReal cut*((d.ν k (p.γ root)).prod volume)
        (F.fineOriginalEvent root r.1.1 univ) ≤
          (((d.ν k (p.γ root)).prod volume).restrict reservoir) (piece r))
    {baseRef hiddenRef mesh : ℝ}
    (hbaseRef : 0 < baseRef) (hhiddenRef : 0 < hiddenRef) (hmesh : 0 < mesh)
    (hrecords : ∀ r z, z∈piece r →
      (fun j => ⌊parentUnshearedCoordinates (d.N k) p root (p.R root) z j /
        ((Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef : Fin 4 → ℝ) j)⌋)∈
      referenceCellOptions
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef)
        (Fin.snoc (fun _ : Fin 3 => baseRef) hiddenRef) (code r.1 r.2))
    (hbaseBudget : 3*baseRef ≤ mesh) (hhiddenBudget : 3*hiddenRef ≤ mesh)
    (beta : ENNReal) (hbeta : beta≠0) (hbetaTop : beta≠⊤)
    (radius : ℝ) (hwidth : (6*p.κ)*radius ≤ frontRadius) :
    ∀ middle : Set Ev, MeasurableSet middle → middle⊆reservoir →
    ∃ current : Set Ev, MeasurableSet current ∧ current⊆middle ∧
      ((d.ν k (p.γ root)).prod volume) middle ≤
        ((d.ν k (p.γ root)).prod volume) current+
          (81:ENNReal)*beta*((d.ν k (p.γ root)).prod volume) reservoir ∧
      ∀ label (normal center : EuclideanSpace ℝ (Fin 2)), ‖normal‖=1 →
        (((d.ν k (p.γ root)).prod volume).restrict current)
          {z | clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh z=label ∧
            |Inner.inner ℝ normal ((6*p.κ)⁻¹ • p.normalizedVelocity root z-center)| ≤ radius} ≤
          (ENNReal.ofReal ((8*fraction)/cut)/beta)*
            (((d.ν k (p.γ root)).prod volume).restrict current)
              ((clockParentCode p root (SignalGraph.ancestorSignal (d.N k) p root) mesh) ⁻¹' {label}) := by
  classical
  let Rec := Σ deep : ↥(F.retainedOriginalFinePackets root), Fin (n deep)
  letI : MeasurableSpace Rec := ⊤
  letI : MeasurableSingletonClass Rec := ⟨fun _ => trivial⟩
  have hf (deep : ↥(F.retainedOriginalFinePackets root)) : p.lev deep.1=stop :=
    (Finset.mem_filter.mp (F.retained_original_fine_spec root deep).1).2.1
  have hw (deep : ↥(F.retainedOriginalFinePackets root)) : p.γ deep.1=p.γ root :=
    (Finset.mem_filter.mp (F.retained_original_fine_spec root deep).1).2.2.1
  intro middle hmiddle hmiddleSub
  obtain ⟨current,hcurrent,hcurrentSub,hloss,hratios⟩ :=
    ancestor_clock_record_renewal (Rec := Rec) (d.N k) root piece (fun r => code r.1 r.2)
      hm hdj ((d.ν k (p.γ root)).prod volume) reservoir hreservoir hcover
      hbaseRef hhiddenRef hmesh hrecords hbaseBudget hhiddenBudget beta hbeta hbetaTop
      middle hmiddle hmiddleSub
  refine ⟨current,hcurrent,hcurrentSub,hloss,?_⟩
  intro label normal center hnormal
  apply hratios _ (ENNReal.ofReal ((8*fraction)/cut)) ?_ label
  intro rec
  by_cases hne : (piece rec).Nonempty
  · exact F.current_record_scaled_normalized_strip_cap hd hp hHE hH root rec.1.1 hactive
      (hf rec.1) (hw rec.1) hfr (hwide rec hne)
      (F.retained_original_fine_spec root rec.1).2
      (((d.ν k (p.γ root)).prod volume).restrict reservoir) Measure.restrict_le_self
      (piece rec) (hsub rec) cut hcut (hfloor rec) radius hwidth normal center hnormal
  · have hempty : piece rec=∅ := Set.not_nonempty_iff_eq_empty.mp hne
    apply (measure_mono inter_subset_left).trans
    simp only [hempty,measure_empty,mul_zero,le_refl]

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource
