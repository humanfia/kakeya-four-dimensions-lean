-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.NativePreStateMetadata, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.NativeRootMetadata
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootAssembly
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.RootPureCaps
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.PhysicalModel.NativePreStateFromScales

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Set MeasureTheory
open Parent.ParentSource
open Parent.ParentSource.Native (ProblemData PathData PreparedAngularPath PaletteFamily BroadResidual
  labelledVelocityPalette)
open Parent.Qualification
open Parent.Qualification.PhysicalModel
open Parent.Qualification.PhysicalModel.NativeAncestor
open Submission.Lib.K4ParentSignalPreparation.Census
open scoped ENNReal BigOperators

noncomputable section

/-- The actual original P1 cut of a root package, before child states.
One common reference is fixed per ancestor, and full-prior floors plus
actual derivative tables are constructed from its retained records.
The resulting global source has the original full-reference charge. -/
theorem prepare_native_pre_state_metadata
    {T : Type*} {d : ProblemData} (hd : d.Valid) {k m : ℕ} {p : PathData (d.W k)}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ}
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w⊆d.E k w)
    {i stop : ℕ} {meshF envF : ℝ} {θF : ENNReal} {F : PaletteFamily Q i stop meshF envF θF}
    {rF frF : ℝ} {Rp : BroadResidual F rF frF} {c : ℕ} {K θ ε aA q d₁ h' a' : ℝ}
    {Krecord baseRef hiddenRef finePv paletteRatio cut frontRadius fraction χ finest dimension
      Kcap : ℝ}
    {original : Fin (d.W k) → Set Event} {n : ℕ} {depth : Fin n → ℕ} {Kcore : ℝ} {e R : ℕ}
    {core : BroadMultiscaleCoreSource d k p original n depth Kcore e R}
    (RP : RootPackage Q F Rp c K θ ε aA q d₁ h' a' Krecord baseRef hiddenRef finePv paletteRatio
      cut frontRadius fraction χ finest dimension Kcap core)
    (a : OriginalRootScales) (ps : OriginalPreStateScales a)
    (hdimension : a.dimension=dimension)
    {Vmax : ℝ} (hVmax : 0 ≤ Vmax)
    (hvelocity : ∀ w, ∀ z∈Rp.residual w, ‖Parent.v z.1‖ ≤ Vmax)
    (hcoeff : coefficientBound (p:=p) Vmax ≤ a.H)
    (haux : 1 < d.N k^χ) (histop : i ≤ stop) (hri : 0 ≤ p.r i)
    (hdepth : p.r i+χ*finest ≤ d.L)
    (hbaseRef : 3*baseRef ≤ (d.N k^χ)^(-finest))
    (hhiddenRef : 3*hiddenRef ≤ (d.N k^χ)^(-finest))
    (hRatio : 0 ≤ paletteRatio) (hcut : 0 < cut) (hKcap : 0 ≤ Kcap)
    (hfinePv : 0 < finePv) (hfineWidth : finePv ≤ Jets2.dyadicParameterWidth a.paletteFinest)
    (hbaseLo : (d.N k^χ)^(-finest) ≤ a.resolution)
    (hbaseHi : Jets2.dyadicParameterWidth a.floorStart ≤ (d.N k^χ)^(-finest⁻¹))
    (hCpure : 4*625*((8*paletteRatio)/cut)*Kcap ≤ a.Cpure)
    (hcensus : ∀ root, F.active root → ∀ b w : ℝ,
      a.resolution ≤ b → b ≤ 1 → a.resolution ≤ w → w ≤ 1 → a.Kcensus^(100:ℕ)*b ≤ w →
      (occupied (RP.E1 (p.γ root)∩p.F root) (fun z j => unshearedPacketBase p root z j)
        (physicalParentSignal (d.N k) p root (p.R root)) b w).Finite ∧
      ((occupied (RP.E1 (p.γ root)∩p.F root) (fun z j => unshearedPacketBase p root z j)
        (physicalParentSignal (d.N k) p root (p.R root)) b w).ncard:ℝ) ≤
          a.Kcensus/(b^3*w^a.dimension)) :
    ∃ (E1' : Fin (d.W k) → Set Ev) (hmeas : ∀ w, MeasurableSet (E1' w))
      (hsub : ∀ w, E1' w⊆RP.E1 w),
      (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (RP.E1 w)) ≤
        (∑ w, ENNReal.ofReal (d.ω k w)*((d.ν k w).prod volume) (E1' w))+ps.charge ∧
      Nonempty (NativeRootMetadata hp {root | F.active root} E1' Vmax finePv a
        (fun root => (Q.coarseLaw (p.lev root) (F.code root)).map (labelledVelocityPalette finePv))) := by
  classical
  have hqroot (root : Fin p.C) : (hp.frozenPacket root).unitFrame.q=(((2:ℝ)^p.T (p.lev root))⁻¹) := rfl
  have hreference (root : Fin p.C) (ha : F.active root) :=
    exists_original_common_dyadic_reference (F:=F) hd hp hHE root ha finePv a.paletteFinest
  let palette (root : Fin p.C) : Measure (Fin 2 → ℝ) :=
    if ha : F.active root then (hreference root ha).choose else Measure.dirac 0
  have href (root : Fin p.C) (ha : F.active root) :
      Jets2.CommonDyadicVelocityReference finePv a.paletteFinest
        (fun b => Parent.OriginalVelocityPalette.originalVectorPalette F root finePv {b}) (palette root) := by
    simpa only [palette,dite_eq_left ha] using (hreference root ha).choose_spec
  have hFmeas (root : Fin p.C) : MeasurableSet (p.F root) := by
    simpa only [hp.frozenPacket_counted] using (hp.frozenPacket root).measurable_counted
  have hcutRoot (root : Fin p.C) (ha : F.active root) :
      ∃ G : Set Ev, MeasurableSet G ∧ G⊆RP.E1 (p.γ root)∩p.F root ∧
        ((d.ν k (p.γ root)).prod volume) ((RP.E1 (p.γ root)∩p.F root)\G) ≤
          ps.charge*(ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*
            d.ν k (p.γ root) (p.A root)) ∧
        Nonempty (Jets2.OriginalPreStateData ((hp.frozenPacket root).prior (d.ν k (p.γ root)))
          (coefficientTable (d.N k) p root Vmax) ((hp.frozenPacket root).selectedEvent G)
          (palette root) a.dimension a.floorExponent a.floorStart a.floorCount
          (fun j : Fin a.regLength => a.regLevel j.val) a.KL) := by
    have hlev : p.lev root=i := F.level root ha
    let S := RP.E1 (p.γ root)∩p.F root
    have hS : MeasurableSet S := (RP.E1_meas _).inter (hFmeas root)
    apply prepare_native_pre_state_from_scales hd hp root hVmax S hS inter_subset_right
      (path_R_degree hp root) (fun z hz => hvelocity _ z (RP.E1_res _ hz.1))
      S hS Subset.rfl a ps hcoeff (palette root) (href root ha).probability (hcensus root ha)
    intro query hquery base w hbase hbase' hw hw1 b j D hD
    have hh := original_root_pure_caps_of_records (RP.data root ha) haux
      (by rw [hlev]; exact histop) (by rw [hlev]; exact hri) (by rw [hlev]; exact hdepth)
      hbaseRef hhiddenRef hRatio hcut hKcap (hFmeas root)
      S (RP.kept root ha) inter_subset_right (href root ha) hfinePv hfineWidth
      (hbaseLo.trans hbase) (hbase'.trans hbaseHi) hCpure query hquery w hw hw1 b j D hD
    simpa only [hdimension,hqroot] using hh
  let G (root : Fin p.C) : Set Ev := if ha : F.active root then (hcutRoot root ha).choose else ∅
  have hG (root : Fin p.C) (ha : F.active root) := by
    have hh := (hcutRoot root ha).choose_spec
    change MeasurableSet (G root) ∧ G root⊆RP.E1 (p.γ root)∩p.F root ∧
      ((d.ν k (p.γ root)).prod volume) ((RP.E1 (p.γ root)∩p.F root)\G root) ≤
        ps.charge*(ENNReal.ofReal ((hp.frozenPacket root).unitFrame.q)*
          d.ν k (p.γ root) (p.A root)) ∧
      Nonempty (Jets2.OriginalPreStateData ((hp.frozenPacket root).prior (d.ν k (p.γ root)))
        (coefficientTable (d.N k) p root Vmax) ((hp.frozenPacket root).selectedEvent (G root))
        (palette root) a.dimension a.floorExponent a.floorStart a.floorCount
        (fun j : Fin a.regLength => a.regLevel j.val) a.KL)
    simpa only [G,dite_eq_left ha] using hh
  have hmass (root : Fin p.C) (ha : F.active root) :
      ((d.ν k (p.γ root)).prod volume) (RP.E1 (p.γ root)∩p.F root) ≤
        ((d.ν k (p.γ root)).prod volume) (G root)+
          ps.charge*(d.ν k (p.γ root) (p.A root)*ENNReal.ofReal (((2:ℝ)^p.T (p.lev root))⁻¹)) := by
    have hh := (hG root ha).2.2.1
    have hcover : RP.E1 (p.γ root)∩p.F root⊆G root∪((RP.E1 (p.γ root)∩p.F root)\G root) := by
      intro z hz
      by_cases hg : z∈G root
      · exact Or.inl hg
      · exact Or.inr ⟨hz,hg⟩
    have hu : ((d.ν k (p.γ root)).prod volume) (RP.E1 (p.γ root)∩p.F root) ≤
        ((d.ν k (p.γ root)).prod volume) (G root)+
          ((d.ν k (p.γ root)).prod volume) ((RP.E1 (p.γ root)∩p.F root)\G root) :=
      (measure_mono hcover).trans (measure_union_le (G root) _)
    have hv := hu.trans (add_le_add le_rfl hh)
    simpa only [hqroot,mul_comm] using hv
  obtain ⟨E1',hmeas,hsub,hslice,hmass'⟩ := RP.cut_per_root hd hp G
    (fun root ha => (hG root ha).1) (fun root ha => (hG root ha).2.1) ps.charge hmass
  refine ⟨E1',hmeas,hsub,hmass',⟨⟨palette,?_,?_⟩⟩⟩
  · intro root ha
    simpa only [Parent.OriginalVelocityPalette.originalVectorPalette] using href root ha
  · intro root ha
    change Jets2.OriginalPreStateData _ _ ((hp.frozenPacket root).selectedEvent
      ((RP.restrict E1' hmeas hsub).E1 (p.γ root)∩p.F root)) _ _ _ _ _ _ _
    rw [hslice root ha]
    exact Classical.choice (hG root ha).2.2.2

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
