-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.OriginalVelocityNumerators, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074), obligation o287, session x1065, commit ff13f7b85f4114e7aebca67dcf65766dc59eb950.
-- Original file Submission/Obl/k4_physical_parent_potential_source/OriginalVelocityNumerators.lean; earlier per-file provenance is retained below.
-- Namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent.
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
import Submission.Lib.K4ReferenceMeshPreparation.OriginalCaps

set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette

open Set MeasureTheory
open ParentSource ParentSource.Native
open scoped ENNReal

noncomputable section

section Prepared

variable {T : Type*} {d : ProblemData} {k : ℕ} {p : PathData (d.W k)} {m : ℕ}
    {H : Fin (d.W k) → Set Ev} {u : T → ℝ} {τ : ℝ}
    {Q : PreparedAngularPath d k p m H u τ} {i stop : ℕ} {a A a₀ R : ℝ} {θ : ENNReal}
    (F : PaletteFamily Q i stop a A θ) (hd : d.Valid)
    {κ₁ δ₀ σ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ}
    (hp : p.Valid (d.N k) d.L (d.ω k) (d.ν k) (d.E k) (d.B k) d.f
      κ₁ m s δ₀ Mp Dp σ)
    (hHE : ∀ w, H w ⊆ d.E k w) (hst : i ≤ stop) (hR : 0 ≤ R)
    (horiginal : ∀ b, F.active b → F.U b ⊆
      likelihoodGood Q.law (labelledSupport Q.residual)
        (finitePacketHistory p.lev p.γ p.F) (labelledVelocityPalette a₀) i stop R)

include hd hp hHE hst hR horiginal

/-- Original physical-velocity numerators use the ACTUAL preceding
selected fine-history mass. The fixed parent palette is unchanged.
Keeping this sharper weight permits localization against the same
original prepared law, before replacing it by a full packet reference. -/
theorem fine_original_physical_palette_cap_with_current_mass
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (b f : Fin p.C) (hb : F.active b) (hf : p.lev f=stop) (hfγ : p.γ f=p.γ b)
    (he : F.coding.code f∉fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
      (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1/8 : ℝ)))
    (D : Set (ℤ×ℤ)) (hD : MeasurableSet D) :
    ((d.ν k (p.γ b)).prod volume)
      (F.fineOriginalEvent b f univ ∩ {z | velocityPalette a₀ (v z.1)∈D}) ≤
      ENNReal.ofReal (8*R) *
        ((d.ν k (p.γ b)).prod volume) (F.fineOriginalEvent b f univ) *
        ((Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)) D := by
  haveI : IsProbabilityMeasure (d.ν k (p.γ b)) := (hd.weights k).2.2 _
  let src := F.fineOriginalEvent b f univ
  let raw := (d.ν k (p.γ b)).prod (volume : Measure ℝ)
  let control : Ev → ℤ×ℤ := fun z => velocityPalette a₀ (v z.1)
  have hm : Measurable control := by
    apply measurable_euclidean_velocityPalette
    exact (show Measurable (fun z : Ev => v z.1) by unfold v; fun_prop)
  have hsource := F.fine_original_event_measurable hp b f hb univ MeasurableSet.univ
  have htop : raw src≠∞ := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (by rw [hfγ]; exact measure_ne_top _ _))
    (F.fine_original_source_mass_le_full hd hp b f hf hfγ)
  have hmap : ((F.fineLaw b (F.coding.code f)).map (labelledVelocityPalette a₀))=
      ((F.fineLaw b (F.coding.code f)).map Prod.snd).map control :=
    (Measure.map_map hm measurable_snd).symm
  have hexact : ((F.fineLaw b (F.coding.code f)).map (labelledVelocityPalette a₀)) D * raw src=
      raw (src∩control ⁻¹' D) := by
    rw [hmap,F.fine_original_posterior hd hp hHE hH b hb f hf hfγ,Measure.map_apply hm hD]
    exact ProbabilityTheory.cond_mul_eq_inter' hsource htop (control ⁻¹' D)
  have hdom := original_fine_palette_domination F hd hp hHE hst hR horiginal b hb
    (F.coding.code f) he D
  rw [Measure.smul_apply,smul_eq_mul] at hdom
  calc
    _ = raw (src∩control ⁻¹' D) := rfl
    _ = ((F.fineLaw b (F.coding.code f)).map (labelledVelocityPalette a₀)) D * raw src :=
      hexact.symm
    _ ≤ (ENNReal.ofReal (8*R)*
        ((Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)) D)*raw src :=
      mul_le_mul' hdom le_rfl
    _ = _ := by ring

/-- Resolved true fine histories transfer their actual original palette
numerators to arbitrary geometric cells. Pure caps are needed only on
the original prepared coarse event. The same fixed parent palette
survives, with no history count or inverse selected-mass factor.

The geometry is explicit: each fine history has a finite state menu and
lies in the padded pure cells of every state in that menu. Thus this
also applies to a separately normalized physical residual, once its
actual history resolution has been established. -/
theorem original_cell_palette_cap_of_resolved_fine_histories
    (hH : ∀ w, H w ⊆ {z | ∃ b, p.lev b=m-1 ∧ p.γ b=w ∧ z∈p.F b})
    (b : Fin p.C) (hb : F.active b)
    {Index Code PureCode : Type*} [Fintype Index]
    (fine : Index → Fin p.C) (hinj : Function.Injective fine)
    (hf : ∀ v, p.lev (fine v)=stop) (hfγ : ∀ v, p.γ (fine v)=p.γ b)
    (hretained : ∀ v, F.coding.code (fine v)∉
      fineRetentionFailures (Q.coarseLaw (p.lev b) (F.code b))
        (finitePacketHistory p.lev p.γ p.F stop) (F.U b) (ENNReal.ofReal (1/8 : ℝ)))
    (μ : Measure Ev) (hμ : μ ≤ (d.ν k (p.γ b)).prod volume)
    (state : Ev → Code) (options : Index → Finset Code)
    (cell : Ev → PureCode) (paddingCells : Code → Finset PureCode)
    (M : ℕ) (hcard : ∀ q, (paddingCells q).card ≤ M)
    (hcover : ∀ᵐ z ∂μ, ∃ v, z∈F.fineOriginalEvent b (fine v) univ)
    (hoptions : ∀ v, ∀ᵐ z ∂μ,
      z∈F.fineOriginalEvent b (fine v) univ → state z∈options v)
    (hlocal : ∀ v q, q∈options v → ∀ z∈F.fineOriginalEvent b (fine v) univ,
      cell z∈paddingCells q)
    (Bpure : ENNReal)
    (hpure : ∀ c, ((d.ν k (p.γ b)).prod volume)
      ({z | (p.γ b,z)∈F.U b} ∩ {z | cell z=c}) ≤ Bpure) :
    ∀ q (D : Set (ℤ×ℤ)), MeasurableSet D →
      μ {z | state z=q ∧ velocityPalette a₀ (v z.1)∈D} ≤
        ENNReal.ofReal (8*R)*(M:ENNReal)*Bpure*
          ((Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)) D := by
  classical
  let raw := (d.ν k (p.γ b)).prod (volume : Measure ℝ)
  let U : Set Ev := {z | (p.γ b,z)∈F.U b}
  let νref : Measure Ev := raw.restrict U
  let Hist : Index → Set Ev := fun v => F.fineOriginalEvent b (fine v) univ
  let weights : Index → ENNReal := fun v => raw (Hist v)
  let π := (Q.coarseLaw (p.lev b) (F.code b)).map (labelledVelocityPalette a₀)
  let control : Ev → ℤ×ℤ := fun z => velocityPalette a₀ (v z.1)
  have hHist : ∀ v, MeasurableSet (Hist v) :=
    fun v => F.fine_original_event_measurable hp b (fine v) hb univ MeasurableSet.univ
  have hHistSub : ∀ v, Hist v ⊆ U := fun _ z hz => hz.2.1
  have hw : ∀ v, weights v ≤ νref (Hist v) := by
    intro v
    dsimp only [weights,νref]
    rw [Measure.restrict_apply (hHist v),inter_eq_left.mpr (hHistSub v)]
  have hpacket (v : Index) {z : Ev} (hz : z∈Hist v) :
      z∈p.F (fine v) ∧ packetUnique p.lev p.γ p.F (p.γ b) z := by
    have hh : (z∈p.F (fine v) ∧ packetUnique p.lev p.γ p.F (p.γ b) z) ∧
        z∈p.terminalCoverage m (p.γ b) := by
      simpa only [PathData.packetWitness,ite_eq_left (And.intro (hf v) (hfγ v)),
        mem_inter_iff,mem_ofPred_eq] using hz.1
    exact hh.1
  have hdisj : Pairwise (fun v w => AEDisjoint νref (Hist v) (Hist w)) := by
    intro v w hvw
    apply Disjoint.aedisjoint
    apply Set.disjoint_left.mpr
    intro z hzv hzw
    have hv := hpacket v hzv
    have hw := hpacket w hzw
    exact hvw (hinj (hv.2 (fine v) (fine w) ((hf v).trans (hf w).symm)
      (hfγ v) (hfγ w) hv.1 hw.1))
  have hnum (v : Index) (D : Set (ℤ×ℤ)) (hD : MeasurableSet D) :
      μ {z | z∈Hist v ∧ control z∈D} ≤ ENNReal.ofReal (8*R)*weights v*π D := by
    have hh := fine_original_physical_palette_cap_with_current_mass F hd hp hHE hst hR
      horiginal hH b (fine v) hb (hf v) (hfγ v) (hretained v) D hD
    exact (hμ _).trans hh
  have hlocal' : ∀ v q, q∈options v → Hist v ≤ᵐ[νref] {z | cell z∈paddingCells q} :=
    fun v q hq => Filter.Eventually.of_forall (fun z hz => hlocal v q hq z hz)
  have hpure' (c : PureCode) : νref {z | cell z=c} ≤ Bpure := by
    have hU : MeasurableSet U := (F.measurable_U b hb).preimage
      (show Measurable (fun z : Ev => (p.γ b,z)) by fun_prop)
    dsimp only [νref]
    rw [Measure.restrict_apply' hU]
    simpa only [U,inter_comm] using hpure c
  exact Submission.Lib.K4ReferenceMeshPreparation.localized_reference_mesh_palette_cap
    νref μ π control state Hist hHist hdisj options weights hw cell paddingCells M hcard
    hlocal' Bpure hpure' (ENNReal.ofReal (8*R)) hcover hoptions hnum

end Prepared

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.OriginalVelocityPalette
